--[[
==================================================================================================
  Pet Simulator 99 — Deep Backrooms Boss Room Farmer  (v6 — Boss Killer)
  =================================================================================================
  WHAT'S NEW (v6):
    * Removed the big "2 chest server found" banner entirely.
    * The script now FARMS boss rooms: finds GameMastersStage rooms, goes to the closest
      one, breaks the mini-chests first, then damages the boss, then moves to the next
      alive boss room. Cycles forever (bosses respawn).
    * Boss fighting: always TPs to the current target, forces pets to attack it, and
      clicks aggressively (Breakables_PlayerDealDamage spam).
    * Only breaks mini-chests that are INSIDE the current boss room (proximity check),
      never random ones elsewhere in the backrooms.
    * Fixed auto-enter Deep Backrooms with retry logic (game has a join cooldown).
    * Anti-AFK: periodically resets the idle timer + jumps occasionally so the game's
      built-in "Move Server" (public rejoin) never triggers.
    * Flying + anti-void still active.
    * TP panel kept (1-click TP to any found boss room).

  KEY GAME APIs USED (discovered from extracted scripts):
    * Network.UnreliableFire("Breakables_PlayerDealDamage", uid)  -- damage a breakable
    * Network.Fire("BR_SetTarget", {[euid]={t=typeId, v=targetVal}})  -- send pets to attack
    * BreakableFrontend.AllByInstanceAndClass("Chest"|"Normal")  -- get breakables in instance
    * PlayerPet.GetByPlayer(LocalPlayer)  -- get the player's pets
    * Network.Fire("Idle Tracking: Stop Timer")  -- anti-AFK
    * InstancingCmds.Enter("Backrooms") / .InvokeCustom("Debug_EnterDeepMaze")
    * Signal.Invoke("Backrooms_IsInDeep")
    * InstancingCmds.Get():InvokeCustom("Backrooms_GetMapDescriptor", true)
==================================================================================================
]]

--================================================================================================
-- Services
--================================================================================================
local Players            = game:GetService("Players")
local ReplicatedStorage  = game:GetService("ReplicatedStorage")
local CollectionService  = game:GetService("CollectionService")
local RunService         = game:GetService("RunService")
local TweenService       = game:GetService("TweenService")
local Workspace          = game:GetService("Workspace")
local UserInputService   = game:GetService("UserInputService")
local VirtualInputManager = game:GetService("VirtualInputManager") -- may be nil on live

local LocalPlayer = Players.LocalPlayer

-- file-scope refs populated by main()
local _Signal = nil
local _InstancingCmds = nil
local _Network = nil
local _BreakableFrontend = nil
local _PlayerPet = nil
local _PetCmds = nil
local _BreakableCmds = nil

-- forward declarations
local refreshTeleportPanel

--================================================================================================
-- Config
--================================================================================================
local CONFIG = {
    TARGET_ROOM_NAME   = "GameMastersStage",   -- boss chest room class name
    REQUIRED_COUNT     = 2,                    -- we want 2 of these in 1 server (for TP panel)
    RESCAN_INTERVAL    = 1.0,                  -- seconds between descriptor rescans
    FLY_HEIGHT_OFFSET  = 6,                    -- studs above room pivot when TPing
    VOID_Y_THRESHOLD   = -50,                  -- below this Y -> emergency TP back
    TP_STREAM_LEAD     = 0.04,                 -- streaming wait (explore loop)
    TP_BUTTON_STREAM   = 1.0,                  -- streaming wait (TP button)
    TP_BUTTON_VERIFY   = 2.0,                  -- seconds after TP before floor-check
    FLOOR_RAYCAST_DIST = 50,                   -- raycast downward to verify floor
    DEEP_ONLY          = true,                 -- only operate in DEEP backrooms
    CLASS_REFRESH      = 8.0,                  -- seconds between class list refreshes

    -- Boss farming
    BOSS_ROOM_RADIUS   = 80,                   -- studs: breakables within this radius of boss room center
    CLICK_INTERVAL     = 0.03,                 -- seconds between damage clicks (very aggressive)
    PET_TARGET_INTERVAL= 0.15,                 -- seconds between re-targeting pets (very fast)
    BOSS_CHECK_INTERVAL= 1.0,                  -- seconds between boss-alive checks
    NO_BOSS_WAIT       = 5.0,                  -- seconds to wait when no alive boss found
    TP_TO_BOSS_INTERVAL= 3.0,                  -- seconds between re-TPing to current boss (keep close)
    MINI_CHEST_CLASS   = "Chest",              -- breakable class for mini chests
    BOSS_CHEST_CLASS   = "Chest",              -- boss is also a "Chest" class breakable (largest health)

    -- Anti-AFK
    ANTI_AFK_INTERVAL  = 20,                   -- seconds between anti-AFK resets
    ANTI_AFK_JUMP_INTERVAL = 45,               -- seconds between jumps
    IDLE_TIMER_RESET_VAL = 0,                  -- value to send for idle timer reset

    -- Deep entry retry
    DEEP_ENTER_RETRY_INTERVAL = 3.0,           -- seconds between deep-entry retries
    DEEP_ENTER_MAX_RETRIES    = 40,            -- max retries (40 * 3s = 2 min)
    BACKROOMS_ENTER_RETRY_INTERVAL = 5.0,      -- seconds between backrooms-enter retries
    BACKROOMS_ENTER_MAX_RETRIES    = 24,       -- max retries (24 * 5s = 2 min)

    -- Room preloading (CRITICAL: breakables only load when you visit the room)
    PRELOAD_DELAY          = 3.0,              -- seconds to wait at each room during preload
    ROOM_REFRESH_INTERVAL  = 30.0,             -- seconds between full room re-visits (refresh breakable data)
}

--================================================================================================
-- State
--================================================================================================
local STATE = {
    stage           = "init",
    foundRooms      = {},       -- array of room entries (descriptor or workspace)
    foundUIDs       = {},       -- set of room UIDs -> true
    visited         = {},       -- set of breakable UIDs we've killed
    confirmedDeep   = false,
    stopScript      = false,
    startTime       = tick(),
    lastSafePos     = nil,
    currentTarget   = "(starting)",
    connections     = {},
    hud             = nil,
    tpPanel         = nil,

    -- Boss farming state
    currentBossRoom = nil,      -- the room entry we're currently farming
    currentBossUid  = nil,      -- UID of the boss breakable we're attacking
    lastClickTime   = 0,
    lastPetTargetTime = 0,
    lastBossCheck   = 0,
    lastTpToBoss    = 0,
    lastAntiAfk     = 0,
    lastJump        = 0,
    bossesKilled    = 0,
    miniChestsKilled= 0,
    lastCandidateLog= 0,      -- throttle for candidate debug logging
    lastBossFindLog  = 0,     -- throttle for findBossInRoom debug logging
    lastMiniChestLog = 0,     -- throttle for mini chest count logging
}

--================================================================================================
-- Small utilities
--================================================================================================
local function log(msg)
    print(("[PS99-Farmer] %s"):format(tostring(msg)))
end

local function warnLog(msg)
    warn(("[PS99-Farmer] %s"):format(tostring(msg)))
end

local function safeRequire(path)
    local ok, mod = pcall(function() return require(path) end)
    if ok and mod then return mod end
    return nil
end

local function waitForChild(parent, name, timeout)
    timeout = timeout or 30
    local child = parent:FindFirstChild(name)
    if child then return child end
    local t0 = tick()
    while tick() - t0 < timeout do
        child = parent:FindFirstChild(name)
        if child then return child end
        task.wait(0.25)
    end
    return parent:FindFirstChild(name)
end

local function getChar()
    local char = LocalPlayer.Character
    if not char then return nil, nil, nil end
    return char, char:FindFirstChild("HumanoidRootPart"), char:FindFirstChildOfClass("Humanoid")
end

local function requireClient(name)
    local lib = ReplicatedStorage:FindFirstChild("Library")
    if not lib then return nil end
    local client = lib:FindFirstChild("Client")
    if not client then return nil end
    local mod = client:FindFirstChild(name)
    if not mod then return nil end
    return safeRequire(mod)
end

local function requireLib(name)
    local lib = ReplicatedStorage:FindFirstChild("Library")
    if not lib then return nil end
    local mod = lib:FindFirstChild(name)
    if not mod then return nil end
    return safeRequire(mod)
end

local function shortUID(uid)
    uid = tostring(uid or "")
    return uid:sub(math.max(1, #uid - 3))
end

--================================================================================================
-- UI: Draggable helper — makes any Frame draggable by clicking and dragging
--================================================================================================
local function makeDraggable(frame)
    if not frame then return end
    local dragging = false
    local dragStart = nil
    local startPos = nil

    -- use InputBegan on the frame itself (works for mouse + touch)
    frame.InputBegan:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1
           or input.UserInputType == Enum.UserInputType.Touch then
            dragging = true
            dragStart = input.Position
            startPos = frame.Position
        end
    end)

    frame.InputChanged:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseMovement
           or input.UserInputType == Enum.UserInputType.Touch then
            if dragging and dragStart and startPos then
                local delta = input.Position - dragStart
                frame.Position = UDim2.new(
                    startPos.X.Scale, startPos.X.Offset + delta.X,
                    startPos.Y.Scale, startPos.Y.Offset + delta.Y
                )
            end
        end
    end)

    frame.InputEnded:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1
           or input.UserInputType == Enum.UserInputType.Touch then
            dragging = false
        end
    end)

    -- also handle global input ended (in case mouse is released outside the frame)
    UserInputService.InputEnded:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1
           or input.UserInputType == Enum.UserInputType.Touch then
            dragging = false
        end
    end)
end

--================================================================================================
-- UI: Status HUD (top-left)
--================================================================================================
local function buildStatusHUD(playerGui)
    local existing = playerGui:FindFirstChild("PS99_Farmer_HUD")
    if existing then existing:Destroy() end

    local gui = Instance.new("ScreenGui")
    gui.Name = "PS99_Farmer_HUD"
    gui.ResetOnSpawn = false
    gui.IgnoreGuiInset = true
    gui.DisplayOrder = 9990
    gui.Parent = playerGui

    local frame = Instance.new("Frame")
    frame.Name = "Panel"
    frame.Size = UDim2.fromOffset(380, 260)
    frame.Position = UDim2.fromOffset(12, 12)
    frame.BackgroundColor3 = Color3.fromRGB(14, 14, 22)
    frame.BackgroundTransparency = 0.08
    frame.BorderSizePixel = 0
    frame.Parent = gui
    Instance.new("UICorner", frame).CornerRadius = UDim.new(0, 8)

    local stroke = Instance.new("UIStroke", frame)
    stroke.Color = Color3.fromRGB(80, 60, 130)
    stroke.Thickness = 1.5
    stroke.Transparency = 0.4

    local title = Instance.new("TextLabel")
    title.Size = UDim2.new(1, -16, 0, 24)
    title.Position = UDim2.fromOffset(8, 6)
    title.BackgroundTransparency = 1
    title.Font = Enum.Font.GothamBold
    title.TextSize = 13
    title.TextColor3 = Color3.fromRGB(215, 200, 255)
    title.TextXAlignment = Enum.TextXAlignment.Left
    title.Text = "Deep Backrooms Boss Farmer"
    title.Parent = frame

    local stageLabel = Instance.new("TextLabel")
    stageLabel.Name = "Stage"
    stageLabel.Size = UDim2.new(1, -16, 0, 18)
    stageLabel.Position = UDim2.fromOffset(8, 30)
    stageLabel.BackgroundTransparency = 1
    stageLabel.Font = Enum.Font.Gotham
    stageLabel.TextSize = 12
    stageLabel.TextColor3 = Color3.fromRGB(200, 200, 220)
    stageLabel.TextXAlignment = Enum.TextXAlignment.Left
    stageLabel.Text = "Stage: initializing..."
    stageLabel.Parent = frame

    -- Deep status
    local deepLabel = Instance.new("TextLabel")
    deepLabel.Name = "DeepStatus"
    deepLabel.Size = UDim2.new(0, 200, 0, 18)
    deepLabel.Position = UDim2.fromOffset(8, 50)
    deepLabel.BackgroundTransparency = 1
    deepLabel.Font = Enum.Font.GothamBold
    deepLabel.TextSize = 12
    deepLabel.TextColor3 = Color3.fromRGB(220, 80, 80)
    deepLabel.TextXAlignment = Enum.TextXAlignment.Left
    deepLabel.Text = "Deep: NO (waiting...)"
    deepLabel.Parent = frame

    -- Stats rows
    local function makeStatRow(y, label)
        local lbl = Instance.new("TextLabel")
        lbl.Size = UDim2.new(0, 160, 0, 16)
        lbl.Position = UDim2.fromOffset(8, y)
        lbl.BackgroundTransparency = 1
        lbl.Font = Enum.Font.Gotham
        lbl.TextSize = 11
        lbl.TextColor3 = Color3.fromRGB(170, 180, 210)
        lbl.TextXAlignment = Enum.TextXAlignment.Left
        lbl.Text = label
        lbl.Parent = frame

        local val = Instance.new("TextLabel")
        val.Size = UDim2.new(0, 200, 0, 16)
        val.Position = UDim2.fromOffset(180, y)
        val.BackgroundTransparency = 1
        val.Font = Enum.Font.GothamBold
        val.TextSize = 11
        val.TextColor3 = Color3.fromRGB(230, 230, 250)
        val.TextXAlignment = Enum.TextXAlignment.Left
        val.Text = "0"
        val.Parent = frame
        return val
    end

    local roomsVal     = makeStatRow(72,  "Boss rooms found:")
    local bossesVal    = makeStatRow(90,  "Bosses killed:")
    local miniVal      = makeStatRow(108, "Mini chests killed:")
    local currentVal   = makeStatRow(126, "Current target:")
    local bossHpVal    = makeStatRow(144, "Boss HP:")

    local timerLabel = Instance.new("TextLabel")
    timerLabel.Name = "Timer"
    timerLabel.Size = UDim2.new(1, -16, 0, 16)
    timerLabel.Position = UDim2.fromOffset(8, 164)
    timerLabel.BackgroundTransparency = 1
    timerLabel.Font = Enum.Font.Gotham
    timerLabel.TextSize = 11
    timerLabel.TextColor3 = Color3.fromRGB(150, 150, 170)
    timerLabel.TextXAlignment = Enum.TextXAlignment.Left
    timerLabel.Text = "elapsed: 0s"
    timerLabel.Parent = frame

    -- Anti-AFK status
    local afkLabel = Instance.new("TextLabel")
    afkLabel.Name = "AfkStatus"
    afkLabel.Size = UDim2.new(1, -16, 0, 16)
    afkLabel.Position = UDim2.fromOffset(8, 182)
    afkLabel.BackgroundTransparency = 1
    afkLabel.Font = Enum.Font.Gotham
    afkLabel.TextSize = 11
    afkLabel.TextColor3 = Color3.fromRGB(120, 220, 140)
    afkLabel.TextXAlignment = Enum.TextXAlignment.Left
    afkLabel.Text = "Anti-AFK: active"
    afkLabel.Parent = frame

    -- make the HUD draggable
    makeDraggable(frame)

    return {
        gui = gui, frame = frame, stage = stageLabel, deep = deepLabel,
        rooms = roomsVal, bosses = bossesVal, mini = miniVal,
        current = currentVal, bossHp = bossHpVal, timer = timerLabel, afk = afkLabel,
    }
end

local function setStage(text)
    STATE.stage = text
    if STATE.hud and STATE.hud.stage then
        STATE.hud.stage.Text = "Stage: " .. tostring(text)
    end
    log("stage -> " .. tostring(text))
end

local function updateStats()
    if not STATE.hud then return end
    local h = STATE.hud

    if h.deep then
        if STATE.confirmedDeep then
            h.deep.Text = "Deep: YES"
            h.deep.TextColor3 = Color3.fromRGB(80, 220, 100)
        else
            h.deep.Text = "Deep: NO (retrying...)"
            h.deep.TextColor3 = Color3.fromRGB(220, 80, 80)
        end
    end

    h.rooms.Text = tostring(#STATE.foundRooms)
    h.bosses.Text = tostring(STATE.bossesKilled)
    h.mini.Text = tostring(STATE.miniChestsKilled)
    h.current.Text = tostring(STATE.currentTarget):sub(1, 30)

    -- Boss HP
    if STATE.currentBossUid and _BreakableFrontend then
        local b = _BreakableFrontend.Get(STATE.currentBossUid)
        if b and b.health then
            h.bossHp.Text = ("%d / %d"):format(math.floor(b.health), math.floor(b.maxHealth or 0))
        else
            h.bossHp.Text = "(dead/despawned)"
        end
    else
        h.bossHp.Text = "-"
    end

    local elapsed = math.floor(tick() - STATE.startTime)
    local mm = math.floor(elapsed / 60)
    local ss = elapsed % 60
    h.timer.Text = ("elapsed: %dm %02ds"):format(mm, ss)
end

--================================================================================================
-- UI: Teleport panel (top-right) — 1-click TP to found boss rooms
--================================================================================================
local function buildTeleportPanel(playerGui)
    local existing = playerGui:FindFirstChild("PS99_Farmer_TPPANEL")
    if existing then existing:Destroy() end

    local gui = Instance.new("ScreenGui")
    gui.Name = "PS99_Farmer_TPPANEL"
    gui.ResetOnSpawn = false
    gui.IgnoreGuiInset = true
    gui.DisplayOrder = 9995
    gui.Parent = playerGui

    local frame = Instance.new("Frame")
    frame.Name = "Panel"
    frame.Size = UDim2.fromOffset(300, 240)
    frame.Position = UDim2.new(1, -312, 0, 12)
    frame.BackgroundColor3 = Color3.fromRGB(14, 14, 22)
    frame.BackgroundTransparency = 0.08
    frame.BorderSizePixel = 0
    frame.Parent = gui
    Instance.new("UICorner", frame).CornerRadius = UDim.new(0, 8)

    local stroke = Instance.new("UIStroke", frame)
    stroke.Color = Color3.fromRGB(180, 130, 50)
    stroke.Thickness = 1.5
    stroke.Transparency = 0.3

    local title = Instance.new("TextLabel")
    title.Size = UDim2.new(1, -16, 0, 22)
    title.Position = UDim2.fromOffset(8, 6)
    title.BackgroundTransparency = 1
    title.Font = Enum.Font.GothamBold
    title.TextSize = 13
    title.TextColor3 = Color3.fromRGB(255, 220, 120)
    title.TextXAlignment = Enum.TextXAlignment.Left
    title.Text = "TP Panel — Boss Rooms"
    title.Parent = frame

    local subtitle = Instance.new("TextLabel")
    subtitle.Name = "Subtitle"
    subtitle.Size = UDim2.new(1, -16, 0, 16)
    subtitle.Position = UDim2.fromOffset(8, 26)
    subtitle.BackgroundTransparency = 1
    subtitle.Font = Enum.Font.Gotham
    subtitle.TextSize = 11
    subtitle.TextColor3 = Color3.fromRGB(180, 180, 200)
    subtitle.TextXAlignment = Enum.TextXAlignment.Left
    subtitle.Text = "No rooms found yet..."
    subtitle.Parent = frame

    local scroll = Instance.new("ScrollingFrame")
    scroll.Name = "List"
    scroll.Size = UDim2.new(1, -8, 1, -50)
    scroll.Position = UDim2.fromOffset(4, 46)
    scroll.BackgroundTransparency = 1
    scroll.BorderSizePixel = 0
    scroll.ScrollBarThickness = 4
    scroll.ScrollBarImageColor3 = Color3.fromRGB(150, 120, 60)
    scroll.CanvasSize = UDim2.fromScale(0, 0)
    scroll.AutomaticCanvasSize = Enum.AutomaticSize.Y
    scroll.Parent = frame

    local layout = Instance.new("UIListLayout", scroll)
    layout.SortOrder = Enum.SortOrder.LayoutOrder
    layout.Padding = UDim.new(0, 3)

    -- make the TP panel draggable
    makeDraggable(frame)

    return { gui = gui, frame = frame, subtitle = subtitle, scroll = scroll, layout = layout, buttons = {} }
end

local function hasFloorBelow(pos)
    local params = RaycastParams.new()
    params.FilterType = Enum.RaycastFilterType.Exclude
    local _, hrp = getChar()
    params.FilterDescendantsInstances = hrp and { hrp.Parent } or {}
    local origin = pos + Vector3.new(0, 2, 0)
    local result = Workspace:Raycast(origin, Vector3.new(0, -CONFIG.FLOOR_RAYCAST_DIST, 0), params)
    return result ~= nil
end

local function teleportToSavedPos(pos, name, Network)
    local _, hrp = getChar()
    if not hrp or not hrp.Parent then return false end
    if not hrp.Anchored then
        pcall(function() hrp.Anchored = true end)
    end
    log(("TP -> %s @ %s"):format(tostring(name), tostring(pos)))
    local prevSafePos = STATE.lastSafePos or hrp.Position
    if Network then
        pcall(function() Network.Fire("RequestStreaming", pos) end)
        task.wait(CONFIG.TP_BUTTON_STREAM)
    end
    pcall(function()
        local ff = Instance.new("ForceField")
        ff.Visible = false
        ff.Parent = hrp.Parent
        task.delay(5, function() if ff and ff.Parent then ff:Destroy() end end)
    end)
    pcall(function() hrp.CFrame = CFrame.new(pos) end)
    task.wait(CONFIG.TP_BUTTON_VERIFY)
    if not hasFloorBelow(pos) then
        warnLog(("VOID DETECTED at %s — recovering"):format(tostring(pos)))
        pcall(function()
            if Network then Network.Fire("RequestStreaming", prevSafePos) end
            task.wait(0.3)
            hrp.CFrame = CFrame.new(prevSafePos)
        end)
        return false
    end
    STATE.lastSafePos = pos
    return true
end

refreshTeleportPanel = function(Network)
    local tp = STATE.tpPanel
    if not tp then return end
    for _, btn in pairs(tp.buttons) do
        pcall(function() btn:Destroy() end)
    end
    tp.buttons = {}

    local count = #STATE.foundRooms
    if count == 0 then
        tp.subtitle.Text = "No rooms found yet..."
        tp.subtitle.TextColor3 = Color3.fromRGB(180, 180, 200)
    else
        tp.subtitle.Text = ("%d room%s found — click to TP"):format(count, count == 1 and "" or "s")
        tp.subtitle.TextColor3 = Color3.fromRGB(120, 255, 140)
    end

    -- TP back button
    local backBtn = Instance.new("TextButton")
    backBtn.Size = UDim2.new(1, -4, 0, 28)
    backBtn.BackgroundColor3 = Color3.fromRGB(60, 40, 40)
    backBtn.BackgroundTransparency = 0.15
    backBtn.BorderSizePixel = 0
    backBtn.Font = Enum.Font.GothamBold
    backBtn.TextSize = 12
    backBtn.TextColor3 = Color3.fromRGB(255, 200, 200)
    backBtn.TextXAlignment = Enum.TextXAlignment.Left
    backBtn.Text = "  ↩ TP BACK TO LAST SAFE POS"
    backBtn.Parent = tp.scroll
    Instance.new("UICorner", backBtn).CornerRadius = UDim.new(0, 4)
    backBtn.MouseButton1Click:Connect(function()
        local safePos = STATE.lastSafePos
        local _, hrp = getChar()
        if safePos and hrp and hrp.Parent then
            pcall(function()
                if _Network then _Network.Fire("RequestStreaming", safePos) end
                task.wait(0.3)
                hrp.CFrame = CFrame.new(safePos)
            end)
        end
    end)

    for i, item in ipairs(STATE.foundRooms) do
        local pos = item.savedPos or item.pos
        if not pos and item.room and item.room.Parent then
            local ok, pivot = pcall(function() return item.room:GetPivot() end)
            if ok and pivot then
                pos = pivot.Position + Vector3.new(0, CONFIG.FLY_HEIGHT_OFFSET, 0)
                item.savedPos = pos
            end
        end

        local btn = Instance.new("TextButton")
        btn.Size = UDim2.new(1, -4, 0, 32)
        btn.BackgroundColor3 = Color3.fromRGB(40, 60, 40)
        btn.BackgroundTransparency = 0.15
        btn.BorderSizePixel = 0
        btn.Font = Enum.Font.GothamBold
        btn.TextSize = 12
        btn.TextColor3 = Color3.fromRGB(220, 255, 220)
        btn.TextXAlignment = Enum.TextXAlignment.Left
        btn.TextWrapped = true
        btn.Text = ("  [%d] %s  %s"):format(i, tostring(item.name or "?"),
            pos and ("@ %.0f, %.0f, %.0f"):format(pos.X, pos.Y, pos.Z) or "(no pos)")
        btn.Parent = tp.scroll
        Instance.new("UICorner", btn).CornerRadius = UDim.new(0, 4)
        btn.MouseButton1Click:Connect(function()
            if pos then
                btn.BackgroundColor3 = Color3.fromRGB(80, 180, 80)
                task.delay(0.4, function()
                    if btn and btn.Parent then btn.BackgroundColor3 = Color3.fromRGB(40, 60, 40) end
                end)
                teleportToSavedPos(pos, item.name, Network)
            end
        end)
        tp.buttons[item.uid] = btn
    end
end

--================================================================================================
-- Stage 1: Wait for game load
--================================================================================================
local function waitForGameLoad()
    setStage("waiting for game:IsLoaded()")
    if not game:IsLoaded() then game.Loaded:Wait() end
    setStage("waiting for ReplicatedStorage.Library")
    waitForChild(ReplicatedStorage, "Library", 60)
    setStage("waiting for PlayerGui")
    local playerGui = waitForChild(LocalPlayer, "PlayerGui", 30)
    setStage("waiting for Character / HumanoidRootPart")
    for _ = 1, 120 do
        local char, hrp, hum = getChar()
        if char and hrp and hum then return playerGui end
        task.wait(0.25)
    end
    return playerGui
end

--================================================================================================
-- Stage 2: Enter Backrooms instance (with retry — game has join cooldown)
--================================================================================================
local function enterBackroomsInstance(InstancingCmds)
    setStage("entering Backrooms instance (with retry)")

    if not InstancingCmds then
        warnLog("InstancingCmds unavailable — wait for manual entry")
        return false
    end

    -- already inside?
    local ok, inside = pcall(function() return InstancingCmds.IsInInstance("Backrooms") end)
    if ok and inside then
        log("already inside Backrooms instance")
        return true
    end

    -- bypass requirement gate
    pcall(function()
        InstancingCmds.DoesMeetRequirement = function(_, _) return true end
    end)

    -- retry loop (game has a join cooldown after server join)
    for attempt = 1, CONFIG.BACKROOMS_ENTER_MAX_RETRIES do
        log(("Backrooms enter attempt %d/%d"):format(attempt, CONFIG.BACKROOMS_ENTER_MAX_RETRIES))
        pcall(function() InstancingCmds.Enter("Backrooms") end)

        -- wait for entry
        for _ = 1, 10 do
            local ok2, inside2 = pcall(function() return InstancingCmds.IsInInstance("Backrooms") end)
            if ok2 and inside2 then
                log("successfully entered Backrooms instance")
                return true
            end
            task.wait(0.5)
        end

        -- not in yet — wait and retry
        log(("attempt %d failed — waiting %ss before retry"):format(
            attempt, CONFIG.BACKROOMS_ENTER_RETRY_INTERVAL))
        task.wait(CONFIG.BACKROOMS_ENTER_RETRY_INTERVAL)
    end

    warnLog("could not enter Backrooms instance — try walking into a portal")
    return false
end

--================================================================================================
-- Stage 3: Enter DEEP Backrooms (with retry)
--================================================================================================
local function enterDeepBackrooms(InstancingCmds, Network, Signal)
    setStage("entering Deep Backrooms (with retry)")

    local function isInDeep()
        if not Signal then return false end
        local ok, result = pcall(function() return Signal.Invoke("Backrooms_IsInDeep") end)
        return ok and result == true
    end

    if isInDeep() then
        STATE.confirmedDeep = true
        return true
    end

    local function tpTo(pos)
        local _, hrp = getChar()
        if not hrp or not hrp.Parent then return end
        pcall(function() Network.Fire("RequestStreaming", pos) end)
        task.wait(CONFIG.TP_STREAM_LEAD)
        pcall(function()
            local ff = Instance.new("ForceField")
            ff.Visible = false
            ff.Parent = hrp.Parent
            task.delay(5, function() if ff and ff.Parent then ff:Destroy() end end)
        end)
        pcall(function() hrp.CFrame = CFrame.new(pos) end)
        STATE.lastSafePos = pos
    end

    -- retry the whole deep-entry sequence multiple times
    for retry = 1, CONFIG.DEEP_ENTER_MAX_RETRIES do
        log(("Deep enter retry %d/%d"):format(retry, CONFIG.DEEP_ENTER_MAX_RETRIES))

        -- STRATEGY A: Debug_EnterDeepMaze
        local ok, result = pcall(function()
            return InstancingCmds.InvokeCustom("Debug_EnterDeepMaze")
        end)
        if ok and type(result) == "table" and result.pos then
            log("Debug_EnterDeepMaze returned pos — TPing")
            tpTo(result.pos)
            task.wait(2)
            if isInDeep() then
                STATE.confirmedDeep = true
                log("Deep entry confirmed via Debug_EnterDeepMaze")
                return true
            end
        end

        -- STRATEGY B: walk through DeepCurtainTarget from both sides
        local curtain = CollectionService:GetTagged("DeepCurtainTarget")[1]
        local _, hrp = getChar()
        if curtain and hrp and hrp.Parent then
            local cPos = curtain.Position
            local look = curtain.CFrame.LookVector
            local front = cPos + look * 6  + Vector3.new(0, 4, 0)
            local back  = cPos - look * 6  + Vector3.new(0, 4, 0)
            local far   = cPos + look * 40 + Vector3.new(0, 4, 0)

            log("walking through DeepCurtainTarget (front->back->far)")
            tpTo(cPos + Vector3.new(0, 4, 0))
            task.wait(0.6)
            tpTo(front)
            task.wait(0.6)
            tpTo(back)
            task.wait(0.8)
            tpTo(far)
            task.wait(1.5)

            if isInDeep() then
                STATE.confirmedDeep = true
                log("Deep entry confirmed via curtain walk")
                return true
            end
        end

        -- STRATEGY C: DeepSpawnLocation fallback
        local spawn = CollectionService:GetTagged("DeepSpawnLocation")[1]
        if spawn then
            log("found DeepSpawnLocation — TPing there")
            tpTo(spawn.Position + Vector3.new(0, 4, 0))
            task.wait(2)
            if isInDeep() then
                STATE.confirmedDeep = true
                log("Deep entry confirmed via DeepSpawnLocation")
                return true
            end
        end

        -- wait before next retry
        log(("deep enter retry %d failed — waiting %ss"):format(
            retry, CONFIG.DEEP_ENTER_RETRY_INTERVAL))
        task.wait(CONFIG.DEEP_ENTER_RETRY_INTERVAL)
    end

    warnLog("could not confirm Deep Backrooms entry — main loop will keep retrying")
    return false
end

--================================================================================================
-- Stage 4: Flying / anti-void
--================================================================================================
local function setupFlying()
    local char, hrp, hum = getChar()
    if not hrp then return false end
    pcall(function() hrp.Anchored = true end)
    pcall(function() hum.PlatformStand = true end)
    pcall(function() hum:ChangeState(Enum.HumanoidStateType.Physics) end)
    pcall(function()
        hum:SetStateEnabled(Enum.HumanoidStateType.FallingDown, false)
        hum:SetStateEnabled(Enum.HumanoidStateType.Ragdoll, false)
    end)
    local existingBV = hrp:FindFirstChild("PS99_Fly_BV")
    if existingBV then existingBV:Destroy() end
    local bv = Instance.new("BodyVelocity")
    bv.Name = "PS99_Fly_BV"
    bv.MaxForce = Vector3.new(math.huge, math.huge, math.huge)
    bv.Velocity = Vector3.new(0, 0, 0)
    bv.Parent = hrp
    log("flying enabled")
    return true
end

local function startYMonitor()
    task.spawn(function()
        while not STATE.stopScript do
            local _, hrp = getChar()
            if hrp and hrp.Parent then
                local pos = hrp.Position
                if pos.Y < CONFIG.VOID_Y_THRESHOLD then
                    warnLog(("VOID DETECTED (Y=%.1f) — emergency TP"):format(pos.Y))
                    pcall(function()
                        hrp.Anchored = true
                        local safe = STATE.lastSafePos or Vector3.new(0, 100, 0)
                        hrp.CFrame = CFrame.new(safe)
                    end)
                elseif pos.Y > -10 then
                    STATE.lastSafePos = pos
                end
            end
            task.wait(0.5)
        end
    end)
end

local function hookRespawn()
    local conn = LocalPlayer.CharacterAdded:Connect(function()
        task.wait(1.5)
        setupFlying()
    end)
    table.insert(STATE.connections, conn)
end

--================================================================================================
-- Stage 5: Anti-AFK (reset idle timer + jump occasionally)
--   The game's Idle Tracking script fires "Move Server" (public rejoin) if you're idle
--   too long. We reset the timer by firing "Idle Tracking: Stop Timer" and jump.
--================================================================================================
local function antiAfkTick(Network)
    local now = tick()

    -- reset idle timer every ANTI_AFK_INTERVAL seconds
    if now - STATE.lastAntiAfk > CONFIG.ANTI_AFK_INTERVAL then
        STATE.lastAntiAfk = now
        if Network then
            pcall(function() Network.Fire("Idle Tracking: Stop Timer") end)
            pcall(function() Network.Fire("Idle Tracking: Update Timer", CONFIG.IDLE_TIMER_RESET_VAL) end)
        end
        -- also fire a fake input to reset the client-side idle tracker
        pcall(function()
            VirtualInputManager:SendKeyEvent(true, Enum.KeyCode.Unknown, false, game)
            VirtualInputManager:SendKeyEvent(false, Enum.KeyCode.Unknown, false, game)
        end)
    end

    -- jump every ANTI_AFK_JUMP_INTERVAL seconds
    if now - STATE.lastJump > CONFIG.ANTI_AFK_JUMP_INTERVAL then
        STATE.lastJump = now
        local _, _, hum = getChar()
        if hum then
            pcall(function()
                hum:ChangeState(Enum.HumanoidStateType.Jumping)
            end)
        end
    end
end

--================================================================================================
-- Stage 6: Room discovery (descriptor-based, PRIMARY)
--================================================================================================
local function isTargetRoom(className)
    if not className then return false end
    className = tostring(className)
    if className == CONFIG.TARGET_ROOM_NAME then return true end
    if className:lower():find("gamemaster") then return true end
    return false
end

local function fetchDeepDescriptor(InstancingCmds)
    if not InstancingCmds then return nil end
    local inst = InstancingCmds.Get()
    if not inst then return nil end
    local ok, result = pcall(function()
        return inst:InvokeCustom("Backrooms_GetMapDescriptor", true)
    end)
    if not ok or type(result) ~= "table" then return nil end
    if not result.rooms or not result.root or not result.res then return nil end
    return result
end

local function roomWorldCenter(desc, room)
    if not desc or not room then return nil end
    local root = desc.root
    local res  = desc.res
    local cx = (room.x or 0) + (room.w or 0) / 2
    local cy = (room.y or 0) + (room.h or 0) / 2
    local worldX = (cx - 1) * res + root.X
    local worldZ = (cy - 1) * res + root.Z
    local worldY = root.Y + 10
    return Vector3.new(worldX, worldY, worldZ)
end

local function scanDescriptorForRooms(InstancingCmds)
    local desc = fetchDeepDescriptor(InstancingCmds)
    if not desc then return false end

    for i, room in ipairs(desc.rooms) do
        if isTargetRoom(room.class) then
            local worldPos = roomWorldCenter(desc, room)
            local uid = "desc:" .. tostring(i) .. ":" .. tostring(room.class)

            if not STATE.foundUIDs[uid] then
                STATE.foundUIDs[uid] = true
                local entry = {
                    room = nil, uid = uid, name = tostring(room.class),
                    pos = worldPos, fromDescriptor = true,
                    locked = room.locked == true,  -- save locked status from descriptor
                }
                if worldPos then entry.savedPos = worldPos end
                table.insert(STATE.foundRooms, entry)
                log(("FOUND boss room #%d  class=%s  pos=%s  locked=%s"):format(
                    #STATE.foundRooms, room.class, tostring(worldPos), tostring(entry.locked)))
                pcall(function() refreshTeleportPanel(_Network) end)
            else
                -- refresh position + locked status
                for _, entry in ipairs(STATE.foundRooms) do
                    if entry.uid == uid and worldPos then
                        entry.pos = worldPos
                        entry.savedPos = worldPos
                        entry.locked = room.locked == true
                        break
                    end
                end
            end
        end
    end
    return true
end

--================================================================================================
-- Stage 7: Boss farming — find breakables in current boss room, kill them
--================================================================================================

-- The BreakableFrontend cache is UNRELIABLE — it only populates for breakables
-- that have been rendered to the client, and even then it can be stale.
-- Instead, we search the WORKSPACE directly for breakable models.
-- Breakable models have these attributes:
--   BreakableUID, BreakableID, BreakableClass ("Normal" or "Chest"),
--   ParentType, ParentID, DisableDamage
-- We find models with BreakableClass == "Chest" near the room center.

-- Find all breakable MODELS in the workspace near a position.
-- Returns: table mapping uid -> { model, uid, class, id, health, maxHealth, disableDamage }
-- We read health/maxHealth from the BreakableFrontend cache if available,
-- otherwise we just use the model and its attributes.
local function findBreakableModelsNear(centerPos, radius, classFilter)
    local result = {}
    if not centerPos then return result end

    pcall(function()
        -- search the Breakables folder in workspace
        local breakablesFolder = Workspace:FindFirstChild("__THINGS")
        if breakablesFolder then
            breakablesFolder = breakablesFolder:FindFirstChild("Breakables")
        end
        -- also search workspace directly (some breakables may be parented elsewhere)
        local folders = {}
        if breakablesFolder then
            table.insert(folders, breakablesFolder)
        end
        table.insert(folders, Workspace)

        local seen = {}
        for _, folder in ipairs(folders) do
            for _, desc in ipairs(folder:GetDescendants()) do
                if desc:IsA("Model") then
                    local uid = desc:GetAttribute("BreakableUID")
                    if uid and not seen[uid] then
                        local bClass = desc:GetAttribute("BreakableClass")
                        -- if no class filter, accept all; otherwise match
                        if not classFilter or bClass == classFilter then
                            -- check distance
                            local ok, pivot = pcall(function() return desc:GetPivot() end)
                            if ok and pivot then
                                local dist = (pivot.Position - centerPos).Magnitude
                                if dist <= radius then
                                    seen[uid] = true
                                    -- try to get health from BreakableFrontend cache
                                    local health, maxHealth, disableDamage
                                    if _BreakableFrontend then
                                        local cached = _BreakableFrontend.Get(uid)
                                        if cached then
                                            health = cached.health
                                            maxHealth = cached.maxHealth
                                            disableDamage = cached.disableDamage
                                        end
                                    end
                                    -- also check model attribute for disableDamage
                                    if disableDamage == nil then
                                        disableDamage = desc:GetAttribute("DisableDamage") == true
                                    end
                                    -- read health from model attribute if cache didn't have it
                                    if not health then
                                        -- the model may have Health attribute
                                        health = desc:GetAttribute("Health")
                                    end

                                    result[uid] = {
                                        model = desc,
                                        uid = uid,
                                        class = bClass,
                                        id = desc:GetAttribute("BreakableID"),
                                        health = health,
                                        maxHealth = maxHealth,
                                        disableDamage = disableDamage,
                                        position = pivot.Position,
                                    }
                                end
                            end
                        end
                    end
                end
            end
        end
    end)

    return result
end

-- Check if a breakable is ALIVE and damageable.
-- A breakable is "alive" if: it has a model in workspace, and damage isn't disabled.
-- We DON'T require health > 0 because health data may be missing from the cache —
-- the model existing in workspace is a strong enough signal that it's alive.
-- Dead/destroyed breakables get their models removed from workspace.
local function isBreakableAlive(b)
    if not b then return false end
    if not b.model then return false end
    if not b.model.Parent then return false end  -- model was removed from workspace (dead)
    if b.disableDamage == true then return false end  -- damage disabled (invulnerable/respawning)
    -- check model's DisableDamage attribute too
    if b.model:GetAttribute("DisableDamage") == true then return false end
    -- if we have health data and it's <= 0, it's dead
    if b.health ~= nil and b.health <= 0 then return false end
    return true
end

-- Find the boss breakable in a specific boss room.
-- The boss is the ALIVE breakable with the HIGHEST maxHealth (or largest model scale)
-- within BOSS_ROOM_RADIUS of the room center.
-- Returns: bossBreakable (table) or nil
local function findBossInRoom(roomEntry)
    if not roomEntry or not roomEntry.savedPos then return nil end
    local roomCenter = roomEntry.savedPos

    -- search workspace directly for Chest-class breakables near the room
    local chests = findBreakableModelsNear(roomCenter, CONFIG.BOSS_ROOM_RADIUS, CONFIG.BOSS_CHEST_CLASS)

    local best, bestHP = nil, 0
    local aliveCount = 0
    for uid, b in pairs(chests) do
        if isBreakableAlive(b) then
            aliveCount = aliveCount + 1
            local hp = b.maxHealth or 0
            -- if no maxHealth data, use model scale as a proxy (bigger = boss)
            if hp == 0 and b.model then
                local ok, scale = pcall(function() return b.model:GetScale() end)
                if ok and scale then
                    hp = scale * 1000  -- arbitrary: scale-based comparison
                end
            end
            if hp > bestHP then
                bestHP = hp
                best = b
            end
        end
    end

    -- (removed debug logging — was causing console spam + lag)

    return best
end

-- Find all mini-chests in a specific boss room (excluding the boss itself).
-- Mini chests are "Chest" class breakables that are NOT the boss.
-- We identify them simply: any alive chest in the room that isn't the boss UID.
-- (Both boss and mini chests are class "Chest" — the only difference is the boss
-- has the highest maxHealth/scale, which we already identified via findBossInRoom.)
local function findMiniChestsInRoom(roomEntry, bossUid, bossMaxHealth)
    if not roomEntry or not roomEntry.savedPos then return {} end
    local roomCenter = roomEntry.savedPos

    local chests = findBreakableModelsNear(roomCenter, CONFIG.BOSS_ROOM_RADIUS, CONFIG.MINI_CHEST_CLASS)
    local result = {}

    for uid, b in pairs(chests) do
        -- Any alive chest that ISN'T the boss is a mini chest
        if uid ~= bossUid and isBreakableAlive(b) then
            result[uid] = b
        end
    end
    return result
end

-- Count how many pets (all players) are currently targeting a breakable by UID.
-- Uses PlayerPet.GetAll() + cpet:GetTarget() — matches what the game does internally.
-- Returns: integer count
local function countPetsOnBreakable(uid)
    if not _PlayerPet or not uid then return 0 end
    local count = 0
    pcall(function()
        local allPets = _PlayerPet.GetAll()
        if not allPets then return end
        for _, pet in pairs(allPets) do
            if pet.cpet then
                local ok, targetType, targetValue = pcall(function()
                    return pet.cpet:GetTarget()
                end)
                if ok and targetType == "Breakable" and targetValue == uid then
                    count = count + 1
                end
            end
        end
    end)
    return count
end

-- Pick the best mini chest to attack: the one with the MOST pets on it.
-- Ties broken by closest distance. Returns: uid, breakable
local function pickBestMiniChest(miniChests, myPos)
    if not miniChests then return nil, nil end
    local bestUid, bestChest, bestPetCount, bestDist = nil, nil, -1, math.huge
    for uid, b in pairs(miniChests) do
        local petCount = countPetsOnBreakable(uid)
        local dist = math.huge
        if b.model and myPos then
            local ok, pivot = pcall(function() return b.model:GetPivot() end)
            if ok and pivot then
                dist = (pivot.Position - myPos).Magnitude
            end
        end
        -- higher pet count wins; on tie, closer wins
        if petCount > bestPetCount or (petCount == bestPetCount and dist < bestDist) then
            bestPetCount = petCount
            bestDist = dist
            bestUid = uid
            bestChest = b
        end
    end
    return bestUid, bestChest, bestPetCount
end

-- FAST FARM damage technique (from GenesisX):
-- Assigns ALL pets to the SINGLE target breakable via Breakables_JoinPetBulk.
-- This ensures maximum DPS on the current target (boss OR mini chest), not split.
local function fastFarmDamage(targetUid, roomEntry, Network)
    if not targetUid or not Network then return end

    -- Get equipped pets
    local petObjs = {}
    if _PlayerPet then
        pcall(function()
            for _, p in pairs(_PlayerPet.GetByPlayer(LocalPlayer)) do
                table.insert(petObjs, p)
            end
        end)
    end
    local pCount = #petObjs
    if pCount == 0 then return end

    -- Build remotes table: ALL pets -> SINGLE target (maximum DPS on one target)
    local remotes = {}
    for _, petObj in ipairs(petObjs) do
        remotes[petObj.euid] = targetUid
    end

    -- Fire the damage + pet assignment (this is the core Fast Farm technique)
    pcall(function()
        Network.UnreliableFire("Breakables_PlayerDealDamage", targetUid)
    end)
    pcall(function()
        Network.Fire("Breakables_JoinPetBulk", remotes)
    end)
end

-- Damage a breakable by UID (uses Fast Farm technique)
local function damageBreakable(uid, Network)
    if not uid then return end
    -- The actual damage is handled by fastFarmDamage which is called separately.
    -- This function just fires the raw damage as a quick tap.
    if Network then
        pcall(function()
            Network.UnreliableFire("Breakables_PlayerDealDamage", uid)
        end)
    end
end

-- Send pets to attack a breakable (uses Fast Farm JoinPetBulk technique)
local function sendPetsToAttack(breakableModel, Network, roomEntry, targetUid)
    if not breakableModel or not _PlayerPet then return end
    -- Use the Fast Farm technique which assigns pets via JoinPetBulk
    fastFarmDamage(targetUid, roomEntry, Network)
end

-- TP to a position near a breakable
local function tpToBreakable(b, Network)
    if not b or not b.model then return end
    local _, hrp = getChar()
    if not hrp or not hrp.Parent then return end

    local ok, pivot = pcall(function() return b.model:GetPivot() end)
    if not ok or not pivot then return end

    -- TP a few studs in front of the breakable, at its height
    local targetPos = pivot.Position + Vector3.new(0, 8, 0)

    pcall(function() hrp.Anchored = true end)
    if Network then
        pcall(function() Network.Fire("RequestStreaming", targetPos) end)
        task.wait(CONFIG.TP_STREAM_LEAD)
    end
    pcall(function() hrp.CFrame = CFrame.new(targetPos) end)
    STATE.lastSafePos = targetPos
end

--================================================================================================
-- Room unlock + player count helpers
--================================================================================================

-- Find the workspace Instance for a descriptor-based room entry.
-- Searches CollectionService:GetTagged("Backrooms") for a room whose position matches.
local function findWorkspaceRoom(roomEntry)
    if not roomEntry or not roomEntry.savedPos then return nil end
    local targetPos = roomEntry.savedPos
    local best, bestDist = nil, math.huge
    pcall(function()
        for _, room in ipairs(CollectionService:GetTagged("Backrooms")) do
            if room.Parent then
                local ok, pivot = pcall(function() return room:GetPivot() end)
                if ok and pivot then
                    local dist = (pivot.Position - targetPos).Magnitude
                    if dist < 80 and dist < bestDist then
                        bestDist = dist
                        best = room
                    end
                end
            end
        end
    end)
    return best
end

-- Check if a room is locked.
-- NOTE: The descriptor's "locked" field represents whether the room HAS a locked door
-- (maze layout), NOT whether it's currently locked. It never updates after unlocking.
-- So we track unlock state ourselves via roomEntry.unlocked.
local function isRoomLocked(roomEntry, workspaceRoom)
    -- If we've explicitly unlocked this room, it's not locked
    if roomEntry and roomEntry.unlocked == true then
        return false
    end
    -- Otherwise, check the descriptor's locked field
    if roomEntry and roomEntry.locked ~= nil then
        return roomEntry.locked == true
    end
    return false
end

--================================================================================================
-- Door unlock — direct remote call
-- The door is opened via: Instancing_FireCustomFromClient("Backrooms", "AbstractRoom_FireServer", roomUID, "UnlockDoors")
-- where roomUID is the NUMERIC RoomUID from the workspace room's attribute.
-- We still TP to the door first because the server may have a distance check.
--================================================================================================

-- Navigate directly to a room's Door instance.
-- Returns: the Door instance (Model or BasePart), or nil if not found.
local function getDoorInstance(roomEntry)
    if not roomEntry or not roomEntry.name then return nil end

    local door = nil
    pcall(function()
        local things = Workspace:FindFirstChild("__THINGS")
        if not things then return end
        local ic = things:FindFirstChild("__INSTANCE_CONTAINER")
        if not ic then return end
        local active = ic:FindFirstChild("Active")
        if not active then return end
        local backrooms = active:FindFirstChild("Backrooms")
        if not backrooms then return end
        local generated = backrooms:FindFirstChild("GeneratedBackrooms")
        if not generated then return end

        local roomModel = generated:FindFirstChild(roomEntry.name)
        if not roomModel then return end

        local lockedDoors = roomModel:FindFirstChild("LockedDoors")
        if not lockedDoors then return end

        door = lockedDoors:FindFirstChild("Door")
    end)
    return door
end

-- Get the world position of a door instance.
local function getDoorPosition(door)
    if not door then return nil end
    if door:IsA("BasePart") then
        return door.Position
    end
    local ok, pivot = pcall(function() return door:GetPivot() end)
    if ok and pivot then
        return pivot.Position
    end
    return nil
end

-- Get the numeric RoomUID from the room model in GeneratedBackrooms.
-- Path: workspace.__THINGS.__INSTANCE_CONTAINER.Active.Backrooms.GeneratedBackrooms.<RoomName>
-- The RoomUID attribute is on that room model.
local function getRoomNumericUID(roomEntry)
    if not roomEntry or not roomEntry.name then return nil end

    local uid = nil
    pcall(function()
        local things = Workspace:FindFirstChild("__THINGS")
        if not things then return end
        local ic = things:FindFirstChild("__INSTANCE_CONTAINER")
        if not ic then return end
        local active = ic:FindFirstChild("Active")
        if not active then return end
        local backrooms = active:FindFirstChild("Backrooms")
        if not backrooms then return end
        local generated = backrooms:FindFirstChild("GeneratedBackrooms")
        if not generated then return end

        -- find the room model by name
        local roomModel = generated:FindFirstChild(roomEntry.name)
        if roomModel then
            uid = roomModel:GetAttribute("RoomUID")
        end

        -- fallback: search all children of GeneratedBackrooms for one with RoomUID near our position
        if not uid and roomEntry.savedPos then
            local bestDist = math.huge
            for _, child in ipairs(generated:GetChildren()) do
                local childUID = child:GetAttribute("RoomUID")
                if childUID then
                    local ok, pivot = pcall(function() return child:GetPivot() end)
                    if ok and pivot then
                        local dist = (pivot.Position - roomEntry.savedPos).Magnitude
                        if dist < bestDist then
                            bestDist = dist
                            uid = childUID
                        end
                    end
                end
            end
        end
    end)

    -- also try CollectionService tagged rooms as a last resort
    if not uid and roomEntry.savedPos then
        pcall(function()
            local targetPos = roomEntry.savedPos
            local bestDist = math.huge
            for _, room in ipairs(CollectionService:GetTagged("Backrooms")) do
                if room.Parent then
                    local roomUID = room:GetAttribute("RoomUID")
                    if roomUID then
                        local ok, pivot = pcall(function() return room:GetPivot() end)
                        if ok and pivot then
                            local dist = (pivot.Position - targetPos).Magnitude
                            if dist < 150 and dist < bestDist then
                                bestDist = dist
                                uid = roomUID
                            end
                        end
                    end
                end
            end
        end)
    end

    return uid
end

-- Get the room model from GeneratedBackrooms (used for DoorOpen attribute check).
local function getRoomModel(roomEntry)
    if not roomEntry or not roomEntry.name then return nil end
    local roomModel = nil
    pcall(function()
        local things = Workspace:FindFirstChild("__THINGS")
        local generated = things
            and things:FindFirstChild("__INSTANCE_CONTAINER")
            and things.__INSTANCE_CONTAINER:FindFirstChild("Active")
            and things.__INSTANCE_CONTAINER.Active:FindFirstChild("Backrooms")
            and things.__INSTANCE_CONTAINER.Active.Backrooms:FindFirstChild("GeneratedBackrooms")
        if generated then
            -- There can be MULTIPLE rooms with the same name (e.g. multiple GameMastersStage).
            -- Find the one closest to roomEntry.savedPos.
            local best, bestDist = nil, math.huge
            for _, child in ipairs(generated:GetChildren()) do
                if child.Name == roomEntry.name then
                    if roomEntry.savedPos then
                        local ok, pivot = pcall(function() return child:GetPivot() end)
                        if ok and pivot then
                            local dist = (pivot.Position - roomEntry.savedPos).Magnitude
                            if dist < bestDist then
                                bestDist = dist
                                best = child
                            end
                        end
                    else
                        -- no savedPos — just take the first match
                        if not best then best = child end
                    end
                end
            end
            roomModel = best
        end
    end)
    return roomModel
end

-- Check if the room's door is open via the DoorOpen attribute on the room model.
-- Returns true if DoorOpen == true.
-- Also checks the door's CanCollide as a fallback (some rooms may not have DoorOpen attribute).
local function isDoorOpen(roomEntry)
    local roomModel = getRoomModel(roomEntry)
    if not roomModel then return false end

    -- Method 1: DoorOpen attribute
    local doorOpen = roomModel:GetAttribute("DoorOpen")
    if doorOpen ~= nil then
        return doorOpen == true
    end

    -- Method 2: fallback — check if the door's CanCollide is false (open)
    local door = getDoorInstance(roomEntry)
    if door then
        pcall(function()
            for _, desc in ipairs(door:GetDescendants()) do
                if desc:IsA("BasePart") and desc.CanCollide then
                    return false  -- door is solid = closed
                end
            end
        end)
        return true  -- no solid parts found = open
    end

    return false
end

-- Try to unlock a room by trying MANY methods.
-- The key item is "Deep Daydream Key".
-- Methods tried:
--   1. InstancingCmds.FireCustom("AbstractRoom_FireServer", roomUID, "UnlockDoors")
--   2. Direct RemoteEvent: Instancing_FireCustomFromClient("Backrooms", "AbstractRoom_FireServer", roomUID, "UnlockDoors")
--   3. Try "UseKey" action instead of "UnlockDoors"
--   4. Try "Open" action
--   5. Find and fire any ProximityPrompt on the door model
--   6. Network.Invoke for key consume
local function tryUnlockRoom(roomEntry, workspaceRoom, InstancingCmds, Network)
    if not roomEntry then return end

    -- Step 1: TP to the door (server has distance check)
    local door = getDoorInstance(roomEntry)
    local doorPos = nil
    if door then
        doorPos = getDoorPosition(door)
    end

    if doorPos then
        local _, hrp = getChar()
        if hrp and hrp.Parent then
            pcall(function() hrp.Anchored = true end)
            if Network then
                pcall(function() Network.Fire("RequestStreaming", doorPos) end)
            end
            pcall(function()
                hrp.CFrame = CFrame.new(doorPos + Vector3.new(0, 5, 0))
            end)
            STATE.lastSafePos = doorPos + Vector3.new(0, 5, 0)
            task.wait(0.3)  -- short wait for streaming + distance check
        end
    end

    -- Step 2: get the numeric RoomUID
    local roomUID = getRoomNumericUID(roomEntry)
    if not roomUID then
        return
    end

    -- Step 3: fire ALL unlock methods at once (no waits between them — they're non-blocking)

    -- Method 1+2: UnlockDoors (FireCustom + direct RemoteEvent)
    if InstancingCmds then
        pcall(function()
            InstancingCmds.FireCustom("AbstractRoom_FireServer", roomUID, "UnlockDoors")
        end)
    end
    pcall(function()
        local remote = ReplicatedStorage:FindFirstChild("Network")
            and ReplicatedStorage.Network:FindFirstChild("Instancing_FireCustomFromClient")
        if remote then
            remote:FireServer("Backrooms", "AbstractRoom_FireServer", roomUID, "UnlockDoors")
        end
    end)

    -- Method 3+4: UseKey (FireCustom + direct RemoteEvent)
    if InstancingCmds then
        pcall(function()
            InstancingCmds.FireCustom("AbstractRoom_FireServer", roomUID, "UseKey")
        end)
    end
    pcall(function()
        local remote = ReplicatedStorage:FindFirstChild("Network")
            and ReplicatedStorage.Network:FindFirstChild("Instancing_FireCustomFromClient")
        if remote then
            remote:FireServer("Backrooms", "AbstractRoom_FireServer", roomUID, "UseKey")
        end
    end)

    -- Method 5: Open action
    if InstancingCmds then
        pcall(function()
            InstancingCmds.FireCustom("AbstractRoom_FireServer", roomUID, "Open")
        end)
    end

    -- Method 6: ProximityPrompt/ClickDetector on door
    if door then
        pcall(function()
            for _, desc in ipairs(door:GetDescendants()) do
                if desc:IsA("ProximityPrompt") then
                    pcall(function() fireproximityprompt(desc, 0) end)
                elseif desc:IsA("ClickDetector") then
                    pcall(function() fireclickdetector(desc) end)
                end
            end
        end)
    end

    -- Method 7: Network key consume (use task.spawn — Network.Invoke YIELDS and can hang forever)
    if Network then
        pcall(function() Network.Fire("BackroomsKey_Unlock", roomUID) end)
        task.spawn(function()
            pcall(function() Network.Invoke("BackroomsKey_Unlock", roomUID) end)
        end)
    end

    -- Step 4: short wait for server to process
    task.wait(0.5)
end

-- Count how many players (other than local) are near a room's center.
-- Returns: integer count of players within PLAYER_ROOM_RADIUS of the room.
local function countPlayersInRoom(roomEntry)
    if not roomEntry or not roomEntry.savedPos then return 0 end
    local roomCenter = roomEntry.savedPos
    local count = 0
    pcall(function()
        for _, player in ipairs(Players:GetPlayers()) do
            if player ~= LocalPlayer and player.Character then
                local hrp = player.Character:FindFirstChild("HumanoidRootPart")
                if hrp then
                    local dist = (hrp.Position - roomCenter).Magnitude
                    if dist <= CONFIG.BOSS_ROOM_RADIUS then
                        count = count + 1
                    end
                end
            end
        end
    end)
    return count
end

-- Pick the best boss room to farm: the one with the MOST players in it.
-- Ties broken by closest distance.
-- Logic (SIMPLIFIED — no locked-state tracking):
--   1. For each room: TP to door, fire UnlockDoors remote (harmless if already unlocked).
--   2. Search for breakables in the room.
--   3. If alive boss found → candidate.
--   4. Pick the one with the most players (then closest).
-- We NEVER skip a room based on locked status — we always try to unlock and always search.
local function pickBestBossRoom(InstancingCmds, Network)
    local _, hrp = getChar()
    local myPos = hrp and hrp.Position or Vector3.zero

    local bestRoom, bestBoss, bestWsRoom, bestPlayerCount, bestDist
    bestPlayerCount = -1
    bestDist = math.huge

    local candidates = {}

    for _, room in ipairs(STATE.foundRooms) do
        local wsRoom = findWorkspaceRoom(room)

        -- NOTE: Do NOT unlock here — that's done in the farm loop after picking.
        -- pickBestBossRoom should ONLY search for bosses, not unlock doors.
        -- This prevents the script from spending 10+ seconds unlocking all rooms
        -- every cycle.

        -- Search for breakables in this room
        local boss = findBossInRoom(room)
        if boss then
            local playerCount = countPlayersInRoom(room)
            local roomPos = room.savedPos or room.pos
            local dist = roomPos and (roomPos - myPos).Magnitude or 0

            table.insert(candidates, ("  %s: ALIVE boss hp=%d/%d players=%d dist=%.0f"):format(
                tostring(room.name),
                math.floor(boss.health or 0),
                math.floor(boss.maxHealth or 0),
                playerCount, dist))

            -- higher player count wins; on tie, closer wins
            if playerCount > bestPlayerCount
               or (playerCount == bestPlayerCount and dist < bestDist) then
                bestPlayerCount = playerCount
                bestDist = dist
                bestRoom = room
                bestBoss = boss
                bestWsRoom = wsRoom
            end
        else
            table.insert(candidates, ("  %s: no alive boss"):format(tostring(room.name)))
        end
    end

    -- log candidates every few seconds (not every cycle — too spammy)
    if not STATE.lastCandidateLog or tick() - STATE.lastCandidateLog > 10 then
        STATE.lastCandidateLog = tick()
        log("=== BOSS ROOM CANDIDATES ===")
        for _, c in ipairs(candidates) do
            log(c)
        end
        if bestRoom then
            log(("  -> PICKED: %s (players=%d)"):format(
                tostring(bestRoom.name), bestPlayerCount))
        else
            log("  -> PICKED: none (no alive boss in any room)")
        end
        log("===")
    end

    return bestRoom, bestBoss, bestWsRoom, bestPlayerCount
end

--================================================================================================
-- Room Preloading: TP to every found boss room with a delay so breakables load.
-- BreakableFrontend only knows about breakables that have been rendered to the client,
-- and rendering only happens when you're physically near the room. So we MUST visit
-- each room first to populate the breakable cache, otherwise findBossInRoom returns nil.
--================================================================================================
local function preloadAllRooms(Network)
    setStage("preloading boss rooms (TP to each so breakables load)")
    log(("preloading %d rooms..."):format(#STATE.foundRooms))

    for i, room in ipairs(STATE.foundRooms) do
        local pos = room.savedPos or room.pos
        if pos then
            log(("preload [%d/%d] %s @ %s"):format(
                i, #STATE.foundRooms, tostring(room.name), tostring(pos)))
            STATE.currentTarget = ("preload %d/%d"):format(i, #STATE.foundRooms)

            -- TP to the room
            local _, hrp = getChar()
            if hrp and hrp.Parent then
                pcall(function() hrp.Anchored = true end)
                pcall(function() Network.Fire("RequestStreaming", pos) end)
                task.wait(0.3)
                pcall(function() hrp.CFrame = CFrame.new(pos) end)
                STATE.lastSafePos = pos
            end

            -- wait for breakables to load
            task.wait(CONFIG.PRELOAD_DELAY)
            updateStats()
        end
    end

    log("preload complete")
    setStage("preload complete — starting boss farm")
end

-- Periodically re-visit rooms to refresh breakable data (bosses respawn, data goes stale).
-- Called from within farmBossRooms every ROOM_REFRESH_INTERVAL seconds.
local function refreshRoomBreakables(Network)
    log("refreshing room breakable data (re-visiting rooms)...")
    for i, room in ipairs(STATE.foundRooms) do
        local pos = room.savedPos or room.pos
        if pos then
            local _, hrp = getChar()
            if hrp and hrp.Parent then
                pcall(function() Network.Fire("RequestStreaming", pos) end)
                task.wait(0.15)
                pcall(function() hrp.CFrame = CFrame.new(pos) end)
                -- short wait for breakables to refresh
                task.wait(1.0)
            end
        end
    end
    log("room refresh complete")
end

-- Main boss-farming loop
-- LOGIC (fixed v7):
--   1. Find a boss room with an alive boss.
--   2. EVERY cycle, check for mini chests in that room.
--   3. If mini chests exist -> switch to them IMMEDIATELY (pick the one with most pets).
--   4. Only attack the boss when NO mini chests are alive.
--   5. This ensures mini chests are always cleared first, even if they spawn mid-fight.
-- Main boss-farming loop
-- LOGIC (v17 — room locking):
--   1. If we're NOT locked onto a room: pick the best room (most players, alive boss).
--      Once picked, LOCK onto it — we stay in this room until the boss is dead.
--   2. If we ARE locked onto a room:
--      a. Check for mini chests in the LOCKED room. If any exist -> attack nearest one.
--      b. If no mini chests -> attack the boss.
--      c. If boss is dead -> UNLOCK (set lockedRoom = nil) so we pick a new room next cycle.
--   3. Only unlock the door ONCE when we first lock onto the room (not every cycle).
local function farmBossRooms(Network, InstancingCmds, Signal)
    setStage("farming boss rooms")
    local lastRescan = 0
    local lastRoomRefresh = 0

    -- locked room state
    local lockedRoom = nil       -- the room entry we're currently fighting in
    local lockedRoomUnlocked = false  -- have we fired UnlockDoors for this room?
    local lockedRoomTpedCenter = false  -- have we TPed to room center after unlock?
    local lastPetTarget = 0

    while not STATE.stopScript do
        -- HARD GATE: must be in deep
        local _inDeep = (not CONFIG.DEEP_ONLY)
        if CONFIG.DEEP_ONLY then
            local ok, inDeep = pcall(function() return Signal.Invoke("Backrooms_IsInDeep") end)
            if ok and inDeep == true then
                STATE.confirmedDeep = true
                _inDeep = true
            else
                STATE.confirmedDeep = false
                setStage("NOT in deep — retrying deep entry...")
                enterDeepBackrooms(InstancingCmds, Network, Signal)
                task.wait(2)
            end
        end

        if not _inDeep then
            task.wait(1)
            updateStats()
        else
            -- periodic rescan for boss rooms (descriptor)
            if tick() - lastRescan > CONFIG.RESCAN_INTERVAL then
                scanDescriptorForRooms(InstancingCmds)
                lastRescan = tick()
            end

            if #STATE.foundRooms == 0 then
                setStage("waiting for boss rooms to be discovered...")
                task.wait(1)
                updateStats()
            else
                -- ===== ROOM LOCKING LOGIC =====
                if not lockedRoom then
                    -- NOT locked — pick a new room to lock onto
                    local bestRoom, bestBoss, bestWsRoom, playerCount = pickBestBossRoom(InstancingCmds, Network)

                    if bestRoom and bestBoss then
                        lockedRoom = bestRoom
                        lockedRoomUnlocked = false
                        log(("LOCKED onto room %s (players=%d)"):format(
                            tostring(bestRoom.name), playerCount or 0))
                    else
                        -- no alive boss anywhere — refresh rooms and wait
                        setStage("no alive boss found — refreshing rooms...")
                        STATE.currentTarget = "(refreshing)"
                        STATE.currentBossUid = nil
                        refreshRoomBreakables(Network)
                        lastRoomRefresh = tick()
                        task.wait(1)
                        updateStats()
                    end
                end

                -- ===== FIGHT IN THE LOCKED ROOM =====
                if lockedRoom then
                    -- Unlock the door — retry up to 10 times until DoorOpen == true.
                    -- The server needs time to process the unlock + key consumption.
                    if not lockedRoomUnlocked then
                        for attempt = 1, 10 do
                            local wsRoom = findWorkspaceRoom(lockedRoom)
                            pcall(function()
                                tryUnlockRoom(lockedRoom, wsRoom, InstancingCmds, Network)
                            end)
                            -- check if door is open now via DoorOpen attribute
                            if isDoorOpen(lockedRoom) then
                                log(("door OPEN after %d attempts — fighting"):format(attempt))
                                lockedRoomUnlocked = true
                                break
                            end
                            task.wait(0.5)  -- wait between attempts
                        end
                        -- if door still closed after 10 attempts, give up on this room
                        -- and try a different one (don't attack a boss we can't damage)
                        if not lockedRoomUnlocked then
                            log("door still closed after 10 attempts — skipping room")
                            lockedRoom = nil
                            lockedRoomTpedCenter = false
                            STATE.currentBossUid = nil
                            STATE.currentTarget = "(door locked, trying next room)"
                            task.wait(1)
                        end
                    end

                    -- TP to the boss room CENTER ONCE (not every cycle — that causes the
                    -- "teleporting back to middle" issue). Only TP after unlock, then
                    -- the fight loop TPs to the actual boss/mini-chest position.
                    if lockedRoom and not lockedRoomTpedCenter and lockedRoom.savedPos then
                        lockedRoomTpedCenter = true
                        local _, hrp = getChar()
                        if hrp and hrp.Parent then
                            pcall(function() Network.Fire("RequestStreaming", lockedRoom.savedPos) end)
                            task.wait(0.1)
                            pcall(function() hrp.CFrame = CFrame.new(lockedRoom.savedPos) end)
                            STATE.lastSafePos = lockedRoom.savedPos
                        end
                    end

                    -- Find the boss in the locked room (only if we still have a locked room)
                    local boss = nil
                    if lockedRoom then
                        boss = findBossInRoom(lockedRoom)
                    end
                    local _, hrp = getChar()
                    local myPos = hrp and hrp.Position or Vector3.zero

                    if not lockedRoom then
                        -- room was skipped (door wouldn't open) — just wait, loop will pick a new room
                        task.wait(0.5)
                    elseif not boss then
                        -- Boss is dead or gone — unlock so we pick a new room
                        log(("boss gone in locked room %s — UNLOCKING"):format(
                            tostring(lockedRoom.name)))
                        STATE.bossesKilled = STATE.bossesKilled + 1
                        lockedRoom = nil
                        lockedRoomUnlocked = false
                        lockedRoomTpedCenter = false
                        STATE.currentBossUid = nil
                        STATE.currentTarget = "(boss dead, finding next...)"
                        task.wait(1)
                    else
                        -- We have a boss — check for mini chests FIRST
                        local miniChests = findMiniChestsInRoom(lockedRoom, boss.uid, boss.maxHealth)

                        -- count mini chests for logging
                        local mcCount = 0
                        for _ in pairs(miniChests) do mcCount = mcCount + 1 end

                        -- log mini chest status (throttled to avoid spam)
                        if not STATE.lastMiniChestLog or tick() - STATE.lastMiniChestLog > 3 then
                            STATE.lastMiniChestLog = tick()
                            log(("mini chests in room: %d (boss uid=%s)"):format(
                                mcCount, tostring(boss.uid)))
                        end

                        if mcCount > 0 then
                            -- ===== MINI CHESTS EXIST — ATTACK NEAREST ONE =====
                            -- pick the nearest mini chest (not by pet count — we want to clear them fast)
                            local mcUid, mcChest, mcDist = nil, nil, math.huge
                            for uid, mc in pairs(miniChests) do
                                if mc.model then
                                    local ok, pivot = pcall(function() return mc.model:GetPivot() end)
                                    if ok and pivot then
                                        local d = (pivot.Position - myPos).Magnitude
                                        if d < mcDist then
                                            mcDist = d
                                            mcUid = uid
                                            mcChest = mc
                                        end
                                    end
                                end
                            end

                            if mcChest then
                                STATE.currentTarget = ("MiniChest @ %s (dist=%.0f)"):format(
                                    shortUID(mcUid), mcDist)
                                STATE.currentBossUid = mcUid

                                -- TP to the mini chest
                                tpToBreakable(mcChest, Network)

                                -- damage it (uses Fast Farm technique)
                                damageBreakable(mcUid, Network)

                                -- send pets EVERY cycle (fast — uses JoinPetBulk)
                                sendPetsToAttack(mcChest.model, Network, lockedRoom, mcUid)

                                -- check if it died
                                local refreshed = _BreakableFrontend and _BreakableFrontend.Get(mcUid)
                                if not refreshed or not refreshed.health or refreshed.health <= 0 then
                                    STATE.miniChestsKilled = STATE.miniChestsKilled + 1
                                    log(("KILLED mini chest %s  total=%d"):format(
                                        mcUid, STATE.miniChestsKilled))
                                end
                            end
                        else
                            -- ===== NO MINI CHESTS — ATTACK BOSS =====
                            STATE.currentBossUid = boss.uid
                            STATE.currentTarget = ("Boss @ %s (hp=%d/%d)"):format(
                                shortUID(boss.uid),
                                math.floor(boss.health or 0),
                                math.floor(boss.maxHealth or 0))

                            -- TP to the boss periodically (keep close)
                            if tick() - STATE.lastTpToBoss > CONFIG.TP_TO_BOSS_INTERVAL then
                                STATE.lastTpToBoss = tick()
                                tpToBreakable(boss, Network)
                            end

                            -- damage the boss EVERY cycle (very aggressive)
                            damageBreakable(boss.uid, Network)

                            -- send pets EVERY cycle (fast — uses JoinPetBulk)
                            sendPetsToAttack(boss.model, Network, lockedRoom, boss.uid)

                            -- check if boss died
                            local refreshed = _BreakableFrontend and _BreakableFrontend.Get(boss.uid)
                            if not refreshed or not refreshed.health or refreshed.health <= 0 then
                                STATE.bossesKilled = STATE.bossesKilled + 1
                                log(("KILLED BOSS %s!  total=%d"):format(boss.uid, STATE.bossesKilled))
                                -- boss dead — unlock so we find a new room
                                lockedRoom = nil
                                lockedRoomUnlocked = false
                                lockedRoomTpedCenter = false
                                STATE.currentBossUid = nil
                                STATE.currentTarget = "(boss killed, finding next...)"
                                task.wait(1)
                            end
                        end
                    end

                    updateStats()
                    task.wait(0.02)  -- very fast loop (50 cycles/sec) for aggressive attacking
                end
            end

            -- periodic room refresh (less frequent — we're locked onto a room now)
            if #STATE.foundRooms > 0
               and tick() - lastRoomRefresh > CONFIG.ROOM_REFRESH_INTERVAL
               and not lockedRoom then
                lastRoomRefresh = tick()
                refreshRoomBreakables(Network)
            end
        end

        -- anti-AFK tick (always)
        antiAfkTick(Network)
        updateStats()
    end
end

--================================================================================================
-- Main orchestrator
--================================================================================================
local function main()
    log("boot — Deep Backrooms Boss Farmer v6")

    local playerGui = waitForGameLoad()
    if playerGui then
        STATE.hud = buildStatusHUD(playerGui)
        STATE.tpPanel = buildTeleportPanel(playerGui)
    end
    updateStats()

    -- load modules
    local InstancingCmds = requireClient("InstancingCmds")
    local Network        = requireClient("Network")
    local Signal         = requireLib("Signal")
    _BreakableFrontend   = requireClient("BreakableFrontend")
    _PlayerPet           = requireClient("PlayerPet")
    _PetCmds             = requireClient("PetCmds")
    _BreakableCmds       = requireClient("BreakableCmds")

    _Signal = Signal
    _InstancingCmds = InstancingCmds
    _Network = Network

    if not InstancingCmds then warnLog("InstancingCmds not found") end
    if not Network        then warnLog("Network not found") end
    if not Signal         then warnLog("Signal not found") end
    if not _BreakableFrontend then warnLog("BreakableFrontend not found — boss farming won't work") end
    if not _PlayerPet     then warnLog("PlayerPet not found — pet targeting won't work") end

    -- equip best pets
    if _PetCmds then
        pcall(function() _PetCmds.EquipBest() end)
    end

    -- SUPER FAST PETS: hook PlayerPet.CalculateSpeedMultiplier to return 200
    -- (same technique as GenesisX — makes pets move insanely fast)
    if _PlayerPet and _PlayerPet.CalculateSpeedMultiplier then
        pcall(function()
            if hookfunction then
                hookfunction(_PlayerPet.CalculateSpeedMultiplier, function() return 200 end)
                log("pet speed hooked to 200x (via hookfunction)")
            end
        end)
    end

    -- enter Backrooms
    if not enterBackroomsInstance(InstancingCmds) then
        setStage("FAILED to enter Backrooms — walk into a portal manually")
        return
    end
    task.wait(2)
    updateStats()

    -- enter Deep
    enterDeepBackrooms(InstancingCmds, Network, Signal)
    task.wait(2)
    updateStats()

    -- flying
    setupFlying()
    hookRespawn()
    startYMonitor()
    task.wait(0.5)

    -- initial descriptor scan
    scanDescriptorForRooms(InstancingCmds)
    pcall(function() refreshTeleportPanel(Network) end)
    updateStats()

    -- CRITICAL: preload all rooms by TPing to each one so breakables load.
    -- Without this, findBossInRoom returns nil because BreakableFrontend
    -- only knows about breakables that have been rendered to the client.
    preloadAllRooms(Network)

    -- main farming loop (runs forever)
    farmBossRooms(Network, InstancingCmds, Signal)

    log("run complete (should not reach here — loop is infinite)")
end

task.spawn(function()
    local ok, err = pcall(main)
    if not ok then
        warnLog("main crashed: " .. tostring(err))
    end
end)

-- on respawn: re-setup flying + re-scan
LocalPlayer.CharacterAdded:Connect(function()
    task.delay(2, function()
        if not STATE.stopScript then
            setupFlying()
            if _InstancingCmds then
                scanDescriptorForRooms(_InstancingCmds)
            end
            pcall(function() refreshTeleportPanel(_Network) end)
            updateStats()
        end
    end)
end)

return nil
