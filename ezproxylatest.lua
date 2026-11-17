-- Ezproxy / SSEmu. The engine below is kept as text: it is compiled from that text when this file runs,
-- and .convert puts the same text into every converted file, so a converted file carries the whole
-- engine and runs on its own, without the proxy and without a loader URL.
local SOURCE = [==============[
-- Check for table that is shared between executions.
if not shared then
	return warn("No shared, no script.")
end

-- Initialize Luraph globals if they do not exist.
loadstring("getfenv().LPH_NO_VIRTUALIZE = function(...) return ... end")()

getfenv().PP_SCRAMBLE_NUM = function(...) return ... end
getfenv().PP_SCRAMBLE_STR = function(...) return ... end
getfenv().PP_SCRAMBLE_RE_NUM = function(...) return ... end

-- A converted file leaves a one-shot job here: the asset to run and, optionally, the original loader line.
local convertedJob = rawget(shared, "SSEmuConverted")
shared.SSEmuConverted = nil
if type(convertedJob) == "table" then
	-- The file also wrote an old style SSEmuConfig for older embedded runtimes, the user's own config comes back.
	shared.SSEmuConfig = convertedJob.previous
end
if type(convertedJob) ~= "table" then
	convertedJob = nil
	-- Files converted by older versions put the job into SSEmuConfig, it is consumed so it never sticks.
	local legacyConfig = rawget(shared, "SSEmuConfig")
	if type(legacyConfig) == "table" and legacyConfig.convertedAsset then
		convertedJob = { asset = legacyConfig.convertedAsset, entry = legacyConfig.convertedEntry }
		shared.SSEmuConfig = nil
	end
end

-- Only one instance may run at a time, stale ones from older versions are detached.
if shared.SSEmu then
	if shared.SSEmu.running then
		-- A converted file executed while the emulation is up runs inside it instead of bailing out.
		if convertedJob and type(shared.SSEmu.runConverted) == "function" then
			task.spawn(shared.SSEmu.runConverted, convertedJob.asset, convertedJob.entry, convertedJob.path)
			return
		end
		return warn("Already running.")
	end
	pcall(shared.SSEmu.detach)
end

local SSEmu = { logHandler = nil, running = true, rawInsert = setmetatable({}, { __mode = "k" }),
	dispatchThreads = setmetatable({}, { __mode = "k" }),
	rawSit = setmetatable({}, { __mode = "k" }), seatSignalMap = setmetatable({}, { __mode = "k" }), seatState = nil,
	sourceCache = {},
	armedScripts = {}, enabledScripts = {},
	clientModuleKeys = {} }
shared.SSEmu = SSEmu

-- Constants.
local CONTAINER_NAME = "Re2lua"
local SOURCE_TAG = "_sse"
local ORIGIN_ATTRIBUTE = "_sse_origin"
local FIRE_EXISTING_PLAYERS = true
local TAKEOVER_GENV = true
local ERROR_COLOR = Color3.fromRGB(255, 90, 90)
local WARN_COLOR = Color3.fromRGB(255, 200, 60)
local INFO_COLOR = Color3.fromRGB(80, 220, 120)
local REMOTE_CLASSES = { RemoteEvent = true, RemoteFunction = true, UnreliableRemoteEvent = true }
local GUI_CLASSES = { ScreenGui = true, BillboardGui = true, SurfaceGui = true }
local REPLICA_ATTRIBUTE = "_sse_replica"
local WAS_DISABLED_ATTRIBUTE = "_sse_wasdisabled"
local MODULE_WAIT_TIMEOUT = 120
local REMOTE_WAIT_TIMEOUT = 2

-- Proxy settings, override them with shared.SSEmuConfig = { url, proxy, room, key, replicate } before executing.
local config = shared.SSEmuConfig or {}
if convertedJob then
	-- Standalone converted run: the user's own settings (dropKey, hideKills, ...) are kept, the proxy is not used.
	local merged = {}
	for key, value in pairs(config) do
		merged[key] = value
	end
	merged.noProxy, merged.replicate = true, false
	merged.convertedAsset, merged.convertedEntry = convertedJob.asset, convertedJob.entry
	merged.convertedPath = convertedJob.path
	config = merged
end
local PROXY_URL = config.proxy or config.url or "http://127.0.0.1:1337"
local RELAY_URL = config.url or PROXY_URL
local RELAY_ROOM = config.room or "default"
local RELAY_KEY = config.key or ""
-- FULL REPLICATION default: replication is on from boot (disable with shared.SSEmuConfig.replicate = false).
-- A standalone converted build (noProxy) never replicates, it has no relay to talk to.
local REPLICATION_ENABLED = config.replicate ~= false and config.noProxy ~= true
if config.moduleTimeout then MODULE_WAIT_TIMEOUT = config.moduleTimeout end

-- Capture our own bytecode so .convert can embed the whole runtime with no URL and no build step.
local selfBytecode
do
	local ok, chunk = pcall(debug.info, 1, "f")
	if ok and type(chunk) == "function" and string and type(string.dump) == "function" then
		local dumped
		local dumpOk = pcall(function() dumped = string.dump(chunk) end)
		if dumpOk and type(dumped) == "string" and #dumped > 1000 then
			selfBytecode = dumped
		end
	end
end

-- Services.
local playersService = game:GetService("Players")
local runService = game:GetService("RunService")
local coreGui = game:GetService("CoreGui")
local insertService = game:GetService("InsertService")
local starterGui = game:GetService("StarterGui")
local starterPack = game:GetService("StarterPack")

-- Native references captured before any takeover.
local realGame = game
local realInstance = Instance
local nativeRequire = require
local realLoadstring = loadstring
local realTypeof = typeof
local genv = getgenv()
local renv = getrenv()
local localPlayer = playersService.LocalPlayer

---Copy a value with everything JSONEncode refuses made harmless: bytes that are not valid UTF-8
---become "?", nan and infinity become 0.
local function jsonSafe(value, depth)
	local kind = type(value)
	if kind == "string" then
		if utf8.len(value) then
			return value
		end
		return (value:gsub("[\128-\255]", "?"))
	elseif kind == "number" then
		if value ~= value or value == math.huge or value == -math.huge then
			return 0
		end
		return value
	elseif kind == "table" and depth < 10 then
		local copy = {}
		for key, item in pairs(value) do
			copy[jsonSafe(key, depth + 1)] = jsonSafe(item, depth + 1)
		end
		return copy
	end
	return value
end

---Encode a request body. One log line with broken characters (a script printing binary data) must not
---take the whole console bridge down, so a refused body is cleaned and encoded again.
---@param body table?
---@return string?
function SSEmu.encodeJson(body)
	if body == nil then
		return nil
	end
	local service = realGame:GetService("HttpService")
	local ok, text = pcall(service.JSONEncode, service, body)
	if not ok then
		ok, text = pcall(service.JSONEncode, service, jsonSafe(body, 0))
	end
	return ok and text or "{}"
end

-- State.
local active = true
local moduleCache = {}
local connections = {}
local savedGlobals = {}
local started = {}
local contexts = {}
local remotes = setmetatable({}, { __mode = "k" })
local proxyTargets = setmetatable({}, { __mode = "k" })
local origins = setmetatable({}, { __mode = "k" })
-- Source text a sandbox script assigned to a script it created, a client cannot write the real property.
local sourceOverrides = {}
local originCounter = 0
local guiSeqCounter = 0

local function nextGuiSeq()
	guiSeqCounter = guiSeqCounter + 1
	return guiSeqCounter
end
local fakeObjects = setmetatable({}, { __mode = "k" })
local fakeByBacking = setmetatable({}, { __mode = "k" })
local workspaceService = realGame:GetService("Workspace")

-- Script start rate limiting.
local MAX_STARTS_PER_SECOND = math.huge
local startWindow, startCount = 0, 0

-- Forward declarations.
local buildEnv, infect, runScript, runDescendantScripts
local requireModule, loadAsset, giveAsset, smartRequire, giveTool, spawnSource

---Track a connection so detach can clean it up.
---@param connection RBXScriptConnection
---@return RBXScriptConnection
local function track(connection)
	table.insert(connections, connection)
	return connection
end

---Return the real object behind a proxy table.
local function unwrap(value)
	return proxyTargets[value] or value
end

---typeof that reports proxied services as Instances.
local function sandboxTypeof(value)
	if type(value) == "table" and proxyTargets[value] then
		return "Instance"
	end
	return realTypeof(value)
end

---Return a stable id for the script that created an instance, used by the duplicate cleaner.
---@param inst Instance?
---@return string
local function getOrigin(inst)
	if not inst then
		return "none"
	end
	if not origins[inst] then
		originCounter = originCounter + 1
		origins[inst] = "script:" .. originCounter
	end
	return origins[inst]
end

-- Executor names never reach the console.
local hiddenNames = { "opiumware", "potassium" }
if identifyexecutor then
	local okName, executorName = pcall(identifyexecutor)
	if okName and type(executorName) == "string" then
		table.insert(hiddenNames, executorName:lower())
	end
end

---Remove executor frames, chunk names and Script 'x', Line n traces from text.
---@param text string
---@return string
local function cleanText(text)
	local lines = {}
	for line in (tostring(text) .. "\n"):gmatch("(.-)\n") do
		local lower, skip = line:lower(), false
		for _, name in ipairs(hiddenNames) do
			local escaped = name:gsub("%p", "%%%0")
			local trimmed = lower:match("^%s*(.-)%s*$")
			-- Pure frame lines such as Opiumware:244 or Script 'Opiumware', Line 244.
			if trimmed:find("^" .. escaped .. "[%w_%.%-]*:%d+%s*$")
				or trimmed:find("^" .. escaped .. "[%w_%.%-]*:%d+ function")
				or trimmed:find("^script '[^']*" .. escaped .. "[^']*', line %d+") then
				skip = true
				break
			end
			-- Error messages keep their text, only the chunk prefix goes away.
			for _, pattern in ipairs({ escaped .. "[%w_%.%-]*:%d+:?%s*", "script '[^']*" .. escaped .. "[^']*', line %d+%s*%-*%s*" }) do
				local first, last = lower:find(pattern)
				while first do
					line = line:sub(1, first - 1) .. line:sub(last + 1)
					lower = line:lower()
					first, last = lower:find(pattern)
				end
			end
		end
		if not skip and line:match("%S") then
			table.insert(lines, line)
		end
	end
	return table.concat(lines, "\n")
end

---Send a line to the proxy console when it is attached.
---@param text string
---@param color Color3?
local function log(text, color)
	if SSEmu.logHandler then
		local cleaned = cleanText(text)
		if cleaned ~= "" then
			SSEmu.logHandler(cleaned, color)
		end
	end
end

---Join varargs into one printable string.
local function joinArgs(...)
	local parts = table.pack(...)
	for index = 1, parts.n do
		parts[index] = tostring(parts[index])
	end
	return table.concat(parts, " ", 1, parts.n)
end

-- Duplicate error collapsing state.
local lastError, lastErrorTime, lastErrorCount = nil, 0, 0

---Log an error once and collapse identical repeats for a few seconds.
---@param message string
---@param trace string?
local function reportError(message, trace)
	local now = os.clock()
	if message == lastError and now - lastErrorTime < 5 then
		lastErrorCount = lastErrorCount + 1
		return false
	end

	if lastErrorCount > 0 then
		log("(previous error repeated " .. lastErrorCount .. " more times)", WARN_COLOR)
	end
	lastError, lastErrorTime, lastErrorCount = message, now, 0

	log("Error: " .. message, ERROR_COLOR)
	if trace then

		-- Show the top of the traceback in the console so the failing line is visible.
		local shown = 0
		for line in trace:gmatch("[^\n]+") do
			shown = shown + 1
			if shown > 8 then
				break
			end
			log("  " .. line, Color3.fromRGB(150, 150, 150))
		end
	end
	return true
end

---Build an error handler that names the script the error came from.
---@param inst Instance?
---@return function
local function makeErrorHandler(inst)
	return function(err)
		local where = ""
		if inst then
			local ok, fullName = pcall(function() return inst:GetFullName() end)
			where = ok and (" [" .. fullName .. "]") or ""
		end
		-- A script erroring in a loop is reported once; looking its source line up again every time
		-- (a tree scan plus a decompile) is what turns an error loop into lag.
		if not reportError(tostring(err) .. where, debug.traceback(nil, 2)) then
			return err
		end
		-- Show the failing source line so the cause is visible without opening the script.
		local scriptPath, lineText = tostring(err):match("^(.-):(%d+):")
		local lineNumber = tonumber(lineText or tostring(err):match(":(%d+):"))
		-- The error names the script it happened in (often a required module), prefer that over the caller.
		if scriptPath and SSEmu.findScript then
			local okFind, found = pcall(SSEmu.findScript, scriptPath)
			if okFind and found then
				inst = found
			end
		end
		if inst and lineNumber and SSEmu.sourceLine then
			local okLine, text = pcall(SSEmu.sourceLine, inst, lineNumber)
			if okLine and text then
				log("  line " .. lineNumber .. ": " .. text, Color3.fromRGB(150, 150, 150))
			end
		end
		return err
	end
end

local onScriptError = makeErrorHandler(nil)

---Return a hidden parent for containers.
local function getUiParent()
	if gethui then
		local ok, ui = pcall(gethui)
		if ok and ui then
			return ui
		end
	end
	return coreGui
end

---Create an instance with properties applied.
local function create(className, properties, parent)
	local object = realInstance.new(className)
	for key, value in pairs(properties) do
		object[key] = value
	end
	object.Parent = parent
	return object
end

-- Script container -> Player that counts as its owner.
local contextOwners = setmetatable({}, { __mode = "k" })

-- Emulated server containers live in a hidden folder.
local serverRoot = create("Folder", { Name = CONTAINER_NAME }, getUiParent())
local serverScriptService = create("Folder", { Name = "ServerScriptService" }, serverRoot)
local serverStorage = create("Folder", { Name = "ServerStorage" }, serverRoot)
-- Required module trees live here, outside every watched container, so nothing auto-runs.
-- Kept under serverRoot (CoreGui/gethui) so server-script GUIs that are shown in place still render.
-- Duplicates from assets that ALSO clone their GUI into PlayerGui are handled by hideTemplateTwin:
-- once the copy is shown, its matching template in this holder is disabled (not destroyed).
-- On a real server a required asset is parented to nothing, so its template GUIs are never drawn and
-- only what the hub clones into PlayerGui shows up. shared.SSEmuConfig.renderTemplates = true puts the
-- holder back under the UI root (old behaviour: every template GUI of the asset is visible).
local moduleHolder = create("Folder", { Name = "Modules" }, config.renderTemplates == true and serverRoot or nil)

-- ═══════════════════════════════════════════════════════════════════
-- REMOTES: emulated signals for mock AND real RemoteEvents/Functions
-- ═══════════════════════════════════════════════════════════════════

-- Block scoped: Luau allows 200 locals per function, only the names used later stay outside.
-- Method tables the world mirror reads on the replica side too.
local WORLD_CALL_METHODS, FE_CALL_METHODS
local newSignal, createMockRemote, lookupRemote, chatSignalFor, installRemoteHooks, selfTest, convertRemotes
do
local REMOTE_ATTRIBUTE = "_sse_remote"
local REMOTE_KEYS = {
	ClassName = true,
	OnServerEvent = true,
	OnClientEvent = true,
	OnServerInvoke = true,
	OnClientInvoke = true,
	FireServer = true,
	FireClient = true,
	FireAllClients = true,
	InvokeServer = true,
	InvokeClient = true,
}

local oldNamecall, oldIndex, oldNewIndex

-- Methods a sandbox script calls on world instances that the mirror forwards to the other clients.
WORLD_CALL_METHODS = {
	Destroy = true,
	ClearAllChildren = true,
	PivotTo = true,
	SetPrimaryPartCFrame = true,
	MoveTo = true,
	TranslateBy = true,
	BreakJoints = true,
	Remove = true,
	TakeDamage = true,
	ApplyImpulse = true,
	ApplyAngularImpulse = true,
	ApplyImpulseAtPosition = true,
	ChangeState = true,
	-- SCALE FIX: Model:ScaleTo oyun scale'i ölçekler, Humanoid:ApplyDescription karakter scale'ini
	-- ve görünümünü uygular, Humanoid:TakeDamage can düşürür — hepsi mirror'a gider.
	ScaleTo = true,
	-- EquipTool / UnequipTools / Move / ApplyDescription are not forwarded: replayed on another
	-- client's character they unequip or move tools there (their own engine handles those).
}

-- Extra methods that travel while FilteringEnabled is off (.fe disable).
FE_CALL_METHODS = {
	Play = true,
	Stop = true,
	Pause = true,
	Resume = true,
	Emit = true,
	SetAttribute = true,
	AddItem = true,
	Clear = true,
	Cancel = true,
	-- SoundService:PlayLocalSound: a sound only we would hear, played for everyone (FE disabled).
	PlayLocalSound = true,
}

---Create a small signal that supports Connect, Once, Wait and Fire.
---When buffered, a Fire with no listeners is queued and delivered to the first listener that connects,
---so a handshake message sent before the other side connects (a common race) is never lost.
---@param buffered boolean?
---@return table
function newSignal(buffered)
	local signal = { count = 0 }
	local handlers = {}
	local pending = buffered and {} or nil

	function signal:Connect(callback)
		local connection = { Connected = true }
		handlers[connection] = callback
		signal.count = signal.count + 1

		function connection:Disconnect()
			if not self.Connected then
				return
			end
			self.Connected = false
			handlers[self] = nil
			signal.count = signal.count - 1
		end
		connection.disconnect = connection.Disconnect

		-- Deliver anything that fired before any listener existed.
		if pending and #pending > 0 then
			local queued = pending
			pending = {}
			for _, packed in ipairs(queued) do
				task.spawn(callback, table.unpack(packed, 1, packed.n))
			end
		end
		return connection
	end

	function signal:Once(callback)
		local connection
		connection = signal:Connect(function(...)
			connection:Disconnect()
			callback(...)
		end)
		return connection
	end

	function signal:Wait()
		local thread = coroutine.running()
		signal:Once(function(...)
			task.spawn(thread, ...)
		end)
		return coroutine.yield()
	end

	function signal:Fire(...)
		local snapshot = {}
		for _, callback in pairs(handlers) do
			table.insert(snapshot, callback)
		end
		if #snapshot == 0 and pending then
			-- No listener yet: buffer up to a cap so an early handshake message survives.
			if #pending < 64 then
				table.insert(pending, table.pack(...))
			end
			return
		end
		for _, callback in ipairs(snapshot) do
			task.spawn(callback, ...)
		end
	end

	signal.connect, signal.once, signal.wait = signal.Connect, signal.Once, signal.Wait
	return signal
end

---Create the state table backing an emulated remote.
---@param className string
---@param isReal boolean
local function newRemoteData(className, isReal, inst)
	return {
		class = className,
		real = isReal,
		inst = inst,
		serverSignal = newSignal(true),
		clientSignal = newSignal(true),
	}
end

---Create a Bindable that is treated as a remote by the hooks.
---@param className string
---@return Instance
function createMockRemote(className)
	local backing = realInstance.new(className == "RemoteFunction" and "BindableFunction" or "BindableEvent")
	backing.Name = className
	remotes[backing] = newRemoteData(className, false, backing)
	pcall(backing.SetAttribute, backing, SOURCE_TAG, true)
	pcall(backing.SetAttribute, backing, REMOTE_ATTRIBUTE, className)
	track(backing.Destroying:Connect(function()
		remotes[backing] = nil
	end))
	return backing
end

---Start emulating a real RemoteEvent/RemoteFunction the first time a sandbox script touches it.
---@param inst Instance
---@return table?
local function adoptRemote(inst)
	if typeof(inst) ~= "Instance" then
		return nil
	end
	local ok, className = pcall(oldIndex, inst, "ClassName")
	if not ok or not REMOTE_CLASSES[className] then
		return nil
	end
	local data = newRemoteData(className, true, inst)
	remotes[inst] = data
	return data
end

---Merge engine OnClientEvent with emulated FireClient calls for real remotes.
local function makeClientSignal(inst, data)
	if not data.real then
		return data.clientSignal
	end

	local merged = {}

	function merged:Connect(callback)
		local emulated = data.clientSignal:Connect(callback)
		local ok, engine = pcall(function()
			return oldIndex(inst, "OnClientEvent"):Connect(callback)
		end)
		return {
			Connected = true,
			Disconnect = function(connection)
				connection.Connected = false
				emulated:Disconnect()
				if ok and engine then
					engine:Disconnect()
				end
			end,
		}
	end

	function merged:Once(callback)
		local connection
		connection = merged:Connect(function(...)
			connection:Disconnect()
			callback(...)
		end)
		return connection
	end

	function merged:Wait()
		return data.clientSignal:Wait()
	end

	merged.connect, merged.once, merged.wait = merged.Connect, merged.Once, merged.Wait
	return merged
end

---Run a remote method in the emulation. Returns false when the real call must go through.
---@param method string
---@param data table
---@return boolean, ...
local function dispatchRemote(method, data, ...)
	-- Mock remotes always emulate, real ones only for our own threads.
	local sandboxCaller = not data.real or checkcaller()

	if method == "FireServer" then
		if data.real and data.serverSignal.count == 0 then
			return false
		end
		data.serverSignal:Fire(localPlayer, ...)
		if sandboxCaller then
			SSEmu.replicateRemote(data, "FireServer", nil, ...)
		end
		return sandboxCaller
	elseif method == "FireClient" then
		if not sandboxCaller then
			return false
		end
		local target = ...
		if fakeObjects[target] then
			SSEmu.fakeReceived(target, data, select(2, ...))
			return true
		end

		-- A call aimed at another real player reaches that client, not this one.
		local targetId = realTypeof(target) == "Instance" and target:IsA("Player") and target.UserId or nil
		if targetId and targetId ~= localPlayer.UserId then
			SSEmu.replicateRemote(data, "FireClient", targetId, select(2, ...))
			return true
		end
		data.clientSignal:Fire(select(2, ...))
		return true
	elseif method == "FireAllClients" then
		if not sandboxCaller then
			return false
		end
		for fake in pairs(fakeObjects) do
			SSEmu.fakeReceived(fake, data, ...)
		end
		data.clientSignal:Fire(...)
		SSEmu.replicateRemote(data, "FireAllClients", nil, ...)
		return true
	elseif method == "InvokeServer" then
		if not sandboxCaller then
			return false
		end
		if data.serverInvoke then
			return true, data.serverInvoke(localPlayer, ...)
		end
		if data.real then
			return false
		end
		-- Another client's remote: its owner runs OnServerInvoke for us and answers.
		if SSEmu.remoteInvoke then
			local handled, results = SSEmu.remoteInvoke(data, ...)
			if handled then
				return true, table.unpack(results or {}, 1, (results and results.n) or 0)
			end
		end
		warn("OnServerInvoke is not set on " .. data.class)
		return true
	elseif method == "InvokeClient" then
		if not data.clientInvoke then
			return not data.real
		end
		if not sandboxCaller then
			return false
		end
		return true, data.clientInvoke(select(2, ...))
	end

	return false
end

---Resolve a remote property or method key. Returns handled, value.
---@param self Instance
---@param data table
---@param key string
local function indexRemote(self, data, key)
	local sandboxCaller = not data.real or checkcaller()

	if key == "ClassName" then
		return not data.real, data.class
	end
	if not sandboxCaller then
		return false
	end

	if key == "OnServerEvent" then
		return true, data.serverSignal
	elseif key == "OnClientEvent" then
		return true, makeClientSignal(self, data)
	elseif key == "OnServerInvoke" then
		return true, data.serverInvoke
	elseif key == "OnClientInvoke" then
		return true, data.clientInvoke
	end

	-- Method keys return a callable that routes through the dispatcher.
	return true, function(target, ...)
		local results = table.pack(dispatchRemote(key, data, ...))
		if results[1] then
			return table.unpack(results, 2, results.n)
		end
		return oldIndex(target, key)(target, ...)
	end
end

-- Hook mode reported in the console: hookmetamethod or rawmetatable.
local hookMode = "hookmetamethod"
local getAttributeFn

-- Methods the client cannot call on its own, emulated for sandbox threads.
local EMULATED_METHODS = {
	SetNetworkOwner = {
		check = function(inst) return pcall(oldIndex, inst, "Anchored") end,
		run = function() end,
	},
	SetNetworkOwnershipAuto = {
		check = function(inst) return pcall(oldIndex, inst, "Anchored") end,
		run = function() end,
	},
	GetNetworkOwner = {
		check = function(inst) return pcall(oldIndex, inst, "Anchored") end,
		run = function() return localPlayer end,
	},
	Kick = {
		check = function(inst) return inst ~= localPlayer and pcall(oldIndex, inst, "UserId") end,
		run = function(inst, reason)
			log("Kick (emulated): " .. tostring(oldIndex(inst, "Name")) .. " - " .. tostring(reason or ""), WARN_COLOR)
			-- A mirrored client that is the target kicks itself.
			if SSEmu.worldPlayer then
				pcall(SSEmu.worldPlayer, "kick", inst, reason)
			end
		end,
	},
	RequestStreamAroundAsync = {
		check = function(inst) return pcall(oldIndex, inst, "UserId") end,
		run = function() end,
	},
	SetAttributeAsync = {
		check = function() return false end,
		run = function() end,
	},
	LoadCharacter = {
		check = function(inst) return pcall(oldIndex, inst, "UserId") end,
		run = function(inst)
			-- Another player is respawned on its own client when it is mirrored.
			if inst ~= localPlayer then
				if SSEmu.worldPlayer then
					pcall(SSEmu.worldPlayer, "respawn", inst)
				end
				return
			end
			local character = localPlayer.Character
			local humanoid = character and character:FindFirstChildOfClass("Humanoid")
			if humanoid then
				humanoid.Health = 0
			end
		end,
	},
	CanSetNetworkOwnership = {
		check = function(inst) return pcall(oldIndex, inst, "Anchored") end,
		run = function() return true end,
	},
	GetNetworkPing = {
		check = function(inst) return pcall(oldIndex, inst, "UserId") end,
		run = function() return 0 end,
	},
	-- Seat:Sit is refused on the client, a hub seating the player goes through the seat emulation.
	Sit = {
		check = function(inst)
			if SSEmu.rawSit[coroutine.running()] or not SSEmu.localSit then
				return false
			end
			local ok, seat = pcall(function() return inst:IsA("Seat") or inst:IsA("VehicleSeat") end)
			return ok and seat == true
		end,
		run = function(inst, humanoid)
			task.spawn(SSEmu.localSit, inst, humanoid)
		end,
	},
}
EMULATED_METHODS.LoadCharacterWithHumanoidDescription = EMULATED_METHODS.LoadCharacter
EMULATED_METHODS.LoadCharacterAsync = EMULATED_METHODS.LoadCharacter
EMULATED_METHODS.LoadCharacterBlocking = EMULATED_METHODS.LoadCharacter

-- Methods that only a server may call: the real call is tried, a refusal is logged instead of
-- killing the script.
local TRY_METHODS = {
	ApplyDescription = true,
	ApplyDescriptionReset = true,
	AddUserAsync = true,
	RemoveCharacter = true,
	ClearCharacterAppearance = true,
	LoadCharacterAppearance = true,
	SetNetworkOwnershipAuto = true,
}

---Find or rebuild the remote state for an instance, cloned mock remotes included.
---@param inst Instance
---@param allowAdopt boolean
---@return table?
function lookupRemote(inst, allowAdopt)
	local data = remotes[inst]
	if data then
		return data
	end

	-- Clones keep the attribute, so a cloned mock remote is recovered here.
	if getAttributeFn then
		local ok, className = pcall(getAttributeFn, inst, REMOTE_ATTRIBUTE)
		if ok and type(className) == "string" then
			data = newRemoteData(className, false, inst)
			remotes[inst] = data
			return data
		end
	end

	if allowAdopt then
		return adoptRemote(inst)
	end
	return nil
end

-- Containers a real server has for every player but a client only has for itself.
local GHOST_KEYS = { PlayerGui = true, Backpack = true, StarterGear = true }
local ghostFolders = {}

---Return a stand-in container for a remote player, or nil when the real one exists.
---@param inst Instance
---@param name string
---@return Instance?
local function getGhostContainer(inst, name)
	if typeof(inst) ~= "Instance" or inst == localPlayer then
		return nil
	end
	if pcall(oldIndex, inst, name) then
		return nil
	end
	if not pcall(oldIndex, inst, "UserId") then
		return nil
	end

	local folders = ghostFolders[inst]
	if not folders then
		folders = {}
		ghostFolders[inst] = folders
	end
	if not folders[name] then
		local folder = realInstance.new("Folder")
		folder.Name = name
		folder.Parent = serverStorage
		folders[name] = folder
	end
	return folders[name]
end

-- Chat messages of every player, a server sees Player.Chatted for all of them.
local chatSignals = {}

---Return the emulated Chatted signal of a player.
---@param player Instance
---@return table
function chatSignalFor(player)
	local signal = chatSignals[player]
	if not signal then
		signal = newSignal()
		chatSignals[player] = signal
	end
	return signal
end

---Chatted source for a player: the bridged signal with TextChatService, the engine one with legacy chat.
---@param player Instance
---@return any
local function getChattedSignal(player)
	local ok, version = pcall(function()
		return realGame:GetService("TextChatService").ChatVersion
	end)
	if ok and version == Enum.ChatVersion.TextChatService then
		return chatSignalFor(player)
	end
	return oldIndex(player, "Chatted")
end

-- Seat state the engine never produced (a hand made seat weld) is answered to sandbox scripts here, so
-- Occupant, SeatPart, Humanoid.Seated and the property changed signals read like a real sit.
SSEmu.seatKeys = { Occupant = true, SeatPart = true, Seated = true, Changed = true }
SSEmu.seatClasses = { Seat = true, VehicleSeat = true }

---Merge an engine signal with an emulated one.
---@param realSignal any
---@param fakeSignal table
---@return table
function SSEmu.mergeSignal(realSignal, fakeSignal)
	local merged = {}

	function merged:Connect(callback)
		local okReal, realConnection = pcall(function()
			return realSignal:Connect(callback)
		end)
		local fakeConnection = fakeSignal:Connect(callback)
		return {
			Connected = true,
			Disconnect = function(connection)
				connection.Connected = false
				if okReal and realConnection then
					realConnection:Disconnect()
				end
				fakeConnection:Disconnect()
			end,
		}
	end

	function merged:Once(callback)
		local connection
		connection = merged:Connect(function(...)
			connection:Disconnect()
			callback(...)
		end)
		return connection
	end

	function merged:Wait()
		local thread = coroutine.running()
		merged:Once(function(...)
			task.spawn(thread, ...)
		end)
		return coroutine.yield()
	end

	merged.connect, merged.once, merged.wait = merged.Connect, merged.Once, merged.Wait
	return merged
end

---Emulated seat signals of a seat or humanoid, created on first use.
---@param inst Instance
---@return table
function SSEmu.seatSignals(inst)
	local signals = SSEmu.seatSignalMap[inst]
	if not signals then
		signals = { occupant = newSignal(), changed = newSignal(), seated = newSignal(), seatPart = newSignal() }
		SSEmu.seatSignalMap[inst] = signals
	end
	return signals
end

---Answer a seat related key for sandbox scripts. Returns handled, value.
---@param self Instance
---@param key string
function SSEmu.indexSeatState(self, key)
	local okClass, className = pcall(oldIndex, self, "ClassName")
	if not okClass then
		return false
	end
	local state = SSEmu.seatState
	if key == "Occupant" and SSEmu.seatClasses[className] then
		if state and state.seat == self then
			return true, state.humanoid
		end
		-- A mirrored client sitting in this seat on its side counts as the occupant here.
		local remote = SSEmu.remoteOccupants and SSEmu.remoteOccupants[self]
		if remote then
			return true, remote
		end
	elseif key == "SeatPart" and className == "Humanoid" then
		if state and state.humanoid == self then
			return true, state.seat
		end
	elseif key == "Seated" and className == "Humanoid" then
		return true, SSEmu.mergeSignal(oldIndex(self, key), SSEmu.seatSignals(self).seated)
	elseif key == "Changed" and SSEmu.seatClasses[className] then
		return true, SSEmu.mergeSignal(oldIndex(self, key), SSEmu.seatSignals(self).changed)
	end
	return false
end

---Handler for game.__index.
local function indexHandler(self, key)
	if active and SSEmu.seatKeys[key] and checkcaller() then
		local handled, value = SSEmu.indexSeatState(self, key)
		if handled then
			return value
		end
	end

	if active and key == "Source" and sourceOverrides[self] ~= nil and checkcaller() then
		return sourceOverrides[self]
	end

	if active and key == "Chatted" and checkcaller() then
		local ok, className = pcall(oldIndex, self, "ClassName")
		if ok and className == "Player" then
			return getChattedSignal(self)
		end
	end

	if active and GHOST_KEYS[key] and checkcaller() then
		local ghost = getGhostContainer(self, key)
		if ghost then
			return ghost
		end
	end

	if active and REMOTE_KEYS[key] then
		local data
		if key == "ClassName" then
			data = remotes[self]
		else
			data = lookupRemote(self, checkcaller())
		end
		if data then
			local handled, value = indexRemote(self, data, key)
			if handled then
				return value
			end
		end
	end
	return oldIndex(self, key)
end

---Inner handler for game.__namecall.
local function namecallInner(self, ...)
	if not active then
		return oldNamecall(self, ...)
	end

	local method = getnamecallmethod()
	local restoreMethod = setnamecallmethod or function() end
	local sandboxCaller = checkcaller()

	-- FindFirstChild/WaitForChild on a remote player resolve to the stand-in containers.
	if sandboxCaller and (method == "FindFirstChild" or method == "WaitForChild") then
		local childName = ...
		if GHOST_KEYS[childName] then
			local ghost = getGhostContainer(self, childName)
			if ghost then
				return ghost
			end
		end
	end

	-- Occupant / SeatPart changed signals also fire for the emulated sit.
	if sandboxCaller and method == "GetPropertyChangedSignal" then
		local property = ...
		if property == "Occupant" or property == "SeatPart" then
			local okClass, className = pcall(oldIndex, self, "ClassName")
			local fits = okClass and ((property == "Occupant" and SSEmu.seatClasses[className])
				or (property == "SeatPart" and className == "Humanoid"))
			if fits then
				restoreMethod(method)
				local real = oldNamecall(self, ...)
				return SSEmu.mergeSignal(real, SSEmu.seatSignals(self)[property == "Occupant" and "occupant" or "seatPart"])
			end
		end
	end

	-- Mock remotes are Bindables underneath. A search by class (FindFirstChildOfClass("RemoteEvent"))
	-- must still find them, hubs wire their buttons up that way.
	if sandboxCaller and (method == "FindFirstChildOfClass" or method == "FindFirstChildWhichIsA") then
		local className, recursive = ...
		if REMOTE_CLASSES[className] or className == "BaseRemoteEvent" then
			restoreMethod(method)
			local found = oldNamecall(self, ...)
			if found then
				return found
			end
			local okList, list = pcall(function()
				local deep = method == "FindFirstChildWhichIsA" and recursive == true
				return oldIndex(self, deep and "GetDescendants" or "GetChildren")(self)
			end)
			if okList and type(list) == "table" then
				for _, child in ipairs(list) do
					local data = lookupRemote(child, false)
					if data and not data.real and (data.class == className
						or (className == "BaseRemoteEvent" and data.class ~= "RemoteFunction")) then
						return child
					end
				end
			end
			return nil
		end
	end

	-- A server script would have created the remote already, so create it instead of yielding forever.
	if sandboxCaller and method == "WaitForChild" and select("#", ...) == 1 then
		local childName = ...
		local lowerName = type(childName) == "string" and childName:lower() or ""
		local looksRemote = lowerName:find("remote", 1, true) or lowerName:find("unreliable", 1, true) or lowerName:find("net", 1, true)
		if looksRemote and getAttributeFn then
			local tagged, isEmulated = pcall(getAttributeFn, self, SOURCE_TAG)
			if tagged and isEmulated then
				restoreMethod(method)
				local found = oldNamecall(self, childName, REMOTE_WAIT_TIMEOUT)
				if found then
					return found
				end

				local remoteClass = "RemoteEvent"
				if lowerName:find("function", 1, true) then
					remoteClass = "RemoteFunction"
				elseif lowerName:find("unreliable", 1, true) then
					remoteClass = "UnreliableRemoteEvent"
				end
				local remote = createMockRemote(remoteClass)
				remote.Name = childName
				remote.Parent = self
				log("Created missing remote: " .. childName .. " (" .. remoteClass .. ")", WARN_COLOR)
				return remote
			end
		end
	end

	-- Emulated server-only methods run for our own threads only.
	local emulated = EMULATED_METHODS[method]
	if emulated and sandboxCaller and emulated.check(self) then
		return emulated.run(self, ...)
	end
	if sandboxCaller and (method == "LoadAsset" or method == "LoadAssetVersion") and self == insertService
		and SSEmu.insertAsset and not SSEmu.rawInsert[coroutine.running()] then
		return SSEmu.insertAsset((...))
	end
	if sandboxCaller and TRY_METHODS[method] then
		restoreMethod(method)
		local results = table.pack(pcall(oldNamecall, self, ...))
		if results[1] then
			return table.unpack(results, 2, results.n)
		end
		log(method .. " is server only, ignored (" .. tostring(results[2]) .. ")", WARN_COLOR)
		return nil
	end

	-- Tweens: TweenService:Create is remembered (target, info, goals) so its Play reaches the other
	-- clients as the same tween. The engine runs tweens itself, no property write is ever seen.
	if method == "Create" and SSEmu.onTweenCreated and (sandboxCaller or SSEmu.feOffAll)
		and self == SSEmu.tweenService then
		restoreMethod(method)
		local tween = oldNamecall(self, ...)
		pcall(SSEmu.onTweenCreated, tween, ...)
		return tween
	end

	-- World mirror: a sandbox Destroy / PivotTo / MoveTo on a world instance reaches the other clients.
	if (sandboxCaller or SSEmu.feOffAll) and SSEmu.worldCall
		-- Sound:Play/Stop/Pause/Resume, ParticleEmitter:Emit, SetAttribute from our own scripts always
		-- travel (a mirrored sound would otherwise exist but stay silent); game scripts only when FE is off.
		and (WORLD_CALL_METHODS[method] or ((sandboxCaller or SSEmu.feOff) and FE_CALL_METHODS[method])) then
		pcall(SSEmu.worldCall, self, method, sandboxCaller, ...)
		restoreMethod(method)
	end

	local data = remotes[self]
	if not data and REMOTE_KEYS[method] then
		data = lookupRemote(self, sandboxCaller)
		restoreMethod(method)
	end
	if not data then
		return oldNamecall(self, ...)
	end

	if REMOTE_KEYS[method] then
		local results = table.pack(dispatchRemote(method, data, ...))
		if results[1] then
			return table.unpack(results, 2, results.n)
		end
	elseif method == "IsA" and not data.real then
		local className = ...
		if className == data.class or className == "BaseRemoteEvent" or className == "Instance" then
			return true
		end
	elseif method == "Clone" and not data.real then
		restoreMethod(method)
		local copy = oldNamecall(self, ...)
		remotes[copy] = newRemoteData(data.class, false, copy)
		return copy
	end

	restoreMethod(method)
	return oldNamecall(self, ...)
end

---Handler for game.__namecall, swaps server proxies for the real objects before the engine sees them.
local function namecallHandler(self, ...)
	if active and checkcaller() then
		local args = table.pack(...)
		local changed = false

		for index = 1, args.n do
			local value = args[index]
			local target = type(value) == "table" and proxyTargets[value]
			if target then
				args[index] = target
				changed = true
			end
		end

		if changed then
			return namecallInner(self, table.unpack(args, 1, args.n))
		end
	end
	return namecallInner(self, ...)
end

---Handler for game.__newindex.
local function newIndexHandler(self, key, value)
	if active and type(value) == "table" and proxyTargets[value] and checkcaller() then
		value = proxyTargets[value]
	end

	-- script.Source = "..." is kept on our side and compiled when the script starts.
	if active and key == "Source" and type(value) == "string" and checkcaller() then
		local okClass, className = pcall(oldIndex, self, "ClassName")
		if okClass and (className == "Script" or className == "LocalScript" or className == "ModuleScript") then
			sourceOverrides[self] = value
			pcall(oldNewIndex, self, key, value)
			return
		end
	end

	if active and (key == "OnServerInvoke" or key == "OnClientInvoke") then
		local sandboxCaller = checkcaller()
		local data = lookupRemote(self, sandboxCaller)
		if data and (not data.real or sandboxCaller) then
			if key == "OnServerInvoke" then
				data.serverInvoke = value
			else
				data.clientInvoke = value
				if data.real then
					pcall(oldNewIndex, self, key, value)
				end
			end
			return
		end
	end

	-- World mirror: a property a sandbox script writes on a world instance is sent to the other clients
	-- once the engine accepted it (a refused write errors here and is never sent).
	if active and SSEmu.worldWrite then
		local executorCaller = checkcaller()
		if executorCaller or SSEmu.feOffAll then
			-- A reparent is described by where the instance was before the write.
			local before
			if key == "Parent" and SSEmu.feOff and SSEmu.feBefore then
				local okBefore, result = pcall(SSEmu.feBefore, self)
				before = okBefore and result or nil
			end
			oldNewIndex(self, key, value)
			pcall(SSEmu.worldWrite, self, key, executorCaller, before)
			return
		end
	end
	return oldNewIndex(self, key, value)
end

---Install one metamethod hook, falling back to a raw metatable write.
---@param name string
---@param handler function
---@param forceRaw boolean
---@return function
local function installHook(name, handler, forceRaw)
	if not forceRaw then
		local ok, old = pcall(hookmetamethod, realGame, name, newcclosure(handler))
		if ok and old then
			return old
		end
	end

	local metatable = getrawmetatable(realGame)
	local old = rawget(metatable, name)
	if setreadonly then
		pcall(setreadonly, metatable, false)
	elseif make_writeable then
		pcall(make_writeable, metatable)
	end
	rawset(metatable, name, newcclosure(handler))
	hookMode = "rawmetatable"
	return old
end

---Hook the game metatable so remotes expose the emulated server API.
---@param forceRaw boolean
function installRemoteHooks(forceRaw)
	if not (newcclosure and getnamecallmethod and checkcaller and (hookmetamethod or getrawmetatable)) then
		return log("Executor lacks metamethod hooking, remotes are disabled.", ERROR_COLOR)
	end

	-- A second install (the raw fallback) would find our own handlers in the metatable and take them
	-- for the originals, which recurses forever. The originals from the first install are kept.
	local previousIndex, previousNamecall, previousNewIndex = oldIndex, oldNamecall, oldNewIndex
	local hooked = installHook("__index", indexHandler, forceRaw)
	oldIndex = previousIndex or hooked
	hooked = installHook("__namecall", namecallHandler, forceRaw)
	oldNamecall = previousNamecall or hooked
	hooked = installHook("__newindex", newIndexHandler, forceRaw)
	oldNewIndex = previousNewIndex or hooked
	getAttributeFn = oldIndex(realGame, "GetAttribute")
end

---Verify the remote emulation end to end.
---@return boolean, string?
function selfTest()
	return pcall(function()
		local event = createMockRemote("RemoteEvent")
		event.Parent = serverScriptService

		local received
		event.OnServerEvent:Connect(function(player, value)
			received = { player, value }
		end)
		event:FireServer(42)
		assert(received and received[1] == localPlayer and received[2] == 42, "FireServer -> OnServerEvent")

		local clientReceived
		event.OnClientEvent:Connect(function(value)
			clientReceived = value
		end)
		event:FireClient(localPlayer, 7)
		assert(clientReceived == 7, "FireClient -> OnClientEvent")

		local copy = event:Clone()
		local copyReceived
		copy.OnServerEvent:Connect(function(_, value)
			copyReceived = value
		end)
		copy:FireServer(9)
		assert(copyReceived == 9, "Clone remote")

		local func = createMockRemote("RemoteFunction")
		func.Parent = serverScriptService
		func.OnServerInvoke = function(_, value)
			return value * 2
		end
		assert(func:InvokeServer(21) == 42, "InvokeServer")
		assert(event.ClassName == "RemoteEvent" and event:IsA("RemoteEvent"), "ClassName/IsA")

		event:Destroy()
		copy:Destroy()
		func:Destroy()
	end)
end

---Replace real remotes inside a loaded asset with mock remotes.
---@param root Instance
function convertRemotes(root)
	for _, node in ipairs(root:GetDescendants()) do
		if REMOTE_CLASSES[node.ClassName] then
			local replacement = createMockRemote(node.ClassName)
			replacement.Name = node.Name
			for _, name in ipairs({ "_sse_src", "_sse_key" }) do
				local okAttr, value = pcall(node.GetAttribute, node, name)
				if okAttr and value ~= nil then
					pcall(replacement.SetAttribute, replacement, name, value)
				end
			end
			for _, child in ipairs(node:GetChildren()) do
				child.Parent = replacement
			end
			replacement.Parent = node.Parent
			node:Destroy()
		end
	end
end


end

-- ═══════════════════════════════════════════════════════════════════
-- SERVER PROXIES: game, Players, RunService
-- ═══════════════════════════════════════════════════════════════════

-- Override value that makes a proxy key read as nil.
local NIL = {}

---Wrap an object so selected keys can be overridden. A NIL override makes the key read as nil.
---__missing(key) supplies values for members the real object lacks, __set[key](value) intercepts writes.
---@param target Instance
---@param overrides table
local function makeProxy(target, overrides)
	local proxy = setmetatable({}, {
		__index = function(_, key)
			local override = overrides[key]
			if override == NIL then
				return nil
			end
			if override ~= nil then
				return override
			end

			local ok, value = pcall(function()
				return target[key]
			end)
			if not ok then
				local missing = overrides.__missing and overrides.__missing(key)
				if missing ~= nil then
					return missing
				end
				error(value, 2)
			end

			if type(value) == "function" then
				return function(_, ...)
					return value(target, ...)
				end
			end
			return value
		end,
		__newindex = function(_, key, value)
			local setter = overrides.__set and overrides.__set[key]
			if setter then
				return setter(value)
			end
			-- Server-only properties that a client cannot write are ignored instead of erroring.
			local ok, err = pcall(function()
				target[key] = value
			end)
			if not ok and overrides.__strictSet then
				error(err, 2)
			end
		end,
		__tostring = function()
			return target.Name
		end,
	})
	proxyTargets[proxy] = target
	return proxy
end

local playersOverrides, playersProxy
do
-- ═══════════════════════════════════════════════════════════════════
-- FAKE PLAYERS: stand-ins that server scripts see as real players
-- ═══════════════════════════════════════════════════════════════════

local fakeList = {}
local fakeAddedSignal = newSignal()
local fakeRemovingSignal = newSignal()
local fakeUserCounter = 0
local fakeMethods = {}
local fakeMetatable = {}

fakeMetatable.__index = function(self, key)
	local method = fakeMethods[key]
	if method ~= nil then
		return method
	end

	if type(key) == "string" then
		local child = rawget(self, "backing"):FindFirstChild(key)
		if child then
			return child
		end
	end
	error(tostring(key) .. " is not a valid member of Player \"" .. rawget(self, "Name") .. "\"", 2)
end

fakeMetatable.__tostring = function(self)
	return rawget(self, "Name")
end

---Build a character for a fake player, cloned from the local one when possible.
---@param fake table
---@return Instance
local function buildFakeCharacter(fake)
	local old = rawget(fake, "Character")
	if old then
		pcall(function()
			old:Destroy()
		end)
	end

	local character
	local source = localPlayer.Character
	if source then
		local cloned, copy = pcall(function()
			return source:Clone()
		end)
		if cloned and copy then
			character = copy
			for _, node in ipairs(character:GetDescendants()) do
				if node:IsA("BaseScript") then
					node:Destroy()
				end
			end
		end
	end

	-- Fallback rig when the local character cannot be cloned.
	if not character then
		character = realInstance.new("Model")
		local root = realInstance.new("Part")
		root.Name = "HumanoidRootPart"
		root.Size = Vector3.new(2, 2, 1)
		root.Parent = character
		character.PrimaryPart = root
		realInstance.new("Humanoid").Parent = character
	end

	character.Name = rawget(fake, "Name")
	local humanoid = character:FindFirstChildOfClass("Humanoid")
	if humanoid then
		humanoid.DisplayName = rawget(fake, "DisplayName")
		humanoid.Health = humanoid.MaxHealth
	end

	-- Stand next to the real player.
	local root = character:FindFirstChild("HumanoidRootPart")
	local sourceRoot = source and source:FindFirstChild("HumanoidRootPart")
	if root and sourceRoot then
		local offset = ((#fakeList - 1) % 8 + 1) * 4
		root.CFrame = sourceRoot.CFrame * CFrame.new(offset, 0, -4)
	end

	pcall(function()
		character:SetAttribute(SOURCE_TAG, true)
	end)
	character.Parent = workspaceService
	rawset(fake, "Character", character)
	fake.CharacterAdded:Fire(character)
	return character
end

fakeMethods.IsA = function(_, className)
	return className == "Player" or className == "Instance" or className == "Object"
end

fakeMethods.GetMouse = function()
	return {
		Hit = CFrame.new(),
		Target = nil,
		X = 0,
		Y = 0,
		Button1Down = newSignal(),
		Button1Up = newSignal(),
		Move = newSignal(),
		KeyDown = newSignal(),
	}
end

fakeMethods.Kick = function(self, reason)
	log("[fake:" .. rawget(self, "Name") .. "] kicked: " .. tostring(reason or ""), WARN_COLOR)
	SSEmu.removeFakePlayer(self)
end

fakeMethods.Destroy = function(self)
	SSEmu.removeFakePlayer(self)
end

fakeMethods.LoadCharacter = function(self)
	return buildFakeCharacter(self)
end

fakeMethods.Chat = function(self, message)
	log("[fake:" .. rawget(self, "Name") .. "] " .. tostring(message), Color3.fromRGB(180, 140, 255))
	rawget(self, "Chatted"):Fire(tostring(message))
end

---Fire a remote as this fake player, so OnServerEvent receives the fake as the sender.
fakeMethods.FireServer = function(self, remote, ...)
	local data = lookupRemote(unwrap(remote), true)
	if not data then
		return log("[fake] FireServer needs a remote.", WARN_COLOR)
	end
	if data.class == "RemoteFunction" and data.serverInvoke then
		return data.serverInvoke(self, ...)
	end
	data.serverSignal:Fire(self, ...)
end

fakeMethods.GetAttribute = function(self, name)
	return rawget(self, "attributes")[name]
end

fakeMethods.SetAttribute = function(self, name, value)
	rawget(self, "attributes")[name] = value
end

fakeMethods.GetAttributes = function(self)
	return table.clone(rawget(self, "attributes"))
end

fakeMethods.FindFirstChild = function(self, name)
	return rawget(self, "backing"):FindFirstChild(name)
end

fakeMethods.WaitForChild = fakeMethods.FindFirstChild

fakeMethods.FindFirstChildOfClass = function(self, className)
	return rawget(self, "backing"):FindFirstChildOfClass(className)
end

fakeMethods.GetChildren = function(self)
	return rawget(self, "backing"):GetChildren()
end

fakeMethods.DistanceFromCharacter = function(self, point)
	local character = rawget(self, "Character")
	local root = character and character:FindFirstChild("HumanoidRootPart")
	return root and (root.Position - point).Magnitude or 0
end

fakeMethods.IsFriendsWith = function()
	return false
end

fakeMethods.IsInGroup = function()
	return false
end

fakeMethods.GetRankInGroup = function()
	return 0
end

fakeMethods.GetRoleInGroup = function()
	return "Guest"
end

fakeMethods.HasAppearanceLoaded = function()
	return true
end

fakeMethods.GetJoinData = function()
	return {}
end

---Create a Player stand-in that server scripts can use like a real Player.
---@param name string
---@param userId number?
---@return table
function SSEmu.createFakePlayer(name, userId)
	name = tostring(name)
	for _, existing in ipairs(fakeList) do
		if rawget(existing, "Name") == name then
			return existing
		end
	end

	fakeUserCounter = fakeUserCounter + 1
	local backing = create("Folder", { Name = "Player_" .. name }, serverStorage)
	for _, folderName in ipairs({ "Backpack", "PlayerGui", "StarterGear" }) do
		create("Folder", { Name = folderName }, backing)
	end

	local fake = setmetatable({
		Name = name,
		DisplayName = name,
		UserId = userId or -(100 + fakeUserCounter),
		ClassName = "Player",
		AccountAge = 365,
		Parent = playersService,
		Neutral = true,
		CanLoadCharacterAppearance = true,
		Chatted = newSignal(),
		CharacterAdded = newSignal(),
		CharacterRemoving = newSignal(),
		CharacterAppearanceLoaded = newSignal(),
		Received = newSignal(),
		attributes = {},
		backing = backing,
	}, fakeMetatable)

	fakeObjects[fake] = true
	fakeByBacking[backing] = fake
	proxyTargets[fake] = backing
	table.insert(fakeList, fake)
	log("Fake player joined: " .. name, INFO_COLOR)

	-- Same order as a real join: PlayerAdded first, then the character.
	fakeAddedSignal:Fire(fake)
	buildFakeCharacter(fake)
	return fake
end

---Remove a fake player the way a leaving player is removed.
---@param fake table
function SSEmu.removeFakePlayer(fake)
	local index = table.find(fakeList, fake)
	if not index then
		return
	end
	table.remove(fakeList, index)
	fakeRemovingSignal:Fire(fake)

	local character = rawget(fake, "Character")
	if character then
		rawget(fake, "CharacterRemoving"):Fire(character)
		pcall(function()
			character:Destroy()
		end)
	end
	pcall(function()
		rawget(fake, "backing"):Destroy()
	end)
	log("Fake player left: " .. rawget(fake, "Name"), INFO_COLOR)
end

---Return the list of fake players.
---@return table
function SSEmu.getFakePlayers()
	return fakeList
end

---Make a fake player say something so Chatted listeners react.
---@param name string
---@param message string
---@return boolean
function SSEmu.fakeChat(name, message)
	for _, fake in ipairs(fakeList) do
		if rawget(fake, "Name") == name then
			fake:Chat(message)
			return true
		end
	end
	return false
end

---Log what a fake player received from a FireClient call and let listeners react.
---@param fake table
---@param data table
function SSEmu.fakeReceived(fake, data, ...)
	log("[fake:" .. rawget(fake, "Name") .. "] " .. data.class .. " received (" .. joinArgs(...) .. ")", Color3.fromRGB(180, 140, 255))
	rawget(fake, "Received"):Fire(data.inst, ...)
end

-- ═══════════════════════════════════════════════════════════════════
-- PLAYERS PROXY: real players plus fake players
-- ═══════════════════════════════════════════════════════════════════

---Every player a server would list, real and fake.
---@return table
local function allPlayers()
	local list = playersService:GetPlayers()
	for _, fake in ipairs(fakeList) do
		table.insert(list, fake)
	end
	return list
end

---Loader lines are often run with a display name, another case, half a name or somebody else's name,
---and the hub then indexes nil. A name lookup falls back the way an admin command would resolve it.
---Disable with shared.SSEmuConfig.lenientPlayers = false.
---@param name any
---@param allowSelf boolean Fall back to the local player when nobody matches.
---@return any
local function lenientPlayer(name, allowSelf)
	if config.lenientPlayers == false or type(name) ~= "string" or name == "" then
		return nil
	end
	local wanted = name:lower()
	local partial
	for _, player in ipairs(allPlayers()) do
		local playerName, displayName = tostring(player.Name):lower(), tostring(player.DisplayName):lower()
		if playerName == wanted or displayName == wanted then
			return player
		end
		if not partial and (playerName:sub(1, #wanted) == wanted or displayName:sub(1, #wanted) == wanted) then
			partial = player
		end
	end
	if partial then
		return partial
	end
	if allowSelf then
		log("Players: no player named \"" .. name .. "\", using " .. localPlayer.Name .. " instead", WARN_COLOR)
		return localPlayer
	end
	return nil
end

---Merge a real player signal with the fake one.
---@param realSignal table
---@param fakeSignal table
---@param fireExisting boolean
local function mergedPlayerSignal(realSignal, fakeSignal, fireExisting)
	local function connect(callback, existing)
		if existing then
			for _, player in ipairs(allPlayers()) do
				task.spawn(callback, player)
			end
		end

		local realConnection = realSignal:Connect(callback)
		local fakeConnection = fakeSignal:Connect(callback)
		return {
			Connected = true,
			Disconnect = function(connection)
				connection.Connected = false
				realConnection:Disconnect()
				fakeConnection:Disconnect()
			end,
		}
	end

	local merged = {}

	function merged:Connect(callback)
		return connect(callback, fireExisting)
	end

	function merged:Once(callback)
		local connection
		connection = connect(function(...)
			connection:Disconnect()
			callback(...)
		end, false)
		return connection
	end

	function merged:Wait()
		local thread = coroutine.running()
		merged:Once(function(...)
			task.spawn(thread, ...)
		end)
		return coroutine.yield()
	end

	merged.connect, merged.once, merged.wait = merged.Connect, merged.Once, merged.Wait
	return merged
end

---Build the overrides that make Players behave like the server one.
---@return table
local function makePlayersOverrides()
	return {
		PlayerAdded = mergedPlayerSignal(playersService.PlayerAdded, fakeAddedSignal, FIRE_EXISTING_PLAYERS),
		PlayerRemoving = mergedPlayerSignal(playersService.PlayerRemoving, fakeRemovingSignal, false),
		GetPlayers = function()
			return allPlayers()
		end,
		GetChildren = function()
			return allPlayers()
		end,
		GetPlayerByUserId = function(_, userId)
			for _, player in ipairs(allPlayers()) do
				if player.UserId == userId then
					return player
				end
			end
			return nil
		end,
		GetPlayerFromCharacter = function(_, character)
			for _, fake in ipairs(fakeList) do
				if rawget(fake, "Character") == character then
					return fake
				end
			end
			return playersService:GetPlayerFromCharacter(character)
		end,
		FindFirstChild = function(_, name)
			for _, fake in ipairs(fakeList) do
				if rawget(fake, "Name") == name then
					return fake
				end
			end
			return playersService:FindFirstChild(name) or lenientPlayer(name, true)
		end,
		WaitForChild = function(_, name, timeout)
			for _, fake in ipairs(fakeList) do
				if rawget(fake, "Name") == name then
					return fake
				end
			end
			local found = playersService:FindFirstChild(name) or lenientPlayer(name, true)
			if found then
				return found
			end
			return playersService:WaitForChild(name, timeout)
		end,
		__missing = function(key)
			for _, fake in ipairs(fakeList) do
				if rawget(fake, "Name") == key then
					return fake
				end
			end
			return lenientPlayer(key, true)
		end,
	}
end

---Ban like a server would: the local player is kicked when it is targeted.
local function banResult(config)
	config = type(config) == "table" and config or {}
	local ids = config.UserIds or {}
	for _, id in ipairs(ids) do
		if id == playersService.LocalPlayer.UserId then
			task.defer(function()
				playersService.LocalPlayer:Kick(tostring(config.DisplayReason or config.PrivateReason or "Banned"))
			end)
		end
	end
	if SSEmu.logHandler then
		SSEmu.logHandler("BanAsync: " .. #ids .. " user(s), duration " .. tostring(config.Duration or "permanent"))
	end
end

playersOverrides = makePlayersOverrides()
playersOverrides.BanAsync = function(_, config) return banResult(config) end
playersOverrides.UnbanAsync = function() end
playersOverrides.GetBanHistoryAsync = function()
	return { GetCurrentPage = function() return {} end, IsFinished = true, AdvanceToNextPageAsync = function() end }
end
playersOverrides.CharacterAutoLoads = true
playersProxy = makeProxy(playersService, playersOverrides)
end

---Strict server mode: a real server has no LocalPlayer, so Players.LocalPlayer reads nil for server scripts.
---@param enabled boolean
function SSEmu.setStrict(enabled)
	playersOverrides.LocalPlayer = enabled and NIL or nil
	playersOverrides.localPlayer = enabled and NIL or nil
end
if config.strictServer == true then
	SSEmu.setStrict(true)
end

local runProxy = makeProxy(runService, {
	IsServer = function() return true end,
	IsClient = function() return false end,
	IsStudio = function() return false end,
	IsRunMode = function() return true end,
})

-- Block scoped: Luau allows 200 locals per function, only the names used later stay outside.
local closeCallbacks, executorRequest, mockGame
do
-- Callbacks registered through game:BindToClose.
closeCallbacks = {}

---Send an HTTP request through the executor request function.
---@param options table
---@return table
function executorRequest(options)
	local requestFunction = request or http_request or (syn and syn.request) or (http and http.request)
	if not requestFunction then
		error("HttpService emulation needs an executor request function.", 3)
	end
	return requestFunction(options)
end

-- DataStores live in memory and, when the executor has a filesystem, in one file per place so
-- hub data survives a rejoin. Disable with shared.SSEmuConfig.persistData = false.
local dataStores = {}
local DATA_FILE = "ezproxy_datastores_" .. tostring(realGame.PlaceId) .. ".json"
local dataSaveQueued = false

if config.persistData ~= false and readfile and isfile then
	pcall(function()
		if isfile(DATA_FILE) then
			local decoded = realGame:GetService("HttpService"):JSONDecode(readfile(DATA_FILE))
			if type(decoded) == "table" then
				dataStores = decoded
			end
		end
	end)
end

---Write the stores to disk shortly after a change, bursts are collapsed into one write.
local function saveDataStores()
	if config.persistData == false or not writefile or dataSaveQueued then
		return
	end
	dataSaveQueued = true
	task.delay(2, function()
		dataSaveQueued = false
		pcall(function()
			writefile(DATA_FILE, realGame:GetService("HttpService"):JSONEncode(dataStores))
		end)
	end)
end

---Empty pages object for the list style calls.
local function emptyPages(rows)
	return { GetCurrentPage = function() return rows or {} end, IsFinished = true, AdvanceToNextPageAsync = function() end }
end

---Build a DataStore object over one table. Keys are strings, like the real service.
---@param data table
local function newDataStore(data)
	local store = {}
	local keyInfo = {
		CreatedTime = 0, UpdatedTime = 0, Version = "sse",
		GetUserIds = function() return {} end,
		GetMetadata = function() return {} end,
	}

	function store:GetAsync(key)
		return data[tostring(key)], keyInfo
	end

	function store:SetAsync(key, value)
		data[tostring(key)] = value
		saveDataStores()
		return "sse"
	end

	function store:UpdateAsync(key, callback)
		key = tostring(key)
		local updated = callback(data[key], keyInfo)
		if updated ~= nil then
			data[key] = updated
			saveDataStores()
		end
		return data[key], keyInfo
	end

	function store:IncrementAsync(key, delta)
		key = tostring(key)
		data[key] = (tonumber(data[key]) or 0) + (delta or 1)
		saveDataStores()
		return data[key], keyInfo
	end

	function store:GetSortedAsync(ascending)
		local rows = {}
		for key, value in pairs(data) do
			table.insert(rows, { key = key, value = value })
		end
		table.sort(rows, function(a, b)
			if ascending then
				return (tonumber(a.value) or 0) < (tonumber(b.value) or 0)
			end
			return (tonumber(a.value) or 0) > (tonumber(b.value) or 0)
		end)
		return emptyPages(rows)
	end

	function store:ListKeysAsync(prefix)
		local keys = {}
		for key in pairs(data) do
			if not prefix or prefix == "" or tostring(key):sub(1, #prefix) == prefix then
				table.insert(keys, { KeyName = key })
			end
		end
		return emptyPages(keys)
	end

	function store:OnUpdate() return { Disconnect = function() end } end

	function store:RemoveAsync(key)
		key = tostring(key)
		local old = data[key]
		data[key] = nil
		saveDataStores()
		return old, keyInfo
	end

	function store:GetVersionAsync(key) return data[tostring(key)], keyInfo end
	function store:GetVersionAtTimeAsync(key) return data[tostring(key)], keyInfo end
	function store:ListVersionsAsync() return emptyPages() end
	function store:RemoveVersionAsync() end

	return store
end

local dataStoreMock = {
	GetDataStore = function(_, name, scope)
		local id = tostring(name) .. (scope and ("/" .. tostring(scope)) or "")
		dataStores[id] = dataStores[id] or {}
		return newDataStore(dataStores[id])
	end,
	GetGlobalDataStore = function()
		dataStores.global = dataStores.global or {}
		return newDataStore(dataStores.global)
	end,
	GetRequestBudgetForRequestType = function()
		return math.huge
	end,
	ListDataStoresAsync = function()
		local rows = {}
		for name in pairs(dataStores) do
			table.insert(rows, { DataStoreName = name })
		end
		return emptyPages(rows)
	end,
}
dataStoreMock.GetOrderedDataStore = dataStoreMock.GetDataStore

local messagingTopics = {}
local messagingMock = {
	SubscribeAsync = function(_, topic, callback)
		messagingTopics[topic] = messagingTopics[topic] or {}
		table.insert(messagingTopics[topic], callback)
		return {
			Disconnect = function()
				local index = table.find(messagingTopics[topic], callback)
				if index then
					table.remove(messagingTopics[topic], index)
				end
			end,
		}
	end,
	PublishAsync = function(_, topic, message)
		for _, callback in ipairs(messagingTopics[topic] or {}) do
			task.spawn(callback, { Data = message, Sent = os.time() })
		end
	end,
}

local httpProxy = makeProxy(realGame:GetService("HttpService"), {
	HttpEnabled = true,
	GetSecret = function() return "" end,
	GetAsync = function(_, url, _, headers)
		return executorRequest({ Url = url, Method = "GET", Headers = headers }).Body
	end,
	PostAsync = function(_, url, data, contentType, _, headers)
		local merged = headers or {}
		merged["Content-Type"] = merged["Content-Type"] or (contentType == Enum.HttpContentType.ApplicationUrlEncoded and "application/x-www-form-urlencoded" or "application/json")
		return executorRequest({ Url = url, Method = "POST", Headers = merged, Body = data }).Body
	end,
	RequestAsync = function(_, options)
		local response = executorRequest(options)
		local status = response.StatusCode or response.Status or 0
		return {
			Success = status >= 200 and status < 300,
			StatusCode = status,
			StatusMessage = response.StatusMessage or "",
			Headers = response.Headers or {},
			Body = response.Body,
		}
	end,
})

local textServiceMock = makeProxy(realGame:GetService("TextService"), {
	FilterStringAsync = function(_, text)
		return {
			GetChatForUserAsync = function() return text end,
			GetNonChatStringForBroadcastAsync = function() return text end,
			GetNonChatStringForUserAsync = function() return text end,
		}
	end,
})

local extraServices = (function()
-- Developer products: ProcessReceipt is stored and called with a receipt when a purchase is prompted.
local receiptCallback
local purchaseCounter = 0
local marketplaceMock = makeProxy(realGame:GetService("MarketplaceService"), {
	__set = {
		ProcessReceipt = function(callback)
			receiptCallback = callback
		end,
	},
	ProcessReceipt = nil,
	UserOwnsGamePassAsync = function(_, userId, passId)
		local ok, owns = pcall(function()
			return realGame:GetService("MarketplaceService"):UserOwnsGamePassAsync(userId, passId)
		end)
		return ok and owns or false
	end,
	PlayerOwnsAsset = function(_, player, assetId)
		local ok, owns = pcall(function()
			return realGame:GetService("MarketplaceService"):PlayerOwnsAsset(unwrap(player), assetId)
		end)
		return ok and owns or false
	end,
	PromptProductPurchase = function(_, player, productId)
		purchaseCounter = purchaseCounter + 1
		if receiptCallback then
			task.spawn(receiptCallback, {
				PlayerId = player.UserId,
				PurchaseId = "sse-" .. purchaseCounter,
				ProductId = productId,
				CurrencySpent = 0,
				CurrencyType = Enum.CurrencyType.Robux,
				PlaceIdWherePurchased = game.PlaceId,
			})
		end
		if SSEmu.logHandler then
			SSEmu.logHandler("PromptProductPurchase: " .. tostring(productId))
		end
	end,
})

local badgeMock = makeProxy(realGame:GetService("BadgeService"), {
	AwardBadge = function() return true end,
	UserHasBadgeAsync = function(_, _, badgeId)
		local ok, result = pcall(function()
			return realGame:GetService("BadgeService"):UserHasBadgeAsync(localPlayer.UserId, badgeId)
		end)
		return ok and result or false
	end,
})

---Build an in-memory MemoryStore map, queue or sorted map.
local function newMemoryMap()
	local data = {}
	local map = {}
	function map:GetAsync(key) return data[key] end
	function map:SetAsync(key, value) data[key] = value return true end
	function map:UpdateAsync(key, callback)
		local updated = callback(data[key])
		if updated ~= nil then data[key] = updated end
		return data[key]
	end
	function map:RemoveAsync(key) data[key] = nil end
	function map:GetRangeAsync()
		local rows = {}
		for key, value in pairs(data) do
			table.insert(rows, { key = key, value = value })
		end
		return rows
	end
	-- Queue API.
	local queue = {}
	function map:AddAsync(value) table.insert(queue, value) end
	function map:ReadAsync(count)
		local items = {}
		for _ = 1, math.min(count or 1, #queue) do
			table.insert(items, queue[1])
			table.remove(queue, 1)
		end
		return items, "sse"
	end
	function map:RemoveAsyncId() end
	return map
end

local memoryMaps = {}
local memoryStoreMock = {
	GetSortedMap = function(_, name)
		memoryMaps[name] = memoryMaps[name] or newMemoryMap()
		return memoryMaps[name]
	end,
	GetQueue = function(_, name)
		memoryMaps["q:" .. name] = memoryMaps["q:" .. name] or newMemoryMap()
		return memoryMaps["q:" .. name]
	end,
	GetHashMap = function(_, name)
		memoryMaps["h:" .. name] = memoryMaps["h:" .. name] or newMemoryMap()
		return memoryMaps["h:" .. name]
	end,
}

-- Chat:Chat and PhysicsService calls are server only, they are tried and ignored when the client refuses.
local chatMock = makeProxy(realGame:GetService("Chat"), {
	Chat = function(_, part, message)
		pcall(function()
			realGame:GetService("TextChatService"):DisplayBubble(part, message)
		end)
	end,
	FilterStringAsync = function(_, text) return text end,
	FilterStringForBroadcast = function(_, text) return text end,
})

local physicsOverrides = {}
for _, name in ipairs({ "RegisterCollisionGroup", "CreateCollisionGroup", "CollisionGroupSetCollidable", "SetPartCollisionGroup", "RemoveCollisionGroup", "RenameCollisionGroup" }) do
	physicsOverrides[name] = function(_, ...)
		pcall(realGame:GetService("PhysicsService")[name], realGame:GetService("PhysicsService"), ...)
	end
end
local physicsMock = makeProxy(realGame:GetService("PhysicsService"), physicsOverrides)

-- TeleportService: emulated as no-op so lobby/hub teleports never eject the client.
local teleportMock = makeProxy(realGame:GetService("TeleportService"), {
	Teleport = function() end,
	TeleportToPlaceInstance = function() end,
	TeleportToSpawnByName = function() end,
	TeleportToPrivateServer = function() end,
	TeleportPartyAsync = function() return "sse-reserved" end,
	ReserveServer = function() return "sse-access", "sse-private" end,
	GetPlayerPlaceInstanceAsync = function() return false, "", 0, "" end,
	TeleportAsync = function() return {} end,
	SetTeleportGui = function() end,
	SetTeleportSetting = function() end,
	GetTeleportSetting = function() end,
})

-- GroupService: answered from the real client where possible, empty otherwise.
local groupMock = makeProxy(realGame:GetService("GroupService"), {
	GetGroupsAsync = function(_, userId)
		local ok, res = pcall(function()
			return realGame:GetService("GroupService"):GetGroupsAsync(userId or localPlayer.UserId)
		end)
		return ok and res or {}
	end,
})

-- PolicyService: permissive defaults so gated features stay enabled under emulation.
local policyMock = makeProxy(realGame:GetService("PolicyService"), {
	GetPolicyInfoForPlayerAsync = function()
		return {
			AllowedExternalLinkReferences = {},
			ArePaidRandomItemsRestricted = false,
			IsPaidItemTradingAllowed = true,
			IsSubjectToChinaPolicies = false,
		}
	end,
})

-- SocialService: invite prompts are no-ops, capability checks say yes.
local socialMock = makeProxy(realGame:GetService("SocialService"), {
	PromptGameInvite = function() end,
	CanSendGameInviteAsync = function() return true end,
})

-- AssetService: creation/save calls stubbed so builder scripts don't error client-side.
local assetMock = makeProxy(realGame:GetService("AssetService"), {
	CreatePlaceAsync = function() return 0 end,
	SavePlaceAsync = function() end,
	CreatePlaceInPlayerInventoryAsync = function() return 0 end,
})

-- AnalyticsService: every event call is server only, they are accepted and dropped.
local analyticsOverrides = {}
for _, name in ipairs({
	"FireCustomEvent", "FireEvent", "FireInGameEconomyEvent", "FireLogEvent", "FirePlayerProgressionEvent",
	"LogCustomEvent", "LogEconomyEvent", "LogFunnelStepEvent", "LogOnboardingFunnelStepEvent", "LogProgressionEvent",
}) do
	analyticsOverrides[name] = function() end
end
local okAnalytics, analyticsService = pcall(realGame.GetService, realGame, "AnalyticsService")
local analyticsMock = okAnalytics and analyticsService and makeProxy(analyticsService, analyticsOverrides) or analyticsOverrides

	return {
		AnalyticsService = analyticsMock,
		MarketplaceService = marketplaceMock,
		BadgeService = badgeMock,
		MemoryStoreService = memoryStoreMock,
		Chat = chatMock,
		PhysicsService = physicsMock,
		TeleportService = teleportMock,
		GroupService = groupMock,
		PolicyService = policyMock,
		SocialService = socialMock,
		AssetService = assetMock,
	}
end)()

local serviceMocks = {
	TextService = textServiceMock,
	ServerScriptService = serverScriptService,
	ServerStorage = serverStorage,
	Players = playersProxy,
	RunService = runProxy,
	HttpService = httpProxy,
	DataStoreService = dataStoreMock,
	MessagingService = messagingMock,
}

for name, mock in pairs(extraServices) do
	serviceMocks[name] = mock
end

---Resolve a service name through the mock table first.
local function resolveService(name)
	return serviceMocks[name] or realGame:GetService(name)
end

local gameOverrides = {
	GetService = function(_, name) return resolveService(name) end,
	FindService = function(_, name) return serviceMocks[name] or realGame:FindService(name) end,
}
gameOverrides.getService = gameOverrides.GetService
gameOverrides.BindToClose = function(_, callback)
	table.insert(closeCallbacks, callback)
end
for name, mock in pairs(serviceMocks) do
	gameOverrides[name] = mock
end

mockGame = makeProxy(realGame, gameOverrides)

end

-- ═══════════════════════════════════════════════════════════════════
-- INSTANCE API + TOOL GUI GATING
-- ═══════════════════════════════════════════════════════════════════

---Whether an instance belongs to content started by another client.
---@param inst Instance?
---@return boolean
local function isReplica(inst)
	if not inst then
		return false
	end
	local ok, value = pcall(function()
		return inst:GetAttribute(REPLICA_ATTRIBUTE)
	end)
	return ok and value == true
end

---Keep a GUI hidden on replicated clients.
---@param gui Instance
local function lockReplicaGui(gui)
	pcall(function()
		gui:SetAttribute(REPLICA_ATTRIBUTE, true)
		gui.Enabled = false
		gui:GetPropertyChangedSignal("Enabled"):Connect(function()
			if gui.Enabled then
				gui.Enabled = false
			end
		end)
	end)
end

-- One shared entry per tool, so a tool that creates many GUIs does not stack event handlers.
local toolGuis = {}

---Only show a tool's GUI while the tool is equipped.
---@param gui Instance
---@param scriptObject Instance
local function bindToolGui(gui, scriptObject)
	local tool = scriptObject and scriptObject:FindFirstAncestorWhichIsA("Tool")
	if not tool then
		return
	end

	local entry = toolGuis[tool]
	if not entry then
		entry = { guis = setmetatable({}, { __mode = "k" }), pending = false }
		toolGuis[tool] = entry

		-- Updates are deferred so the tool events never nest inside each other.
		entry.refresh = function()
			if entry.pending then
				return
			end
			entry.pending = true
			task.defer(function()
				entry.pending = false
				local equipped = tool.Parent ~= nil and tool.Parent == localPlayer.Character
				for guiObject in pairs(entry.guis) do
					pcall(function()
						guiObject.Enabled = equipped
					end)
				end
			end)
		end

		track(tool.Equipped:Connect(entry.refresh))
		track(tool.Unequipped:Connect(entry.refresh))
	end

	entry.guis[gui] = true
	entry.refresh()
end

---Build an Instance replacement bound to the script that uses it.
---@param scriptObject Instance
local function makeInstanceApi(scriptObject)
	local api = setmetatable({}, { __index = realInstance })

	api.new = function(className, parent)
		local created
		if REMOTE_CLASSES[className] then
			created = createMockRemote(className)
		else
			created = realInstance.new(className)
		end

		pcall(created.SetAttribute, created, SOURCE_TAG, true)
		-- Content made by a script of a dispatched asset inherits that asset's origin, so the mirror
		-- knows every client already builds the same thing locally.
		local okInherit, inherited = pcall(function()
			return scriptObject and scriptObject:GetAttribute(ORIGIN_ATTRIBUTE)
		end)
		pcall(created.SetAttribute, created, ORIGIN_ATTRIBUTE,
			(okInherit and type(inherited) == "string") and inherited or getOrigin(scriptObject))
		if GUI_CLASSES[className] then
			pcall(created.SetAttribute, created, "_sse_seq", nextGuiSeq())
			if className == "ScreenGui" then
				pcall(function() created.ResetOnSpawn = false end)
			end
			bindToolGui(created, scriptObject)
			if isReplica(scriptObject) then
				lockReplicaGui(created)
			end
		end
		if parent ~= nil then
			created.Parent = unwrap(parent)
		end
		return created
	end

	return api
end

-- ═══════════════════════════════════════════════════════════════════
-- COMPILING + SANDBOX ENVIRONMENT
-- ═══════════════════════════════════════════════════════════════════

---Whether text contains anything besides comments and blank space. A decompiler that finds no bytecode
---answers with a comment ("-- no script bytecode found"), which must not be run as the script.
---@param text string
---@return boolean
function SSEmu.hasCode(text)
	local stripped = text:gsub("%-%-%[(=*)%[.-%]%1%]", ""):gsub("%-%-[^\n]*", "")
	return stripped:match("%S") ~= nil
end

---A bare copy of a script under a plain name inside the game tree. Some executors cannot reach the code
---of a script whose path has unreadable characters or that sits outside the tree; the copy has neither
---problem. Made once per script and kept, the closure taken from it may need it alive.
---@param inst Instance
---@return Instance?
function SSEmu.cleanCopy(inst)
	SSEmu.cleanCopies = SSEmu.cleanCopies or {}
	local existing = SSEmu.cleanCopies[inst]
	if existing ~= nil then
		return existing or nil
	end
	local ok, copy = pcall(function()
		local wasArchivable = inst.Archivable
		inst.Archivable = true
		local clone = inst:Clone()
		inst.Archivable = wasArchivable
		clone:ClearAllChildren()
		clone.Name = "Module"
		if not SSEmu.compileHolder then
			SSEmu.compileHolder = create("Folder", { Name = "Compiled" }, serverRoot)
		end
		clone.Parent = SSEmu.compileHolder
		return clone
	end)
	SSEmu.cleanCopies[inst] = ok and copy or false
	return ok and copy or nil
end

---Read source through Source, then the decompiler.
---@param inst Instance
---@return string?
local function readSource(inst)
	if sourceOverrides[inst] ~= nil then
		return sourceOverrides[inst]
	end
	local ok, source = pcall(function() return inst.Source end)
	if ok and type(source) == "string" and source ~= "" then
		return source
	end
	if decompile then
		local decompiled, result = pcall(decompile, inst)
		if decompiled and type(result) == "string" and SSEmu.hasCode(result) then
			return result
		end
	end
	return nil
end

---Return one line of a script's source.
---@param inst Instance
---@param lineNumber number
---@return string?
function SSEmu.sourceLine(inst, lineNumber)
	-- Decompiling is slow, each script is read once for error reports.
	local source = SSEmu.sourceCache[inst]
	if source == nil then
		source = readSource(inst) or false
		SSEmu.sourceCache[inst] = source
	end
	if not source then
		return nil
	end
	local current = 0
	for line in (source .. "\n"):gmatch("(.-)\r?\n") do
		current = current + 1
		if current == lineNumber then
			return (line:gsub("^%s+", ""))
		end
	end
	return nil
end

-- Scripts already resolved by SSEmu.findScript, so an error loop does not rescan the tree.
local scriptPathCache = setmetatable({}, { __mode = "v" })

---Find an emulated script by the full name an error message carries.
---@param path string
---@return Instance?
function SSEmu.findScript(path)
	local cached = scriptPathCache[path]
	if type(cached) == "number" then
		-- A miss is remembered for a while so the same unknown path is not searched again and again.
		if os.clock() - cached < 30 then
			return nil
		end
	elseif cached then
		return cached
	end

	-- Scripts of tools and GUIs live in the game tree, their path resolves directly.
	local current = realGame
	for segment in path:gmatch("[^%.]+") do
		current = current and current:FindFirstChild(segment)
	end
	if current and current ~= realGame and current:IsA("LuaSourceContainer") then
		scriptPathCache[path] = current
		return current
	end

	for _, node in ipairs(serverRoot:GetDescendants()) do
		if node:IsA("LuaSourceContainer") and node:GetFullName() == path then
			scriptPathCache[path] = node
			return node
		end
	end
	scriptPathCache[path] = os.clock()
	return nil
end

---Turn a script instance into a function, preferring real bytecode.
---@param inst Instance
---@param isClient boolean
---@return function?
local function compileInstance(inst, isClient)
	local func

	if getscriptclosure and sourceOverrides[inst] == nil then
		local ok, closure = pcall(getscriptclosure, inst)
		if ok and type(closure) == "function" then
			func = closure
		end
	end

	-- Other names executors give the same thing, then the same attempts on a clean copy of the script.
	if not func and sourceOverrides[inst] == nil then
		local getters = {}
		if getscriptclosure then table.insert(getters, getscriptclosure) end
		if getscriptfunction then table.insert(getters, getscriptfunction) end
		if type(debug.loadmodule) == "function" and inst:IsA("ModuleScript") then table.insert(getters, debug.loadmodule) end
		if loadmodule and inst:IsA("ModuleScript") then table.insert(getters, loadmodule) end

		for index, getter in ipairs(getters) do
			if index > 1 then
				local ok, closure = pcall(getter, inst)
				if ok and type(closure) == "function" then
					func = closure
					break
				end
			end
		end
		if not func and not readSource(inst) then
			local copy = SSEmu.cleanCopy(inst)
			if copy then
				for _, getter in ipairs(getters) do
					local ok, closure = pcall(getter, copy)
					if ok and type(closure) == "function" then
						func = closure
						break
					end
				end
				if not func then
					local source = readSource(copy)
					if source then
						func = realLoadstring(source, "=" .. inst:GetFullName())
					end
				end
				if func then
					log("Reached the code of " .. inst.Name .. " through a clean copy", INFO_COLOR)
				end
			end
		end
	end

	if not func then
		local source = readSource(inst)
		if source then
			local compiled, err = realLoadstring(source, "=" .. inst:GetFullName())
			if compiled then
				func = compiled
			else
				log("Compile failed: " .. inst.Name .. " - " .. tostring(err), ERROR_COLOR)
			end
		end
	end

	if func then
		infect(func, inst, isClient)
	end
	return func
end

---Build the environment a sandboxed script sees.
---@param scriptObject Instance
---@param isClient boolean
buildEnv = function(scriptObject, isClient)
	local sandboxGame = isClient and realGame or mockGame

	local env = {
		script = scriptObject,
		owner = contextOwners[scriptObject] or localPlayer,
		game = sandboxGame,
		Game = sandboxGame,
		Instance = makeInstanceApi(scriptObject),
		typeof = sandboxTypeof,
		require = function(target)
			return smartRequire(target, scriptObject, isClient)
		end,
		print = function(...)
			print(...)
			log(joinArgs(...))
		end,
		warn = function(...)
			warn(...)
			log(joinArgs(...), WARN_COLOR)
		end,
		loadstring = function(source, chunkName)
			-- babyboo calling convention: loadstring({ Contents = ..., RunContext = ..., Player = ... })
			if type(source) == "table" then
				return SSEmu.babyboo(source)
			end
			local func, err = realLoadstring(source, chunkName)
			if func then
				infect(func, scriptObject, isClient)
			end
			return func, err
		end,
		LoadLibrary = function(name)
			return SSEmu.loadLibrary(name)
		end,
		NS = function(source, parent)
			return spawnSource(source, parent, false, isReplica(scriptObject))
		end,
		NLS = function(source, parent)
			return spawnSource(source, parent, true, isReplica(scriptObject))
		end,
	}

	-- getfenv(0) is the environment of the running script on Roblox. Modules that keep their API in
	-- globals and end with "return getfenv(0)" (F3X Core does) must get this sandbox table, not the
	-- executor's thread environment where none of those globals live.
	local realGetfenv, realSetfenv = getfenv, setfenv
	env.getfenv = function(target)
		if target == 0 then
			return env
		end
		if target == nil then
			target = 1
		end
		if type(target) == "number" then
			return realGetfenv(target + 1)
		end
		return realGetfenv(target)
	end
	env.setfenv = function(target, newEnv)
		if target == 0 then
			return
		end
		if type(target) == "number" then
			return realSetfenv(target + 1, newEnv)
		end
		return realSetfenv(target, newEnv)
	end

	-- Everything else resolves through the executor, then the Roblox environment.
	return setmetatable(env, {
		__index = function(_, key)
			local value = genv[key]
			if value ~= nil then
				return value
			end
			return renv[key]
		end,
	})
end

---Force a function to run inside the sandbox.
---@param func function
---@param scriptObject Instance
---@param isClient boolean
---@return function
infect = function(func, scriptObject, isClient)
	if type(func) ~= "function" then
		return func
	end
	contexts[scriptObject] = isClient
	local ok, err = pcall(setfenv, func, buildEnv(scriptObject, isClient))
	if not ok then
		log("setfenv failed: " .. tostring(err), WARN_COLOR)
	end
	return func
end

-- ═══════════════════════════════════════════════════════════════════
-- SCRIPTS, TOOLS, ASSETS, REQUIRE
-- ═══════════════════════════════════════════════════════════════════

---Run a sandboxed function on its own thread once the character exists.
---@param func function
---@param inst Instance?
local function runSandboxed(func, inst)
	task.spawn(function()
		local deadline = os.clock() + 5
		while not localPlayer.Character and os.clock() < deadline do
			task.wait(0.1)
		end
		xpcall(func, makeErrorHandler(inst))
	end)
end

---Run source in a fresh Script or LocalScript object.
---@param source string
---@param parent Instance?
---@param isClient boolean
---@param replica boolean?
---@return Instance
spawnSource = function(source, parent, isClient, replica)
	local container = realInstance.new(isClient and "LocalScript" or "Script")
	container.Name = isClient and "NLS" or "NS"
	container.Disabled = true
	if replica then
		container:SetAttribute(REPLICA_ATTRIBUTE, true)
	end
	container.Parent = unwrap(parent) or serverScriptService

	local func, err = realLoadstring(source, "=" .. container.Name)
	if not func then
		log("Error: " .. tostring(err), ERROR_COLOR)
		return container
	end

	infect(func, container, isClient)
	started[container] = true
	runSandboxed(func, container)
	return container
end

---Whether the engine would run a script where it currently sits: LocalScripts under our player or
---character, server Scripts there too and anywhere in Workspace or the emulated ServerScriptService.
---A script that was removed again before its turn (parent nil) or sits in storage does not run.
---@param inst Instance
---@return boolean
function SSEmu.isRunnablePlace(inst)
	local ok, runnable = pcall(function()
		local character = localPlayer.Character
		if inst:IsDescendantOf(localPlayer) or (character and inst:IsDescendantOf(character)) then
			return true
		end
		if inst:IsA("LocalScript") then
			return false
		end
		return inst:IsDescendantOf(workspaceService) or inst:IsDescendantOf(serverScriptService)
	end)
	return ok and runnable == true
end

---True while a script must not start yet: it shipped disabled and nothing has enabled it so far,
---exactly like the engine treats it. The first call also listens for the enable and starts it then.
---@param inst Instance
---@return boolean
function SSEmu.waitsForEnable(inst)
	local okAttr, wasDisabled = pcall(function() return inst:GetAttribute(WAS_DISABLED_ATTRIBUTE) end)
	if not okAttr or wasDisabled ~= true or SSEmu.enabledScripts[inst] then
		return false
	end

	-- Every script of an asset is switched off on load, so one that reads enabled was enabled by the hub.
	local okState, disabled = pcall(function() return inst.Disabled end)
	if okState and disabled == false then
		SSEmu.enabledScripts[inst] = true
		pcall(function() inst.Disabled = true end)
		return false
	end

	if not SSEmu.armedScripts[inst] then
		SSEmu.armedScripts[inst] = true
		for _, property in ipairs({ "Disabled", "Enabled" }) do
			pcall(function()
				track(inst:GetPropertyChangedSignal(property):Connect(function()
					if started[inst] or SSEmu.enabledScripts[inst] then
						return
					end
					local okNow, nowDisabled = pcall(function() return inst.Disabled end)
					if okNow and nowDisabled == false then
						SSEmu.enabledScripts[inst] = true
						-- Our copy runs instead of the engine's, the instance itself goes back to off.
						pcall(function() inst.Disabled = true end)
						task.defer(runScript, inst)
					end
				end))
			end)
		end
	end
	return true
end

---Run one Script or LocalScript instance once.
---@param inst Instance
runScript = function(inst, force)
	if started[inst] then
		return
	end
	-- Scripts only start where the engine would start them. Explicit commands (.load, .give, convert of
	-- a model) pass force and run their scripts in place.
	if not force and config.runAnywhere ~= true and not SSEmu.isRunnablePlace(inst) then
		return
	end
	-- shared.SSEmuConfig.runDisabled = true brings back the old "run everything" behaviour.
	if config.runDisabled ~= true and SSEmu.waitsForEnable(inst) then
		return
	end
	started[inst] = true

	-- Guard against clone loops that would start scripts endlessly and crash the game.
	local now = os.clock()
	if now - startWindow > 1 then
		startWindow, startCount = now, 0
	end
	startCount = startCount + 1

	local isClient = inst:IsA("LocalScript")
	local ok, runContext = pcall(function() return inst.RunContext end)
	if ok and runContext == Enum.RunContext.Client then
		isClient = true
	end

	local func = compileInstance(inst, isClient)
	if not func then
		return log("No source or bytecode: " .. inst:GetFullName(), WARN_COLOR)
	end

	runSandboxed(func, inst)
end

---Run every non-module script under a root.
---@param root Instance
runDescendantScripts = function(root, force)
	local nodes = root:GetDescendants()
	table.insert(nodes, 1, root)
	for _, node in ipairs(nodes) do
		if node:IsA("BaseScript") then
			runScript(node, force)
		end
	end
end

---Require through the native loader with a low identity to avoid env leaks.
local function nativeRequireSafe(target)
	local previous = getthreadidentity and getthreadidentity() or 8
	if setthreadidentity then
		setthreadidentity(2)
	end
	local ok, result = pcall(nativeRequire, target)
	if setthreadidentity then
		setthreadidentity(previous)
	end
	return ok, result
end

---Mark a cache key as loading by the current thread.
---@param key any
local function beginLoading(key)
	moduleCache[key] = { loading = true, thread = coroutine.running(), waiters = {} }
end

---Store the result of a load and wake every thread that waited on it.
---@param key any
---@param success boolean
---@param value any
local function finishLoading(key, success, value, keepFailure)
	local entry = moduleCache[key]
	-- A failed module stays failed, like on Roblox. Loading it again on every require (a hub asking for
	-- its broken core each frame) is pure lag. Asset downloads are not kept, they may work next time.
	moduleCache[key] = success and { value = value } or (keepFailure and { failed = true } or nil)

	if entry and entry.loading then
		for _, resume in ipairs(entry.waiters) do
			resume()
		end
	end
end

---Wait for a module that another thread is loading. Returns handled, value.
---The same thread asking again is a real circular require, anything else waits like the engine does.
---@param key any
---@param label string
---@return boolean, any
local function awaitLoading(key, label)
	local entry = moduleCache[key]
	if not (entry and entry.loading) then
		return false
	end

	local thread = coroutine.running()
	if entry.thread == thread then
		log("Recursive require: " .. label, WARN_COLOR)
		return true, nil
	end

	-- Poll until the module finishes loading. Large dependency trees (hundreds of modules) legitimately
	-- take a long time, so we only give up when the loader thread has died or the hard deadline passes.
	local deadline = os.clock() + MODULE_WAIT_TIMEOUT
	while true do
		local done = moduleCache[key]
		if done and not done.loading then
			return true, done.value
		end
		if entry.thread and coroutine.status(entry.thread) == "dead" and moduleCache[key] == entry then
			log("Require aborted (loader died): " .. label, WARN_COLOR)
			return true, nil
		end
		if os.clock() >= deadline then
			log("Require timed out: " .. label, WARN_COLOR)
			return true, nil
		end
		task.wait(0.1)
	end
end

---Load and cache a ModuleScript inside the sandbox.
---@param moduleScript Instance
---@param isClient boolean
requireModule = function(moduleScript, isClient)
	-- A module required by a LocalScript and by a server Script is two separate copies on Roblox (two
	-- VMs). Sharing one copy hands the client a module that was set up with the server environment.
	local cacheKey = moduleScript
	if isClient then
		cacheKey = SSEmu.clientModuleKeys[moduleScript]
		if not cacheKey then
			cacheKey = {}
			SSEmu.clientModuleKeys[moduleScript] = cacheKey
		end
	end

	local handled, waited = awaitLoading(cacheKey, moduleScript.Name)
	if handled then
		return waited
	end

	local cached = moduleCache[cacheKey]
	if cached then
		return cached.value
	end

	beginLoading(cacheKey)
	local func = compileInstance(moduleScript, isClient)
	if not func then
		-- No bytecode and no source the executor can read: the engine's own require is the last resort.
		-- It runs the module outside the server sandbox, so server-only calls inside it will fail.
		local ok, result = nativeRequireSafe(moduleScript)
		finishLoading(cacheKey, ok, result, true)
		if ok then
			log("No readable code for " .. moduleScript:GetFullName() .. ", loaded by the engine without the server sandbox", WARN_COLOR)
			return result
		end
		log("No readable code for " .. moduleScript:GetFullName() .. " and the engine refused it: " .. tostring(result), ERROR_COLOR)
		log("Module failed: " .. moduleScript:GetFullName(), ERROR_COLOR)
		return nil
	end

	local results = table.pack(xpcall(func, onScriptError))
	if not results[1] then
		finishLoading(cacheKey, false, nil, true)
		return nil
	end

	finishLoading(cacheKey, true, results[2])
	return results[2]
end

---Download an asset as loose instances, retrying because asset downloads fail transiently.
---@param assetId number
---@param attempts number?
---@return table?
local function fetchObjects(assetId, attempts)
	local thread = coroutine.running()
	for attempt = 1, attempts or 1 do
		local ok, objects = pcall(function()
			return realGame:GetObjects("rbxassetid://" .. assetId)
		end)
		if ok and type(objects) == "table" and #objects > 0 then
			return objects
		end

		-- The real LoadAsset is tried here, the emulated one would call straight back into this function.
		SSEmu.rawInsert[thread] = true
		local loaded, model = pcall(function()
			return insertService:LoadAsset(assetId)
		end)
		SSEmu.rawInsert[thread] = nil
		if attempt == (attempts or 1) then
			log("Asset " .. tostring(assetId) .. " download failed. GetObjects: "
				.. (ok and "returned nothing" or tostring(objects))
				.. " | LoadAsset: " .. (loaded and "returned nothing" or tostring(model)), WARN_COLOR)
		end
		if loaded and model then
			local children = model:GetChildren()
			for _, child in ipairs(children) do
				child.Parent = nil
			end
			model:Destroy()
			if #children > 0 then
				return children
			end
		end

		-- Last resort: download the model file itself and load it as a custom asset.
		if attempt == (attempts or 1) and writefile and getcustomasset then
			local okFile, fromFile = pcall(function()
				local response = executorRequest({ Url = "https://assetdelivery.roblox.com/v1/asset/?id=" .. assetId, Method = "GET" })
				local status = response.StatusCode or response.Status
				if status ~= 200 or type(response.Body) ~= "string" or #response.Body < 16 then
					return nil
				end
				local path = "ezproxy_asset_" .. assetId .. ".rbxm"
				writefile(path, response.Body)
				local loaded = realGame:GetObjects(getcustomasset(path))
				if delfile then
					pcall(delfile, path)
				end
				return loaded
			end)
			if okFile and type(fromFile) == "table" and #fromFile > 0 then
				return fromFile
			end
		end
		if attempt < (attempts or 1) then
			task.wait(1)
		end
	end
	return nil
end

---Disable stock scripts, tag instances and swap remotes before use.
---@param root Instance
---@param replica boolean?
---@param origin string?
---Every node under a root with its structural address: "<rootKey>/<name>/<name~2>/...". The same
---asset downloaded on another client gives the same addresses, that is how a copy is found there.
---@param root Instance
---@param rootKey string
---@return table { {node, key}, ... }
function SSEmu.keyTree(root, rootKey)
	local list = {}
	local function walk(node, key)
		table.insert(list, { node, key })
		local okKids, kids = pcall(function() return node:GetChildren() end)
		if not okKids then
			return
		end
		local counts = {}
		for _, child in ipairs(kids) do
			local name = child.Name
			counts[name] = (counts[name] or 0) + 1
			walk(child, key .. "/" .. (counts[name] > 1 and (name .. "~" .. counts[name]) or name))
		end
	end
	walk(root, rootKey)
	return list
end

---Source of an asset origin for the exact copy: "a:<assetId>" (downloadable) or "p:<path>" (an
---instance of the game itself, every client has it). nil when the content has no shared source.
---@param origin string?
---@return string?
function SSEmu.sourceOf(origin)
	if type(origin) ~= "string" then
		return nil
	end
	local plain = origin:gsub("^dispatch:", "")
	local kind, rest = plain:match("^(%a+):(.+)$")
	if not kind then
		return nil
	end
	if rest:match("^%d+$") then
		return "a:" .. rest
	end
	if kind == "convert" then
		return "p:" .. rest
	end
	return nil
end

local function prepareAsset(root, replica, origin, rootIndex)
	-- Exact copy addresses, stamped on the untouched tree (before remotes are swapped): clones the
	-- hub makes later carry them, so the other clients can clone the very same source piece.
	local source = SSEmu.sourceOf(origin)
	if source then
		local okStamped, stamped = pcall(function() return root:GetAttribute("_sse_key") end)
		if not (okStamped and stamped) then
			for _, pair in ipairs(SSEmu.keyTree(root, tostring(rootIndex or 1))) do
				pcall(pair[1].SetAttribute, pair[1], "_sse_src", source)
				pcall(pair[1].SetAttribute, pair[1], "_sse_key", pair[2])
			end
		end
	end
	-- An asset loaded by a command the proxy broadcast to every client: each client builds its own
	-- copy, the mirror must not send it again (see isDispatchedContent).
	if origin and SSEmu.dispatchThreads[coroutine.running()] then
		origin = "dispatch:" .. origin
	end
	convertRemotes(root)
	local nodes = root:GetDescendants()
	table.insert(nodes, 1, root)
	for _, node in ipairs(nodes) do
		pcall(function()
			if node:IsA("BaseScript") then
				if node:GetAttribute(WAS_DISABLED_ATTRIBUTE) == nil then
					node:SetAttribute(WAS_DISABLED_ATTRIBUTE, node.Disabled)
				end
				node.Disabled = true
			end
			node:SetAttribute(SOURCE_TAG, true)
			if origin then
				node:SetAttribute(ORIGIN_ATTRIBUTE, origin)
			end
			if node:IsA("LayerCollector") then
				node:SetAttribute("_sse_seq", nextGuiSeq())
				if node:IsA("ScreenGui") then
					node.ResetOnSpawn = false
				end
			end
			if replica then
				node:SetAttribute(REPLICA_ATTRIBUTE, true)
				if node:IsA("LayerCollector") then
					lockReplicaGui(node)
				end
			end
		end)
	end
end

-- InsertService:LoadAsset is server only, sandbox calls download the way require(id) does and get
-- the usual Model wrapper. Scripts inside start when the caller parents them somewhere live.
do
	local function loadAssetModel(assetId)
		local id = tonumber(assetId)
		local objects = id and fetchObjects(id, 2)
		if not objects then
			error("InsertService: asset " .. tostring(assetId) .. " could not be loaded", 3)
		end
		local model = realInstance.new("Model")
		pcall(model.SetAttribute, model, SOURCE_TAG, true)
		for index, root in ipairs(objects) do
			prepareAsset(root, false, "insert:" .. id, index)
			root.Parent = model
		end
		return model
	end

	-- No proxy on purpose: executors implement game:GetObjects on top of the real InsertService and
	-- must keep getting it from GetService. The namecall hook routes sandbox LoadAsset calls here.
	SSEmu.insertAsset = loadAssetModel
end

---LoadLibrary was removed from Roblox, old scripts still call it for RbxUtility.Create.
---@param name string
---@return table
function SSEmu.loadLibrary(name)
	if name ~= "RbxUtility" then
		return {}
	end

	-- Create "Class" { Property = value, child, [Create.E "Event"] = handler, [Create] = constructor }
	local Create = {}
	setmetatable(Create, {
		__call = function(_, className)
			return function(properties)
				local object = realInstance.new(className)
				pcall(object.SetAttribute, object, SOURCE_TAG, true)
				local parent, constructor
				for key, value in pairs(properties or {}) do
					if type(key) == "number" then
						unwrap(value).Parent = object
					elseif key == "Parent" then
						parent = value
					elseif key == Create then
						constructor = value
					elseif type(key) == "table" and key.__eventname then
						object[key.__eventname]:Connect(value)
					else
						object[key] = value
					end
				end
				if constructor then
					constructor(object)
				end
				if parent then
					object.Parent = unwrap(parent)
				end
				return object
			end
		end,
	})
	Create.E = function(eventName)
		return { __eventname = eventName }
	end

	return {
		Create = Create,
		-- Signal object with the lowercase methods the library had: connect, fire, wait, disconnect.
		CreateSignal = function()
			local signal = newSignal()
			local live = {}
			local object = {}
			function object:connect(callback)
				if type(callback) ~= "function" then
					error("connect(" .. tostring(callback) .. ")", 2)
				end
				local connection = signal:Connect(callback)
				table.insert(live, connection)
				return connection
			end
			function object:disconnect()
				for _, connection in ipairs(live) do
					connection:Disconnect()
				end
				table.clear(live)
			end
			function object:wait()
				return signal:Wait()
			end
			function object:fire(...)
				signal:Fire(...)
			end
			object.Connect, object.Disconnect, object.Wait, object.Fire = object.connect, object.disconnect, object.wait, object.fire
			return object
		end,
	}
end

---Pick the module that require(assetId) should return.
local function findMainModule(objects)
	for _, root in ipairs(objects) do
		if root:IsA("ModuleScript") then
			return root
		end
	end
	for _, root in ipairs(objects) do
		if not root:IsA("Tool") then
			local named = root:FindFirstChild("MainModule", true)
			if named and named:IsA("ModuleScript") then
				return named
			end
		end
	end
	for _, root in ipairs(objects) do
		if not root:IsA("Tool") then
			for _, node in ipairs(root:GetDescendants()) do
				if node:IsA("ModuleScript") then
					return node
				end
			end
		end
	end
	return nil
end

---Put a tool in the Backpack and start its scripts.
---@param tool Instance
giveTool = function(tool)
	local backpack = localPlayer:FindFirstChildOfClass("Backpack") or localPlayer:WaitForChild("Backpack", 5)
	if not backpack then
		return log("No Backpack found.", WARN_COLOR)
	end
	tool.Parent = backpack
	runDescendantScripts(tool)
end

-- ═══════════════════════════════════════════════════════════════════
-- BABYBOO, REVERSED: the original lets client code run on a server,
-- this one runs server code on the client inside the emulated server.
-- ═══════════════════════════════════════════════════════════════════

local BABYBOO_ASSET_ID = 135879132527047

---Compile Contents into the environment of the requested RunContext.
---Client runs with the real game, Server and Legacy run with the emulated server.
---@param config table
---@return function?, string?, Instance?
local function babybooCompile(config)
	local contents = tostring(config.Contents or config.Source or "print(\"Hello World!\")")
	local isClient = config.RunContext == Enum.RunContext.Client

	local container = create(isClient and "LocalScript" or "Script", { Name = "Babyboo", Disabled = true }, serverScriptService)
	local owner = config.Player
	if realTypeof(owner) == "Instance" and owner:IsA("Player") then
		contextOwners[container] = owner
	end

	local func, err = realLoadstring(contents, "=" .. container.Name)
	if not func then
		container:Destroy()
		return nil, err
	end

	infect(func, container, isClient)
	if type(config.Environment) == "table" then
		local env = getfenv(func)
		for key, value in pairs(config.Environment) do
			if env[key] ~= value and env ~= value then
				env[key] = value
			end
		end
	end

	started[container] = true
	return func, nil, container
end

-- Callable like the original module: babyboo(config)(...) or babyboo("source")().
local babyboo = {}

---Same entry the original convert Script uses.
---@param contents string
---@param player Player?
function babyboo.AAA(contents, player)
	local func, _, container = babybooCompile({ Contents = contents, Player = player, RunContext = Enum.RunContext.Server })
	if func then
		task.spawn(xpcall, func, makeErrorHandler(container))
	end
end

setmetatable(babyboo, {
	__call = function(_, config)
		if type(config) == "string" then
			config = { Contents = config }
		end
		if type(config) ~= "table" then
			return nil
		end

		local func, err, container = babybooCompile(config)
		if not func then
			log("Babyboo compile failed: " .. tostring(err), ERROR_COLOR)
			return nil, err
		end
		return function(...)
			local results = table.pack(xpcall(func, makeErrorHandler(container), ...))
			if results[1] then
				return table.unpack(results, 2, results.n)
			end
		end
	end,
})

SSEmu.babyboo = babyboo

---require(assetId) like Roblox: only the MainModule runs, the rest of the model never auto-runs.
---@param assetId number
---@param replica boolean?
---@return any
loadAsset = function(assetId, replica)
	-- The server side executor module is replaced by the reversed emulation.
	if assetId == BABYBOO_ASSET_ID then
		log("require(" .. assetId .. ") -> emulated babyboo", INFO_COLOR)
		return babyboo
	end

	local key = "asset:" .. assetId
	local handled, waited = awaitLoading(key, tostring(assetId))
	if handled then
		return waited
	end

	local cached = moduleCache[key]
	if cached then
		return cached.value
	end

	beginLoading(key)
	local objects = fetchObjects(assetId, 2)
	if not objects then
		finishLoading(key, false)
		error("Attempted to call require with invalid argument(s).", 2)
	end

	for index, root in ipairs(objects) do
		prepareAsset(root, replica, key, index)
		root.Parent = moduleHolder
	end

	local main = findMainModule(objects)
	if not main then
		-- Not a module asset: a server would refuse it, here it is started as the model it is.
		log("require(" .. assetId .. "): no ModuleScript in the asset, running it as a model", WARN_COLOR)
		for _, root in ipairs(objects) do
			if root:IsA("Tool") then
				giveTool(root)
			else
				runDescendantScripts(root, true)
			end
		end
		finishLoading(key, true, nil)
		return nil
	end

	local value = requireModule(main, false)
	finishLoading(key, true, value)
	return value
end

---Give an asset to the player the way gear works: tools go to the Backpack and their scripts start.
---@param assetId number
---@param replica boolean?
giveAsset = function(assetId, replica)
	local objects = fetchObjects(assetId)
	if not objects then
		return log("Could not load asset " .. assetId, ERROR_COLOR)
	end

	for index, root in ipairs(objects) do
		prepareAsset(root, replica, "give:" .. assetId, index)
		if root:IsA("Tool") then
			giveTool(root)
		else
			root.Parent = moduleHolder
			runDescendantScripts(root, true)
		end
	end
end

---Find a module by path or name near the caller.
local function findModuleByName(path, caller)
	local name = path:match("([^/]+)$")
	if not name then
		return nil
	end
	if caller then
		local found = caller:FindFirstChild(name) or (caller.Parent and caller.Parent:FindFirstChild(name))
		if found and found:IsA("ModuleScript") then
			return found
		end
	end
	for _, root in ipairs({ serverRoot, moduleHolder }) do
		for _, node in ipairs(root:GetDescendants()) do
			if node.Name == name and node:IsA("ModuleScript") then
				return node
			end
		end
	end
	return nil
end

---Sandbox replacement for require.
---@param target any
---@param caller Instance?
---@return any
smartRequire = function(target, caller, callerIsClient)
	-- The side comes from the environment that called require; a module shared by both sides has no
	-- single side of its own.
	if callerIsClient == nil then
		callerIsClient = caller ~= nil and contexts[caller] == true
	end

	-- Report every require to the proxy console.
	if SSEmu.onRequire then
		pcall(SSEmu.onRequire, target, caller)
	end

	if typeof(target) == "Instance" then
		if target:IsA("ModuleScript") then
			return requireModule(target, callerIsClient)
		end
		return error("Attempted to call require with invalid argument(s).", 2)
	end

	local assetId = tonumber(target)
	if not assetId and type(target) == "string" then
		assetId = tonumber(target:match("^rbxassetid://(%d+)$") or target:match("^%s*(%d+)%s*$"))
	end
	if assetId then
		return loadAsset(assetId, isReplica(caller))
	end

	if type(target) == "string" then
		local module = findModuleByName(target, caller)
		if module then
			return requireModule(module, callerIsClient)
		end
	end

	local ok, result = nativeRequireSafe(target)
	if ok then
		return result
	end
	log("Could not resolve module: " .. tostring(target), ERROR_COLOR)
	return nil
end

-- ═══════════════════════════════════════════════════════════════════
-- WATCHERS: StarterGui, StarterPack, PlayerGui, Backpack, Character
-- ═══════════════════════════════════════════════════════════════════

-- Block scoped: Luau allows 200 locals per function, only the names used later stay outside.
local setupKillHandler, setupToolDrops, setupSeats, startServerEvents, setupWatchers
do
---True when an instance lives inside the emulated server/module tree rather than on screen.
---@param inst Instance
---@return boolean
local function isUnderModuleTree(inst)
	local ok, under = pcall(function()
		return inst:IsDescendantOf(serverRoot) or inst:IsDescendantOf(moduleHolder)
	end)
	return ok and under == true
end

---Identity signature of a GUI: its class, name and immediate children. A fresh clone matches its
---template exactly, so this pairs a shown copy with the template it came from.
---@param gui Instance
---@return string
local function fullGuiSignature(gui)
	local parts = { gui.ClassName, gui.Name }
	local ok, children = pcall(function() return gui:GetChildren() end)
	if ok then
		local names = {}
		for _, child in ipairs(children) do
			table.insert(names, child.ClassName .. ":" .. child.Name)
		end
		table.sort(names)
		for _, name in ipairs(names) do
			table.insert(parts, name)
		end
	end
	return table.concat(parts, "|")
end

---When a real GUI copy is shown outside the module tree (PlayerGui, CoreGui, gethui), hide every
---same-named template still sitting inside the emulated server tree (Re2lua) so it stops rendering as
---a ghost duplicate. Matched by NAME, so it catches a copy whose children differ from the template.
---Only disabled, never destroyed, and ONLY templates inside the server tree are touched -- real GUIs
---outside it (including legitimate same-named windows) are never affected.
---@param copy Instance
local function hideTemplateTwin(copy)
	if not (copy:IsA("ScreenGui") and copy:GetAttribute(SOURCE_TAG)) then
		return
	end
	if isUnderModuleTree(copy) then
		return
	end
	local name = copy.Name
	for _, node in ipairs(serverRoot:GetDescendants()) do
		if node ~= copy and node:IsA("ScreenGui") and node.Name == name and node.Enabled
			and node:GetAttribute(SOURCE_TAG) then
			pcall(function() node.Enabled = false end)
			log("Hid duplicate template GUI: " .. node.Name, WARN_COLOR)
		end
	end
end

---Start scripts of emulated instances that get parented into a container.
---@param container Instance
local function watchContainer(container)
	track(container.ChildAdded:Connect(function(child)
		if child:GetAttribute(SOURCE_TAG) then
			task.defer(runDescendantScripts, child)
		end
	end))
	-- A script cloned deeper into something that is already there (a frame of an open GUI) starts too.
	track(container.DescendantAdded:Connect(function(node)
		if node:IsA("BaseScript") and not started[node] and node:GetAttribute(SOURCE_TAG) then
			task.defer(runScript, node)
		end
	end))
end

---Forward real server events the client sees: chat of every player, BindToClose on leave.
local enableGroundPickup

---Physically drop a tool into the world: strip the grips that weld it to the character, unanchor the
---handle and leave it in front of the player, with client ownership so it falls like a real drop.
local function dropToolToWorld(tool, character)
	local handle = tool:FindFirstChild("Handle")
	if not (character and handle and handle:IsA("BasePart")) then
		return
	end

	-- While the tool is still assembled (equipped), weld every loose part to the Handle so the drop
	-- stays rigid instead of scattering into separate falling parts.
	for _, part in ipairs(tool:GetDescendants()) do
		if part:IsA("BasePart") and part ~= handle then
			local alreadyWelded = false
			for _, j in ipairs(part:GetJoints()) do
				if (j:IsA("WeldConstraint") or j:IsA("Weld") or j:IsA("Motor6D"))
					and (j.Part0 == handle or j.Part1 == handle) then
					alreadyWelded = true
					break
				end
			end
			if not alreadyWelded then
				pcall(function()
					local weld = realInstance.new("WeldConstraint")
					weld.Part0 = handle
					weld.Part1 = part
					weld.Parent = handle
				end)
			end
			pcall(function() part.Anchored = false end)
		end
	end

	-- Detach from the character: remove ONLY the weld tying the handle to a character limb (the grip).
	-- Welds between the handle and the tool's own parts are kept so the tool stays in one piece.
	for _, node in ipairs(character:GetDescendants()) do
		if node:IsA("Weld") or node:IsA("Motor6D") or node:IsA("ManualWeld") then
			local other = (node.Part0 == handle and node.Part1) or (node.Part1 == handle and node.Part0) or nil
			if other and not other:IsDescendantOf(tool) then
				pcall(function() node:Destroy() end)
			end
		end
	end

	pcall(function() tool.CanBeDropped = true end)
	tool.Parent = workspaceService
	pcall(function() handle.Anchored = false end)
	pcall(function() handle.CanCollide = true end)
	local root = character:FindFirstChild("HumanoidRootPart") or character.PrimaryPart
	if root then
		pcall(function() tool:PivotTo(root.CFrame * CFrame.new(0, 0.5, -3)) end)
	end
	pcall(function() handle:SetNetworkOwner(localPlayer) end)
	enableGroundPickup(tool, handle)
end

-- Tools lying in the world, each with the state of its pickup connection.
local groundArmed = setmetatable({}, { __mode = "k" })

---Let a tool lying in the world be picked up the way Roblox does it: walking into its Handle equips
---it. Works for a tool we dropped and for one a script spawned on the ground.
---Set shared.SSEmuConfig.pickupToBackpack = true to put it in the Backpack instead of the hand.
---@param tool Instance
---@param handle Instance?
---@param grace number? Seconds before it can be taken, so a fresh drop is not grabbed back at once.
enableGroundPickup = function(tool, handle, grace)
	local previous = groundArmed[tool]
	if previous and previous.connection then
		pcall(function() previous.connection:Disconnect() end)
	end
	-- Only the latest call arms the tool, an older pending one sees a different state and stops.
	local state = {}
	groundArmed[tool] = state

	task.delay(grace or 1, function()
		if not active or groundArmed[tool] ~= state then
			return
		end
		if not (tool.Parent and tool:IsDescendantOf(workspaceService)) then
			return
		end
		handle = handle or tool:FindFirstChild("Handle") or tool:WaitForChild("Handle", 5)
		if not (handle and handle:IsA("BasePart")) or groundArmed[tool] ~= state then
			return
		end
		pcall(function() handle.CanTouch = true end)

		-- A tool that lies right at our feet was just dropped. It can be taken again only after we have
		-- stepped away from it once, otherwise a drop jumps straight back into the hand.
		local function distance()
			local character = localPlayer.Character
			local root = character and (character:FindFirstChild("HumanoidRootPart") or character.PrimaryPart)
			return root and (root.Position - handle.Position).Magnitude or math.huge
		end
		local okNear, near = pcall(distance)
		state.released = not okNear or near > 6
		if not state.released then
			task.spawn(function()
				while active and groundArmed[tool] == state and not state.released do
					task.wait(0.2)
					if not tool:IsDescendantOf(workspaceService) then
						break
					end
					local okFar, far = pcall(distance)
					if not okFar or far > 6 then
						state.released = true
					end
				end
			end)
		end

		state.connection = handle.Touched:Connect(function(hit)
			if not active or groundArmed[tool] ~= state then
				return
			end
			-- Another player walked into it (their real character here, or their touch on our tool
			-- relayed by the mirror): like Roblox, the tool goes to them.
			local okModel, model = pcall(function() return hit:FindFirstAncestorOfClass("Model") end)
			local picker = okModel and model and playersService:GetPlayerFromCharacter(model)
			if picker and picker ~= localPlayer then
				if SSEmu.handOver and not isReplica(tool) and SSEmu.handOver(tool, picker) then
					groundArmed[tool] = nil
					state.connection:Disconnect()
				end
				return
			end
			if not state.released then
				return
			end
			local character = localPlayer.Character
			if not (character and hit:IsDescendantOf(character)) or hit:FindFirstAncestorWhichIsA("Tool") then
				return
			end
			local humanoid = character:FindFirstChildOfClass("Humanoid")
			if not humanoid or humanoid.Health <= 0 then
				return
			end
			-- Still on the ground: not removed and not in somebody's hand.
			local holder = tool.Parent
			if not (holder and tool:IsDescendantOf(workspaceService)) or holder:FindFirstChildOfClass("Humanoid") then
				return
			end

			groundArmed[tool] = nil
			state.connection:Disconnect()
			pcall(function() handle.Anchored = false end)

			local equipped = false
			if config.pickupToBackpack ~= true then
				pcall(function() humanoid:EquipTool(tool) end)
				equipped = tool.Parent == character
			end
			if not equipped then
				local backpack = localPlayer:FindFirstChildOfClass("Backpack") or localPlayer:WaitForChild("Backpack", 3)
				if backpack then
					tool.Parent = backpack
				end
			end
			log("Picked up: " .. tool.Name, INFO_COLOR)
		end)
	end)
end

---Strip a lingering grip when a tool enters Workspace still welded to us (e.g. a game-side drop that
---did not remove the grip client-side), so the handle does not stay stuck to the hand.
local function emulateToolDrop(tool)
	task.defer(function()
		if not (tool and tool.Parent and tool:IsDescendantOf(workspaceService)) then
			return
		end
		local handle = tool:FindFirstChild("Handle")
		local character = localPlayer.Character
		if not (handle and handle:IsA("BasePart") and character) then
			return
		end
		local grips = {}
		for _, node in ipairs(character:GetDescendants()) do
			if node:IsA("Weld") or node:IsA("Motor6D") or node:IsA("ManualWeld") then
				local other = (node.Part0 == handle and node.Part1) or (node.Part1 == handle and node.Part0) or nil
				if other and not other:IsDescendantOf(tool) then
					table.insert(grips, node)
				end
			end
		end
		if #grips == 0 then
			return
		end
		for _, grip in ipairs(grips) do
			pcall(function() grip:Destroy() end)
		end
		pcall(function() handle.Anchored = false end)
		pcall(function() handle.CanCollide = true end)
		pcall(function() handle:SetNetworkOwner(localPlayer) end)
		enableGroundPickup(tool, handle)
	end)
end

---Drop the currently equipped tool when the drop key is pressed.
local function dropEquippedTool()
	local character = localPlayer.Character
	if not character then
		return
	end
	local tool = character:FindFirstChildOfClass("Tool")
	if tool then
		dropToolToWorld(tool, character)
	end
end

-- Killed players respawn, but their corpse vanishes to a hidden spot so the area stays clean.
local KILL_HIDE_CFRAME = CFrame.new(0, -5000, 0)
local corpseHandled = setmetatable({}, { __mode = "k" })

---Move a dead character out of sight and make it invisible/non-colliding.
---@param character Model
local function hideCorpse(character)
	task.spawn(function()
		pcall(function()
			for _, part in ipairs(character:GetDescendants()) do
				if part:IsA("BasePart") then
					part.CanCollide = false
					part.CanTouch = false
					part.CanQuery = false
					part.Anchored = true
					part.Transparency = 1
				elseif part:IsA("Decal") or part:IsA("Texture") then
					part.Transparency = 1
				end
			end
			character:PivotTo(config.killHideCFrame or KILL_HIDE_CFRAME)
		end)
	end)
end

---On death, hide the corpse and ask the emulation to respawn the player.
---@param character Model
local function watchCharacterDeath(character)
	local humanoid = character:FindFirstChildOfClass("Humanoid")
	if not humanoid then
		return
	end
	track(humanoid.Died:Connect(function()
		if corpseHandled[character] then
			return
		end
		corpseHandled[character] = true
		local player = playersService:GetPlayerFromCharacter(character)
		-- Your own death stays normal unless asked otherwise; killed players get hidden + respawned.
		if player == localPlayer and config.hideOwnDeath ~= true then
			return
		end
		if config.respawnKilled ~= false and player then
			pcall(function() player:LoadCharacter() end)
		end
		task.delay(config.killHideDelay or 0.15, function()
			hideCorpse(character)
		end)
	end))
end

---Watch every player's character for death. Disable with shared.SSEmuConfig.hideKills = false.
function setupKillHandler()
	if config.hideKills == false then
		return
	end
	local function bind(player)
		if player.Character then
			watchCharacterDeath(player.Character)
		end
		track(player.CharacterAdded:Connect(watchCharacterDeath))
	end
	for _, player in ipairs(playersService:GetPlayers()) do
		bind(player)
	end
	track(playersService.PlayerAdded:Connect(bind))
end

-- Seats: the engine only welds a character into a seat it simulates. Emulated vehicles are local
-- parts the server never sees, so walking into their seats does nothing and a hub calling Seat:Sit is
-- refused on the client. Both are handled here. Disable with shared.SSEmuConfig.emulateSeats = false.
SSEmu.seats = { armed = setmetatable({}, { __mode = "k" }), lastStand = 0 }

---Whether an instance is a Seat or VehicleSeat.
---@param inst any
---@return boolean
function SSEmu.seats.isSeat(inst)
	if realTypeof(inst) ~= "Instance" then
		return false
	end
	local ok, seat = pcall(function()
		return inst:IsA("Seat") or inst:IsA("VehicleSeat")
	end)
	return ok and seat == true
end

---Fire the signals a real sit or stand would fire, so hub scripts react to the emulated one.
---@param seat Instance
---@param humanoid Instance
---@param seated boolean
function SSEmu.seats.announce(seat, humanoid, seated)
	local seatSignals, humanoidSignals = SSEmu.seatSignals(seat), SSEmu.seatSignals(humanoid)
	seatSignals.occupant:Fire()
	seatSignals.changed:Fire("Occupant")
	humanoidSignals.seatPart:Fire()
	humanoidSignals.seated:Fire(seated, seated and seat or nil)
end

---Release the hand made seat weld and let the humanoid stand.
function SSEmu.seats.standUp()
	local info = SSEmu.seats.current
	if not info then
		return
	end
	SSEmu.seats.current = nil
	SSEmu.seatState = nil
	SSEmu.seats.lastStand = os.clock()
	SSEmu.seats.announce(info.seat, info.humanoid, false)
	for _, connection in ipairs(info.connections) do
		pcall(function() connection:Disconnect() end)
	end
	pcall(function() info.weld:Destroy() end)
	pcall(function()
		if info.seat:IsA("VehicleSeat") then
			info.seat.Throttle = 0
			info.seat.Steer = 0
		end
	end)
	pcall(function()
		info.humanoid.Sit = false
		info.humanoid.AutoRotate = true
		info.humanoid:ChangeState(Enum.HumanoidStateType.GettingUp)
	end)
end

---Seat the local humanoid: the engine's own Sit first, a hand made SeatWeld when the engine refuses.
---@param seat Instance
---@param humanoid Instance?
---@return boolean
function SSEmu.localSit(seat, humanoid)
	seat = unwrap(seat)
	humanoid = unwrap(humanoid)
	local character = localPlayer.Character
	if not character or not SSEmu.seats.isSeat(seat) then
		return false
	end
	if realTypeof(humanoid) ~= "Instance" or not humanoid:IsA("Humanoid") then
		humanoid = character:FindFirstChildOfClass("Humanoid")
	end
	-- Only our own character can be seated from here, other players are left alone.
	if not (humanoid and humanoid.Parent == character and humanoid.Health > 0) then
		return false
	end
	if (SSEmu.seats.current and SSEmu.seats.current.seat == seat) or humanoid.SeatPart == seat then
		return true
	end
	local okDisabled, disabled = pcall(function() return seat.Disabled end)
	if okDisabled and disabled then
		return false
	end

	SSEmu.seats.standUp()

	-- The engine welds and sets Occupant itself when it accepts the call.
	local thread = coroutine.running()
	SSEmu.rawSit[thread] = true
	pcall(seat.Sit, seat, humanoid)
	SSEmu.rawSit[thread] = nil
	-- The engine seats on a physics step, so it gets a few frames before the hand made weld takes over.
	for _ = 1, 10 do
		task.wait()
		if humanoid.SeatPart == seat then
			return true
		end
	end

	local root = character:FindFirstChild("HumanoidRootPart")
	if not root then
		return false
	end

	local weld = realInstance.new("Weld")
	weld.Name = "SeatWeld"
	weld.Part0 = seat
	weld.Part1 = root
	weld.C0 = CFrame.new(0, seat.Size.Y / 2, 0) * CFrame.Angles(-math.pi / 2, 0, 0)
	weld.C1 = CFrame.new(0, -root.Size.Y / 2, 0) * CFrame.Angles(-math.pi / 2, 0, 0)
	SSEmu.seats.hold(seat, humanoid, root, weld)
	weld.Parent = seat
	log("Seated (emulated): " .. seat:GetFullName(), INFO_COLOR)
	return true
end

---Keep the local humanoid seated on a weld the engine knows nothing about: ours, or one a hub made.
---@param seat Instance
---@param humanoid Instance
---@param root Instance
---@param weld Instance
SSEmu.seats.hold = function(seat, humanoid, root, weld)
	-- A humanoid left in Running inside a welded assembly keeps balancing the whole car with its own
	-- forces, which is why a weld alone leaves the car floating and undrivable. Seated turns them off.
	pcall(function()
		root.AssemblyLinearVelocity = Vector3.zero
		root.AssemblyAngularVelocity = Vector3.zero
		humanoid.AutoRotate = false
		humanoid.Sit = true
		humanoid:ChangeState(Enum.HumanoidStateType.Seated)
	end)

	local info = { seat = seat, humanoid = humanoid, weld = weld, connections = {} }
	SSEmu.seats.current = info
	SSEmu.seatState = { seat = seat, humanoid = humanoid }
	SSEmu.seats.announce(seat, humanoid, true)

	-- Jumping, dying or the seat leaving the world ends the ride like it does on a real seat.
	local userInput = realGame:GetService("UserInputService")
	local seatedAt = os.clock()
	table.insert(info.connections, humanoid.Jumping:Connect(function(jumping)
		if jumping then
			SSEmu.seats.standUp()
		end
	end))
	table.insert(info.connections, userInput.JumpRequest:Connect(function()
		if SSEmu.seats.current == info and os.clock() - seatedAt > 0.5 then
			SSEmu.seats.standUp()
		end
	end))
	-- The engine keeps trying to stand a humanoid that has no SeatPart, it is put back every frame.
	table.insert(info.connections, runService.Heartbeat:Connect(function()
		if SSEmu.seats.current ~= info then
			return
		end
		local state = humanoid:GetState()
		if state ~= Enum.HumanoidStateType.Seated and state ~= Enum.HumanoidStateType.Dead
			and state ~= Enum.HumanoidStateType.Jumping then
			pcall(function()
				humanoid.Sit = true
				humanoid:ChangeState(Enum.HumanoidStateType.Seated)
			end)
		end
	end))
	table.insert(info.connections, humanoid.Died:Connect(SSEmu.seats.standUp))
	table.insert(info.connections, weld.AncestryChanged:Connect(function()
		if SSEmu.seats.current == info and not weld.Parent then
			SSEmu.seats.standUp()
		end
	end))
	table.insert(info.connections, seat.AncestryChanged:Connect(function()
		if not seat:IsDescendantOf(workspaceService) then
			SSEmu.seats.standUp()
		end
	end))

	-- Occupant never gets set on a hand made weld, so the engine will not drive a VehicleSeat for us.
	if seat:IsA("VehicleSeat") then
		table.insert(info.connections, runService.Heartbeat:Connect(function()
			if SSEmu.seats.current ~= info or userInput:GetFocusedTextBox() then
				return
			end
			local throttle = (userInput:IsKeyDown(Enum.KeyCode.W) or userInput:IsKeyDown(Enum.KeyCode.Up)) and 1 or 0
			throttle = throttle - ((userInput:IsKeyDown(Enum.KeyCode.S) or userInput:IsKeyDown(Enum.KeyCode.Down)) and 1 or 0)
			local steer = (userInput:IsKeyDown(Enum.KeyCode.D) or userInput:IsKeyDown(Enum.KeyCode.Right)) and 1 or 0
			steer = steer - ((userInput:IsKeyDown(Enum.KeyCode.A) or userInput:IsKeyDown(Enum.KeyCode.Left)) and 1 or 0)
			pcall(function()
				seat.Throttle = throttle
				seat.Steer = steer
				seat.ThrottleFloat = throttle
				seat.SteerFloat = steer
			end)
		end))
	end
end

---A hub that welds the character into a seat itself (door prompts do this) gets the same humanoid
---handling, otherwise the weld holds but the humanoid fights the car.
---@param joint Instance
function SSEmu.seats.adopt(joint)
	if SSEmu.seats.current or not (joint:IsA("Weld") or joint:IsA("WeldConstraint") or joint:IsA("Motor6D")) then
		return
	end
	local character = localPlayer.Character
	local root = character and character:FindFirstChild("HumanoidRootPart")
	if not root then
		return
	end
	local okParts, part0, part1 = pcall(function() return joint.Part0, joint.Part1 end)
	if not okParts then
		return
	end
	local function ours(part)
		return realTypeof(part) == "Instance" and part:IsDescendantOf(character)
	end
	local seat = (ours(part1) and part0) or (ours(part0) and part1) or nil
	if not SSEmu.seats.isSeat(seat) then
		return
	end
	local humanoid = character:FindFirstChildOfClass("Humanoid")
	if not humanoid or humanoid.Health <= 0 or humanoid.SeatPart then
		return
	end
	SSEmu.seats.hold(seat, humanoid, root, joint)
	log("Seated (adopted weld): " .. seat:GetFullName(), INFO_COLOR)
end

---Pick the seat a door prompt is meant to put the player in: the prompt's own part when it is a seat,
---otherwise the driver seat of the same model, otherwise the nearest seat of that model.
---@param prompt Instance
---@return Instance?
function SSEmu.seats.forPrompt(prompt)
	local part = prompt.Parent
	if realTypeof(part) ~= "Instance" then
		return nil
	end
	if SSEmu.seats.isSeat(part) then
		return part
	end
	if part:IsA("Attachment") then
		part = part.Parent
	end
	local model = part and part:FindFirstAncestorOfClass("Model")
	if not model then
		return nil
	end
	local position = part:IsA("BasePart") and part.Position or model:GetPivot().Position
	local best, bestDistance
	for _, node in ipairs(model:GetDescendants()) do
		if SSEmu.seats.isSeat(node) then
			local distance = (node.Position - position).Magnitude
			if node:IsA("VehicleSeat") or node.Name:lower():find("drive", 1, true) then
				distance = distance - 100
			end
			if not best or distance < bestDistance then
				best, bestDistance = node, distance
			end
		end
	end
	if best and (best.Position - position).Magnitude > 20 then
		return nil
	end
	return best
end

---Arm an emulated seat so walking into it seats the local character.
---@param seat Instance
function SSEmu.seats.arm(seat)
	if SSEmu.seats.armed[seat] then
		return
	end
	SSEmu.seats.armed[seat] = true
	pcall(function() seat.CanTouch = true end)
	track(seat.Touched:Connect(function(hit)
		if not active or config.emulateSeats == false or SSEmu.seats.current then
			return
		end
		-- A seat just left needs a moment before it takes the character again, like the engine's cooldown.
		if os.clock() - SSEmu.seats.lastStand < 1.5 then
			return
		end
		local character = localPlayer.Character
		if not (character and hit:IsDescendantOf(character)) or hit:FindFirstAncestorWhichIsA("Tool") then
			return
		end
		local humanoid = character:FindFirstChildOfClass("Humanoid")
		if not humanoid or humanoid.Sit or humanoid.SeatPart or humanoid.PlatformStand then
			return
		end
		local okOccupant, occupant = pcall(function() return seat.Occupant end)
		if okOccupant and occupant then
			return
		end
		task.spawn(SSEmu.localSit, seat, humanoid)
	end))
end

---Watch emulated seats that reach the world and keep the manual weld in step with respawns.
function setupSeats()
	if config.emulateSeats == false then
		return
	end
	local function scan(node)
		if SSEmu.seats.isSeat(node) then
			local ok, tagged = pcall(function() return node:GetAttribute(SOURCE_TAG) end)
			if ok and tagged then
				SSEmu.seats.arm(node)
			end
		elseif node:IsA("JointInstance") or node:IsA("WeldConstraint") then
			-- The hub's weld may be created before its parts are set, so it is checked a frame later.
			task.defer(function()
				if active then
					pcall(SSEmu.seats.adopt, node)
				end
			end)
		end
	end
	pcall(function()
		for _, node in ipairs(workspaceService:GetDescendants()) do
			scan(node)
		end
	end)
	track(workspaceService.DescendantAdded:Connect(scan))
	track(localPlayer.CharacterAdded:Connect(SSEmu.seats.standUp))

	-- Door prompts: the hub's handler runs first (door animation, its own Sit). When nothing has seated
	-- us shortly after, the prompt's seat is taken the way the server would have done it.
	pcall(function()
		local promptService = realGame:GetService("ProximityPromptService")
		track(promptService.PromptTriggered:Connect(function(prompt, player)
			if player ~= localPlayer or config.emulateSeats == false then
				return
			end
			local okTag, tagged = pcall(function()
				return prompt:GetAttribute(SOURCE_TAG) or (prompt.Parent and prompt.Parent:GetAttribute(SOURCE_TAG))
			end)
			if not (okTag and tagged) then
				return
			end
			local seat = SSEmu.seats.forPrompt(prompt)
			if not seat then
				return
			end
			task.delay(1.2, function()
				if not active or SSEmu.seats.current then
					return
				end
				local character = localPlayer.Character
				local humanoid = character and character:FindFirstChildOfClass("Humanoid")
				if not humanoid or humanoid.SeatPart or humanoid.Sit then
					return
				end
				local okOccupant, occupant = pcall(function() return seat.Occupant end)
				if okOccupant and occupant then
					return
				end
				SSEmu.localSit(seat, humanoid)
			end)
		end))
	end)
end

---Bind the drop key (Backspace by default; override with shared.SSEmuConfig.dropKey) to a world drop,
---and strip grips from tools that otherwise reach Workspace still stuck to the hand.
function setupToolDrops()
	local dropKey = config.dropKey or Enum.KeyCode.Backspace
	local userInput = realGame:GetService("UserInputService")
	track(userInput.InputBegan:Connect(function(input, processed)
		if not processed and input.KeyCode == dropKey then
			dropEquippedTool()
		end
	end))
	track(workspaceService.DescendantAdded:Connect(function(node)
		if not node:IsA("Tool") then
			return
		end
		local parent = node.Parent
		-- In a character's hand: equipped, not lying around.
		if parent and parent:FindFirstChildOfClass("Humanoid") then
			return
		end
		if parent == workspaceService then
			emulateToolDrop(node)
		end
		-- An emulated tool that reaches the world any other way (a script spawning it) can be taken too.
		-- A mirrored copy of another client's tool is scenery, it is never picked up.
		if node:GetAttribute(SOURCE_TAG) and not isReplica(node) then
			enableGroundPickup(node, nil, 0.5)
		end
	end))
end

function startServerEvents()
	pcall(function()
		track(realGame:GetService("TextChatService").MessageReceived:Connect(function(message)
			local source = message.TextSource
			local player = source and playersService:GetPlayerByUserId(source.UserId)
			if player then
				chatSignalFor(player):Fire(message.Text)
			end
		end))
	end)

	-- Legacy chat fires Chatted itself, fake players are fired by their own Chat method.
	track(playersService.PlayerRemoving:Connect(function(player)
		if player ~= localPlayer then
			return
		end
		for _, callback in ipairs(closeCallbacks) do
			task.spawn(callback)
		end
	end))
end

---Allow Character:Clone() the way server scripts expect.
---@param character Instance
local function makeArchivable(character)
	pcall(function()
		character.Archivable = true
	end)
end

---Deliver emulated Starter content the way a real server would.
function setupWatchers()
	if localPlayer.Character then
		makeArchivable(localPlayer.Character)
	end
	track(localPlayer.CharacterAdded:Connect(makeArchivable))

	task.spawn(function()
		local playerGui = localPlayer:WaitForChild("PlayerGui", 10)
		if playerGui then
			watchContainer(playerGui)
			track(playerGui.ChildAdded:Connect(function(child)
				if child:IsA("LayerCollector") and isReplica(child) then
					lockReplicaGui(child)
				end
				if child:IsA("ScreenGui") then
					task.defer(hideTemplateTwin, child)
				end
			end))
		end
	end)

	-- A GUI cloned straight into CoreGui/gethui also leaves its template rendering; hide it too.
	pcall(function()
		local ui = getUiParent()
		track(ui.DescendantAdded:Connect(function(node)
			if node:IsA("ScreenGui") and not isUnderModuleTree(node) then
				task.defer(hideTemplateTwin, node)
			end
		end))
	end)

	local function onPlayerChild(child)
		if child:IsA("Backpack") or child:IsA("PlayerScripts") then
			watchContainer(child)
		end
	end
	for _, child in ipairs(localPlayer:GetChildren()) do
		onPlayerChild(child)
	end
	track(localPlayer.ChildAdded:Connect(onPlayerChild))

	if localPlayer.Character then
		watchContainer(localPlayer.Character)
	end
	track(localPlayer.CharacterAdded:Connect(watchContainer))

	-- An emulated server Script dropped anywhere in Workspace runs there, like on a real server.
	-- LocalScripts only run under our own character.
	-- SPAWNS: a loaded map brings its own SpawnLocations, but the real server still spawns us at the
	-- real game's spawn. The emulated ones are remembered and used for every respawn, and StarterPack
	-- and StarterCharacterScripts content is handed out again like a server does on spawn.
	-- Disable with shared.SSEmuConfig.emulateSpawns = false.
	SSEmu.spawns = SSEmu.spawns or {}

	local function pickSpawn()
		local matching, enabled = {}, {}
		for spawn in pairs(SSEmu.spawns) do
			if spawn.Parent and spawn:IsDescendantOf(workspaceService) then
				local okEnabled, isEnabled = pcall(function() return spawn.Enabled end)
				if not okEnabled or isEnabled then
					table.insert(enabled, spawn)
					local okTeam, fits = pcall(function()
						return spawn.Neutral or spawn.TeamColor == localPlayer.TeamColor
					end)
					if okTeam and fits then
						table.insert(matching, spawn)
					end
				end
			else
				SSEmu.spawns[spawn] = nil
			end
		end
		local list = #matching > 0 and matching or enabled
		return list[1] and list[math.random(1, #list)] or nil
	end

	local function placeAtSpawn(character)
		local spawn = pickSpawn()
		if not (spawn and character and character.Parent) then
			return false
		end
		local ok = pcall(function()
			character:PivotTo(spawn.CFrame + Vector3.new(0, spawn.Size.Y / 2 + 3.5, 0))
			local root = character:FindFirstChild("HumanoidRootPart") or character.PrimaryPart
			if root then
				root.AssemblyLinearVelocity = Vector3.new(0, 0, 0)
			end
		end)
		if ok then
			log("Spawned at " .. spawn:GetFullName(), INFO_COLOR)
		end
		return ok
	end
	SSEmu.placeAtSpawn = placeAtSpawn

	---True when nothing solid is below the character: the real map under it was removed.
	local function overVoid(character)
		local root = character:FindFirstChild("HumanoidRootPart") or character.PrimaryPart
		if not root then
			return false
		end
		local params = RaycastParams.new()
		params.FilterDescendantsInstances = { character }
		params.FilterType = Enum.RaycastFilterType.Exclude
		return workspaceService:Raycast(root.Position, Vector3.new(0, -2000, 0), params) == nil
	end

	local rescueQueued = false
	local function onSpawnLocation(spawn)
		SSEmu.spawns[spawn] = true
		-- The map just arrived. If we are hanging over the void because the old map is gone, move to
		-- the new spawn now instead of falling to death first.
		if rescueQueued or config.emulateSpawns == false then
			return
		end
		rescueQueued = true
		task.delay(1.5, function()
			rescueQueued = false
			local character = localPlayer.Character
			local okVoid, falling = pcall(overVoid, character)
			if active and character and okVoid and falling then
				placeAtSpawn(character)
			end
		end)
	end

	track(localPlayer.CharacterAdded:Connect(function(character)
		if config.emulateSpawns == false then
			return
		end
		task.spawn(function()
			local root = character:WaitForChild("HumanoidRootPart", 10)
			if not (active and root) then
				return
			end
			task.wait(0.1)
			placeAtSpawn(character)

			-- Emulated StarterPack tools come back on every spawn.
			local backpack = localPlayer:FindFirstChildOfClass("Backpack") or localPlayer:WaitForChild("Backpack", 5)
			if backpack then
				for _, child in ipairs(starterPack:GetChildren()) do
					if child:IsA("Tool") and child:GetAttribute(SOURCE_TAG) and not backpack:FindFirstChild(child.Name) then
						giveTool(child:Clone())
					end
				end
			end

			-- Emulated StarterCharacterScripts are copied into the new character.
			pcall(function()
				local folder = realGame:GetService("StarterPlayer"):FindFirstChild("StarterCharacterScripts")
				for _, child in ipairs(folder and folder:GetChildren() or {}) do
					if child:GetAttribute(SOURCE_TAG) and not character:FindFirstChild(child.Name) then
						child:Clone().Parent = character
					end
				end
			end)
		end)
	end))

	track(workspaceService.DescendantAdded:Connect(function(node)
		if node:IsA("SpawnLocation") then
			if node:GetAttribute(SOURCE_TAG) then
				onSpawnLocation(node)
			end
			return
		end
		if not node:IsA("BaseScript") or started[node] or not node:GetAttribute(SOURCE_TAG) then
			return
		end
		if node:IsA("LocalScript") then
			local character = localPlayer.Character
			if not (character and node:IsDescendantOf(character)) then
				return
			end
		end
		task.defer(runScript, node)
	end))

	track(starterGui.ChildAdded:Connect(function(child)
		if not child:GetAttribute(SOURCE_TAG) then
			return
		end
		local playerGui = localPlayer:WaitForChild("PlayerGui", 5)
		if not playerGui then
			return
		end
		-- Move the original out of real StarterGui so Roblox does not auto-copy it to PlayerGui on spawn.
		local delivered = child
		pcall(function()
			child.Parent = serverStorage
		end)
		if delivered:IsA("ScreenGui") then
			pcall(function() delivered.ResetOnSpawn = false end)
		end
		delivered.Parent = playerGui
		task.defer(runDescendantScripts, delivered)
	end))

	track(starterPack.ChildAdded:Connect(function(child)
		if child:IsA("Tool") and child:GetAttribute(SOURCE_TAG) then
			giveTool(child:Clone())
		end
	end))
end

end

-- ═══════════════════════════════════════════════════════════════════
-- EXTERNAL EXECUTOR TAKEOVER
-- ═══════════════════════════════════════════════════════════════════

---Make everything the executor runs afterwards use the emulated environment.
local function takeoverGlobals()
	local defaultScript = create("Script", { Name = "ExternalScript", Disabled = true }, serverScriptService)

	local overrides = {
		game = mockGame,
		Game = mockGame,
		owner = localPlayer,
		Instance = makeInstanceApi(defaultScript),
		typeof = sandboxTypeof,
		require = function(target)
			return smartRequire(target, defaultScript)
		end,
		loadstring = function(source, chunkName)
			if type(source) == "table" then
				return SSEmu.babyboo(source)
			end
			local func, err = realLoadstring(source, chunkName)
			if func and active then
				infect(func, defaultScript, false)
			end
			return func, err
		end,
		NS = function(source, parent)
			return spawnSource(source, parent, false)
		end,
		NLS = function(source, parent)
			return spawnSource(source, parent, true)
		end,
	}

	for key, value in pairs(overrides) do
		savedGlobals[key] = { value = genv[key] }
		genv[key] = value
	end
end

-- ═══════════════════════════════════════════════════════════════════
-- FEATURES: duplicate cleaner, live convert, url loader, commands
-- ═══════════════════════════════════════════════════════════════════

-- Block scoped: Luau allows 200 locals per function, only the names used later stay outside.
local httpGet, setupDedupe, setupLiveConvert, resolvePath, findExplicitMainModule, commandHandlers
do
-- State. The duplicate cleaner is off by default, enable it with /dedupe on.
local liveConvertEnabled = true
local dedupeEnabled = false
local dedupePending = {}

---Send an HTTP GET through the executor request function.
---@param url string
---@return string?, string?
function httpGet(url)
	local requestFunction = request or http_request or (syn and syn.request) or (http and http.request)
	if not requestFunction then
		return nil, "No request function in this executor."
	end

	local ok, response = pcall(requestFunction, { Url = url, Method = "GET" })
	if not ok then
		return nil, tostring(response)
	end

	local status = response.StatusCode or response.Status
	if status ~= 200 then
		return nil, "HTTP " .. tostring(status)
	end
	return response.Body
end

---Richness score of a GUI: how many descendants it has and its creation order.
---The real GUI is fully built (more descendants) and newer; an undraggable leftover shell
---or a stale clone is emptier or older.
---@param inst Instance
---@return number, number
---Structural signature of a GUI: its immediate children by class and name, order independent.
---Two copies of the same window share a signature even when their ScreenGui names differ.
---@param gui Instance
---@return string, number
local function guiSignature(gui)
	local parts = {}
	local ok, children = pcall(function() return gui:GetChildren() end)
	if ok then
		for _, child in ipairs(children) do
			table.insert(parts, child.ClassName .. ":" .. child.Name)
		end
	end
	table.sort(parts)
	return table.concat(parts, "|"), #parts
end

---Remove the leaked twin of an emulated GUI. Our GUI runs in the sandbox and carries SOURCE_TAG,
---so it keeps the emulation hooks and stays draggable. A copy that escaped to the real environment
---has no tag and no hooks (the broken, undraggable one). We only ever destroy an untagged ScreenGui
---that structurally matches one of ours, so a tagged (working) GUI is never touched and unrelated
---game GUIs are left alone.
local function dedupeGuis()
	local containers = {}
	local playerGui = localPlayer:FindFirstChildOfClass("PlayerGui")
	if playerGui then table.insert(containers, playerGui) end
	table.insert(containers, getUiParent())
	if coreGui then table.insert(containers, coreGui) end

	-- Signatures of the GUIs we created.
	local ours = {}
	for _, container in ipairs(containers) do
		local ok, children = pcall(function() return container:GetChildren() end)
		if ok then
			for _, child in ipairs(children) do
				if child:IsA("ScreenGui") and child:GetAttribute(SOURCE_TAG) then
					local sig, size = guiSignature(child)
					if size >= 2 then
						ours[sig] = child
					end
				end
			end
		end
	end

	-- Destroy only an untagged ScreenGui that is a structural twin of one of ours.
	for _, container in ipairs(containers) do
		local ok, children = pcall(function() return container:GetChildren() end)
		if ok then
			for _, child in ipairs(children) do
				if child:IsA("ScreenGui") and not child:GetAttribute(SOURCE_TAG) then
					local sig, size = guiSignature(child)
					if size >= 2 and ours[sig] and ours[sig] ~= child then
						pcall(function() child:Destroy() end)
						log("Removed leaked duplicate GUI: " .. child.Name, WARN_COLOR)
					end
				end
			end
		end
	end
end

---Tools stay origin + newest scoped within their own container.
---@param container Instance
local function dedupeTools(container)
	local seen = {}
	local children = container:GetChildren()
	for index = #children, 1, -1 do
		local child = children[index]
		if child:GetAttribute(SOURCE_TAG) and child:IsA("Tool") then
			local origin = child:GetAttribute(ORIGIN_ATTRIBUTE)
			if origin then
				local key = child.Name .. ":" .. tostring(origin)
				if seen[key] then
					pcall(function() child:Destroy() end)
					log("Removed duplicate: Tool:" .. child.Name, WARN_COLOR)
				else
					seen[key] = true
				end
			end
		end
	end
end

---Dedupe one container (tools) plus every GUI container (global).
---@param container Instance
local function dedupeContainer(container)
	pcall(dedupeTools, container)
	pcall(dedupeGuis)
end

---Queue a dedupe pass so a burst of children is handled once.
---@param container Instance
local function queueDedupe(container)
	if not dedupeEnabled or dedupePending[container] then
		return
	end
	dedupePending[container] = true
	-- Two passes: an early one, then a late one so GUIs whose scripts start a beat later
	-- (and Roblox-replicated copies that arrive late) are still collapsed.
	task.delay(0.2, function()
		dedupePending[container] = nil
		if active and dedupeEnabled and container.Parent then
			dedupeContainer(container)
		end
	end)
	task.delay(1.5, function()
		if active and dedupeEnabled and container.Parent then
			dedupeContainer(container)
		end
	end)
end

---Find every container that can hold emulated GUIs and tools.
---@return table
local function getDedupeTargets()
	local targets = {}
	local playerGui = localPlayer:FindFirstChildOfClass("PlayerGui")
	local backpack = localPlayer:FindFirstChildOfClass("Backpack")

	if playerGui then table.insert(targets, playerGui) end
	if backpack then table.insert(targets, backpack) end
	if localPlayer.Character then table.insert(targets, localPlayer.Character) end
	table.insert(targets, getUiParent())
	if coreGui then table.insert(targets, coreGui) end
	return targets
end

---Run a full dedupe pass now.
function SSEmu.dedupe()
	for _, container in ipairs(getDedupeTargets()) do
		dedupeContainer(container)
	end
end

---Watch the containers for new duplicates.
function setupDedupe()
	local function watch(container)
		track(container.ChildAdded:Connect(function()
			queueDedupe(container)
		end))
	end

	for _, container in ipairs(getDedupeTargets()) do
		watch(container)
	end

	track(localPlayer.ChildAdded:Connect(function(child)
		if child:IsA("Backpack") or child:IsA("PlayerGui") then
			watch(child)
		end
	end))
	track(localPlayer.CharacterAdded:Connect(watch))
end

---Convert any instance tree into running emulated content, on a clone.
---@param inst Instance
---@param replica boolean?
---@return Instance
function SSEmu.convert(inst, replica)
	-- Non-archivable instances clone as nil, so the flag is lifted for the copy only.
	local okFlag, wasArchivable = pcall(function() return inst.Archivable end)
	pcall(function() inst.Archivable = true end)
	local copy = inst:Clone()
	if okFlag then
		pcall(function() inst.Archivable = wasArchivable end)
	end
	if not copy then
		error("Convert: " .. inst:GetFullName() .. " cannot be cloned", 2)
	end
	prepareAsset(copy, replica, "convert:" .. inst:GetFullName())

	if copy:IsA("Tool") then
		giveTool(copy)
	elseif copy:IsA("LayerCollector") then
		copy.Parent = localPlayer:FindFirstChildOfClass("PlayerGui")
	else
		copy.Parent = serverScriptService
		runDescendantScripts(copy, true)
	end
	return copy
end

---Run scripts that appear in the emulated server containers on their own.
function setupLiveConvert()
	local function onAdded(node)
		if not liveConvertEnabled or not node:IsA("BaseScript") or started[node] then
			return
		end
		pcall(function() node.Disabled = true end)
		task.defer(runScript, node)
	end

	-- Only ServerScriptService runs scripts, ServerStorage is storage on a real server too.
	local containers = { serverScriptService }
	if config.runServerStorage == true then
		table.insert(containers, serverStorage)
	end
	for _, container in ipairs(containers) do
		track(container.DescendantAdded:Connect(onAdded))
	end
end

---Resolve a dotted path from game, e.g. Workspace.Model.Part.
---@param path string
---@return Instance?
function resolvePath(path)
	local current = realGame
	for segment in path:gmatch("[^%.%/]+") do
		if segment ~= "game" then
			current = current:FindFirstChild(segment)
			if not current then
				return nil
			end
		end
	end
	return current
end

---Load a model or admin loader by asset id into ServerScriptService and run every script in it.
---@param assetId number
---@return Instance?
function SSEmu.loadModel(assetId)
	local objects = fetchObjects(assetId)
	if not objects then
		log("Load failed: asset " .. tostring(assetId) .. " could not be downloaded", ERROR_COLOR)
		return nil
	end
	local folder = create("Folder", { Name = "Loaded_" .. assetId }, serverScriptService)
	for index, root in ipairs(objects) do
		prepareAsset(root, false, "load:" .. assetId, index)
		root.Parent = folder
	end
	runDescendantScripts(folder, true)
	log("Loaded " .. #objects .. " root(s) from " .. assetId, INFO_COLOR)
	return folder
end

---Only an explicit MainModule (root module or a child literally named MainModule), never a
---random nested module, so model-style hubs aren't mistaken for require-style ones.
---@param objects table
---@return ModuleScript?
function findExplicitMainModule(objects)
	for _, root in ipairs(objects) do
		if root:IsA("ModuleScript") then
			return root
		end
	end
	for _, root in ipairs(objects) do
		local named = root:FindFirstChild("MainModule", true)
		if named and named:IsA("ModuleScript") then
			return named
		end
	end
	return nil
end

---Run a converted asset. With an entry (the original loader line, e.g. require(id).load("name")) the
---line itself runs inside the emulation, exactly like on a server: only the MainModule runs and whatever
---it clones out starts through the watchers. Without one, the MainModule is required AND the asset's
---Scripts/LocalScripts run in place, so model-style hubs still come alive.
---@param assetId number?
---@param entry string?
---@return Instance?
function SSEmu.runConverted(assetId, entry, path)
	-- An instance of the game itself was converted: it is looked up again by its path.
	if type(path) == "string" and path ~= "" then
		return SSEmu.runConvertedPath(path)
	end
	if type(entry) == "string" and entry:match("%S") then
		-- An expression such as require(id).Value is not a statement, return makes it one.
		local source = entry
		if not realLoadstring(source) then
			source = "return " .. entry
		end
		log("Converted entry: " .. entry, INFO_COLOR)
		local ok, err = SSEmu.execute(source, "Ezproxy", false, true)
		if not ok then
			error("Converted entry does not compile: " .. tostring(err), 2)
		end
		return nil
	end

	local objects = fetchObjects(assetId, 3)
	if not objects then
		error("Converted asset " .. tostring(assetId) .. " could not be downloaded.", 2)
	end
	local tools = {}
	for index, root in ipairs(objects) do
		prepareAsset(root, false, "convert:" .. assetId, index)
		if root:IsA("Tool") then
			table.insert(tools, root)
		end
	end

	-- Module asset: exactly what require(id) does on a server. Only the MainModule runs, the asset stays
	-- out of sight and whatever the module clones out starts through the watchers.
	local main = findExplicitMainModule(objects)
	local folder = create("Folder", { Name = "Converted_" .. assetId }, main and moduleHolder or serverScriptService)
	for _, root in ipairs(objects) do
		if not (root:IsA("Tool") and not main) then
			root.Parent = folder
		end
	end
	if main then
		local ok, value = pcall(requireModule, main, false)
		if not ok then
			log("Converted require note: " .. tostring(value), WARN_COLOR)
		elseif type(value) == "function" or type(value) == "table" then
			log("MainModule returned a " .. type(value) .. " and was not called. If nothing shows up, convert the "
				.. "whole loader line instead: .convert require(" .. assetId .. ").NAME(owner.Name)", INFO_COLOR)
		end
		log("Converted asset " .. assetId .. " required", INFO_COLOR)
		return folder
	end

	-- Model asset (no MainModule): its scripts run in place and tools go to the Backpack.
	runDescendantScripts(folder, true)
	for _, tool in ipairs(tools) do
		giveTool(tool)
	end
	log("Converted asset " .. assetId .. " running (" .. #objects .. " root(s))", INFO_COLOR)
	return folder
end

---Download a script and run it inside the emulation.
---@param url string
function SSEmu.loadUrl(url)
	local body, err = httpGet(url)
	if not body then
		return log("Download failed: " .. tostring(err), ERROR_COLOR)
	end
	log("Loaded " .. #body .. " bytes from " .. url, INFO_COLOR)
	return SSEmu.execute(body, "UrlScript")
end

-- Console commands, each handler receives the text after the command name.
commandHandlers = {
	url = function(argument)
		SSEmu.loadUrl(argument)
	end,
	give = function(argument)
		local assetId = tonumber(argument)
		if not assetId then
			return log("Usage: /give <assetId>", WARN_COLOR)
		end
		giveAsset(assetId)
		SSEmu.replicate("give", { id = assetId })
	end,
	convert = function(argument)
		local target = resolvePath(argument)
		if not target then
			return log("Path not found: " .. argument, ERROR_COLOR)
		end
		SSEmu.convert(target)
		SSEmu.replicate("convert", { path = argument })
		log("Converted " .. target:GetFullName(), INFO_COLOR)
	end,
	live = function(argument)
		liveConvertEnabled = argument ~= "off"
		log("Live convert: " .. (liveConvertEnabled and "on" or "off"), INFO_COLOR)
	end,
	dedupe = function(argument)
		if argument == "on" or argument == "off" then
			dedupeEnabled = argument == "on"
		end
		if argument ~= "off" and dedupeEnabled then
			SSEmu.dedupe()
		end
		log("Dedupe: " .. (dedupeEnabled and "on" or "off"), INFO_COLOR)
	end,
	tree = function()
		local count = 0
		for _, node in ipairs(serverScriptService:GetDescendants()) do
			count = count + 1
			if count > 80 then
				return log("... truncated", WARN_COLOR)
			end
			log(node.ClassName .. "  " .. node:GetFullName(), Color3.fromRGB(150, 150, 150))
		end
		log(count .. " instances in ServerScriptService", INFO_COLOR)
	end,
	help = function()
		log("/url <link>  /give <id>  /convert <path>  /live  /dedupe on|off  /rep on|off  /mirror on|off  /resync  /room <name>  /tree", INFO_COLOR)
	end,
}

---Handle a console line that starts with a slash.
---@param line string
---@return boolean
function SSEmu.command(line)
	local name, argument = line:match("^/(%w+)%s*(.-)%s*$")
	local handler = name and commandHandlers[name:lower()]
	if not handler then
		return false
	end
	handler(argument)
	return true
end

end

-- ═══════════════════════════════════════════════════════════════════
-- REPLICATION: mirror executed input to other clients through the relay
-- ═══════════════════════════════════════════════════════════════════

-- Block scoped: Luau allows 200 locals per function, only the names used later stay outside.
local httpService, replication, applyEvent
do
-- Services.
httpService = realGame:GetService("HttpService")

-- State.
replication = {
	enabled = false,
	connected = false,
	warned = false,
	failures = 0,
	since = -1,
	clientId = tostring(localPlayer.UserId) .. "-" .. tostring(math.random(100000, 999999)),
}

---Call the relay server through the executor request function.
---@param method string
---@param path string
---@param body table?
---@return table?, string?
local function relayRequest(method, path, body)
	local headers = { ["Content-Type"] = "application/json" }
	if RELAY_KEY ~= "" then
		headers["X-Key"] = RELAY_KEY
	end

	local ok, response = pcall(executorRequest, {
		Url = RELAY_URL .. path,
		Method = method,
		Headers = headers,
		Body = SSEmu.encodeJson(body),
	})
	if not ok then
		return nil, tostring(response)
	end

	local status = response.StatusCode or response.Status
	if status ~= 200 then
		return nil, "HTTP " .. tostring(status)
	end

	local decoded, result = pcall(httpService.JSONDecode, httpService, response.Body)
	if not decoded then
		return nil, "Bad relay response"
	end
	return result
end

---Log a relay problem only once until the relay comes back.
---@param text string
local function warnRelayOnce(text)
	if replication.warned then
		return
	end
	replication.warned = true
	log(text, WARN_COLOR)
end

---Send an event to every other client in the room.
---@param kind string
---@param payload table
function SSEmu.replicate(kind, payload)
	if not replication.enabled or not replication.connected then
		return
	end

	task.spawn(function()
		local _, err = relayRequest("POST", "/push", {
			room = RELAY_ROOM,
			client = replication.clientId,
			type = kind,
			payload = payload,
		})
		if err then
			warnRelayOnce("Replication push failed: " .. err)
		end
	end)
end

-- ═══════════════════════════════════════════════════════════════════
-- REMOTE SYNC: FireServer/FireClient/FireAllClients reach the other clients' emulated servers
-- ═══════════════════════════════════════════════════════════════════

local MAX_ENCODE_DEPTH = 6

-- ═══════════════════════════════════════════════════════════════════
-- Serialization: instances travel as paths, values as tagged tables.
-- ═══════════════════════════════════════════════════════════════════

---Encode an instance as a path both clients can resolve.
---@param inst Instance
---@return table?
local function encodePath(inst)
	local segments = {}
	local current = inst

	while current and current ~= realGame and current ~= serverRoot and current ~= moduleHolder do
		local index = 1
		local parent = current.Parent
		if parent then
			for _, sibling in ipairs(parent:GetChildren()) do
				if sibling == current then
					break
				end
				if sibling.Name == current.Name then
					index = index + 1
				end
			end
		end
		table.insert(segments, 1, { current.Name, index })
		current = parent
	end

	-- Players.<name>: origin'in UserId'si ile kodla, replica aynı player'a çözer (tool/gear origin'in
	-- karakterine gider, replica'nın kendi gövdesine değil). Oyuncu offline/yoksa fallback LocalPlayer.
	if current == realGame and segments[1] and segments[1][1] == "Players" and segments[2] then
		local named = playersService:FindFirstChild(segments[2][1])
		if named and named:IsA("Player") then
			segments[2] = { "@uid:" .. tostring(named.UserId), 1 }
		end
	end

	if current == realGame then
		return { root = "game", path = segments }
	end
	if current == serverRoot then
		return { root = "sse", path = segments }
	end
	if current == moduleHolder then
		return { root = "mod", path = segments }
	end
	return nil
end

---Resolve a path made by encodePath.
---@param data table
---@return Instance?
local function decodePath(data)
	if type(data) ~= "table" or type(data.path) ~= "table" then
		return nil
	end

	local rootKind = data.root
	local current = (rootKind == "sse" and serverRoot) or (rootKind == "mod" and moduleHolder) or realGame
	-- Ezproxy iç konteynerlerinde (serverRoot / moduleHolder) replica'nın ağacında aynı Folder'lar
	-- yoksa otomatik oluştur: hub oraya parça saklamışsa path kayıp olmasın.
	local autoCreate = rootKind == "sse" or rootKind == "mod"
	-- MIRROR GUI'S: Players.<X>.PlayerGui/Backpack/StarterGear path'leri replica tarafında kendi
	-- localPlayer'ımıza çözülür. Origin'in GUI'si replica'nın kendi PlayerGui'sinde görünür.
	-- Character ise yine origin'in gerçek karakterine çözülür (gear/accessory görünürlüğü için).
	local prevPlayer = nil
	for index, segment in ipairs(data.path) do
		local seen = 0
		local found
		-- @uid:<id> = origin'in UserId'si; replica aynı oyuncuyu bulur, yoksa LocalPlayer fallback.
		if type(segment[1]) == "string" and segment[1]:sub(1, 5) == "@uid:" and current == playersService then
			local uid = tonumber(segment[1]:sub(6))
			if uid then
				local byId = playersService:GetPlayerByUserId(uid)
				found = byId or localPlayer
				prevPlayer = found
			end
		elseif segment[1] == "*" and current == playersService then
			found = localPlayer
			prevPlayer = found
		end
		-- Full-convert mode: PlayerGui/Backpack/StarterGear/PlayerScripts yönlendirilmez. Her
		-- client kendi convert'inden kendi GUI/tool'una sahip; cross-client mirror sadece
		-- Character altındaki görünür gear'ı taşır.
		for _, child in ipairs(found and {} or current:GetChildren()) do
			if child.Name == segment[1] then
				seen = seen + 1
				if seen == segment[2] then
					found = child
					break
				end
			end
		end
		if not found then
			-- Path son segment olmayan bir ara klasör ise ve Ezproxy iç ağacındaysak eksik Folder'ı yarat.
			if autoCreate and index < #data.path and type(segment[1]) == "string" and segment[1]:sub(1, 1) ~= "@" then
				local folder = realInstance.new("Folder")
				folder.Name = segment[1]
				folder.Parent = current
				pcall(folder.SetAttribute, folder, SOURCE_TAG, true)
				pcall(folder.SetAttribute, folder, REPLICA_ATTRIBUTE, true)
				found = folder
			else
				return nil
			end
		end
		current = found
	end
	return current
end

---Encode one value for transport, nil when it cannot travel.
---@param value any
---@param depth number
---@return any
local function encodeValue(value, depth)
	if depth > MAX_ENCODE_DEPTH then
		return nil
	end

	local kind = realTypeof(value)
	if kind == "boolean" or kind == "string" then
		return value
	elseif kind == "number" then
		if value ~= value or value == math.huge or value == -math.huge then
			return { t = "num", s = tostring(value) }
		end
		return value
	elseif kind == "Vector3" then
		return { t = "v3", x = value.X, y = value.Y, z = value.Z }
	elseif kind == "Vector2" then
		return { t = "v2", x = value.X, y = value.Y }
	elseif kind == "CFrame" then
		return { t = "cf", c = { value:GetComponents() } }
	elseif kind == "Color3" then
		return { t = "c3", r = value.R, g = value.G, b = value.B }
	elseif kind == "BrickColor" then
		return { t = "bc", n = value.Number }
	elseif kind == "EnumItem" then
		return { t = "enum", e = tostring(value.EnumType), n = value.Name }
	elseif kind == "TweenInfo" then
		return { t = "ti", time = value.Time, style = value.EasingStyle.Name, dir = value.EasingDirection.Name,
			rep = value.RepeatCount, rev = value.Reverses, delay = value.DelayTime }
	elseif kind == "UDim2" then
		return { t = "u2", xs = value.X.Scale, xo = value.X.Offset, ys = value.Y.Scale, yo = value.Y.Offset }
	elseif kind == "UDim" then
		return { t = "u1", s = value.Scale, o = value.Offset }
	elseif kind == "Rect" then
		return { t = "rect", xmin = value.Min.X, ymin = value.Min.Y, xmax = value.Max.X, ymax = value.Max.Y }
	elseif kind == "NumberRange" then
		return { t = "nr", mn = value.Min, mx = value.Max }
	elseif kind == "NumberSequence" then
		local pts = {}
		for _, kp in ipairs(value.Keypoints) do
			table.insert(pts, { t = kp.Time, v = kp.Value, e = kp.Envelope })
		end
		return { t = "ns", k = pts }
	elseif kind == "ColorSequence" then
		local pts = {}
		for _, kp in ipairs(value.Keypoints) do
			table.insert(pts, { t = kp.Time, r = kp.Value.R, g = kp.Value.G, b = kp.Value.B })
		end
		return { t = "cs", k = pts }
	elseif kind == "Axes" then
		return { t = "ax", v = { value.Top, value.Bottom, value.Left, value.Right, value.Front, value.Back } }
	elseif kind == "Faces" then
		return { t = "fc", v = { value.Top, value.Bottom, value.Left, value.Right, value.Front, value.Back } }
	elseif kind == "PhysicalProperties" then
		return { t = "pp", d = value.Density, fr = value.Friction, el = value.Elasticity,
			fw = value.FrictionWeight, ew = value.ElasticityWeight }
	elseif kind == "Font" then
		local family = (value.Family ~= nil and tostring(value.Family)) or "rbxasset://fonts/families/SourceSansPro.json"
		local weight = value.Weight and tostring(value.Weight.Name) or "Regular"
		local style = value.Style and tostring(value.Style.Name) or "Normal"
		return { t = "ft", f = family, w = weight, s = style }
	elseif kind == "Content" or kind == "ContentId" then
		-- WHITE FIX: Content userdata never travels. Its string form cleared TextureID/MeshId on the
		-- other side (everything white); the string twins (MeshId, TextureID, ColorMap) carry the asset.
		if config.mirrorContent ~= true then
			return nil
		end
		-- Yeni Content userdata (MeshContent / TextureContent / Decal.Texture / SurfaceAppearance.ColorMap).
		-- Birden fazla Roblox sürümüne karşı dayanıklı: Uri, SourceId, Url, tostring hepsi denenir.
		local uri
		for _, key in ipairs({ "Uri", "SourceId", "Url", "Value" }) do
			local ok, got = pcall(function() return value[key] end)
			if ok and type(got) == "string" and got ~= "" then
				uri = got
				break
			end
		end
		if type(uri) ~= "string" then
			-- tostring Content userdata'da "Content<id>" dönebilir, içinden rbxassetid URL'i ayıklanır.
			local text = tostring(value)
			if type(text) == "string" then
				local extracted = text:match("rbxassetid://%d+") or text:match("rbxasset://[^%s%)]+")
					or text:match("https?://[^%s%)]+")
				uri = extracted or text
			end
		end
		return { t = "ct", u = uri or "" }
	elseif kind == "Instance" then
		if value:IsA("Player") then
			return { t = "plr", id = value.UserId, name = value.Name }
		end
		local ok, path = pcall(encodePath, value)
		if ok and path then
			return { t = "inst", p = path }
		end
		return nil
	elseif kind == "table" then
		if fakeObjects[value] then
			return { t = "plr", id = value.UserId, name = value.Name }
		end
		if proxyTargets[value] then
			return encodeValue(proxyTargets[value], depth + 1)
		end

		local entries = {}
		for key, item in pairs(value) do
			local encodedKey = encodeValue(key, depth + 1)
			local encodedItem = encodeValue(item, depth + 1)
			if encodedKey ~= nil and encodedItem ~= nil then
				table.insert(entries, { k = encodedKey, v = encodedItem })
			end
		end
		return { t = "tbl", e = entries }
	end
	return nil
end

---Decode a value made by encodeValue.
---@param value any
---@return any
local function decodeValue(value)
	if type(value) ~= "table" then
		return value
	end

	local kind = value.t
	if kind == "num" then
		local text = tostring(value.s)
		if text:find("nan", 1, true) then
			return 0 / 0
		end
		if text:sub(1, 1) == "-" then
			return -math.huge
		end
		return math.huge
	elseif kind == "v3" then
		return Vector3.new(value.x, value.y, value.z)
	elseif kind == "v2" then
		return Vector2.new(value.x, value.y)
	elseif kind == "cf" then
		return CFrame.new(table.unpack(value.c))
	elseif kind == "c3" then
		return Color3.new(value.r, value.g, value.b)
	elseif kind == "bc" then
		return BrickColor.new(value.n)
	elseif kind == "enum" then
		local ok, item = pcall(function()
			return Enum[value.e][value.n]
		end)
		return ok and item or nil
	elseif kind == "u2" then
		return UDim2.new(value.xs, value.xo, value.ys, value.yo)
	elseif kind == "u1" then
		return UDim.new(value.s, value.o)
	elseif kind == "ti" then
		local okInfo, info = pcall(function()
			return TweenInfo.new(tonumber(value.time) or 1, Enum.EasingStyle[value.style or "Quad"],
				Enum.EasingDirection[value.dir or "Out"], tonumber(value.rep) or 0, value.rev == true,
				tonumber(value.delay) or 0)
		end)
		return okInfo and info or nil
	elseif kind == "rect" then
		return Rect.new(value.xmin, value.ymin, value.xmax, value.ymax)
	elseif kind == "nr" then
		if value.mn == value.mx then return NumberRange.new(value.mn) end
		return NumberRange.new(value.mn, value.mx)
	elseif kind == "ns" then
		local pts = {}
		for _, kp in ipairs(value.k or {}) do
			table.insert(pts, NumberSequenceKeypoint.new(kp.t, kp.v, kp.e or 0))
		end
		return NumberSequence.new(pts)
	elseif kind == "cs" then
		local pts = {}
		for _, kp in ipairs(value.k or {}) do
			table.insert(pts, ColorSequenceKeypoint.new(kp.t, Color3.new(kp.r, kp.g, kp.b)))
		end
		return ColorSequence.new(pts)
	elseif kind == "ax" then
		local v = value.v
		return Axes.new(table.unpack({
			v[1] and Enum.NormalId.Top or nil, v[2] and Enum.NormalId.Bottom or nil,
			v[3] and Enum.NormalId.Left or nil, v[4] and Enum.NormalId.Right or nil,
			v[5] and Enum.NormalId.Front or nil, v[6] and Enum.NormalId.Back or nil,
		}))
	elseif kind == "fc" then
		local v = value.v
		return Faces.new(table.unpack({
			v[1] and Enum.NormalId.Top or nil, v[2] and Enum.NormalId.Bottom or nil,
			v[3] and Enum.NormalId.Left or nil, v[4] and Enum.NormalId.Right or nil,
			v[5] and Enum.NormalId.Front or nil, v[6] and Enum.NormalId.Back or nil,
		}))
	elseif kind == "pp" then
		return PhysicalProperties.new(value.d, value.fr, value.el, value.fw or 1, value.ew or 1)
	elseif kind == "ft" then
		local okFont, font = pcall(function()
			return Font.new(value.f, Enum.FontWeight[value.w or "Regular"], Enum.FontStyle[value.s or "Normal"])
		end)
		return okFont and font or nil
	elseif kind == "ct" then
		-- Content tipi: dönüşte string ver, hem eski (ContentId) hem yeni (Content) property'ler kabul eder.
		return value.u or ""
	elseif kind == "inst" then
		return decodePath(value.p)
	elseif kind == "plr" then
		local player = playersService:GetPlayerByUserId(value.id)
		if player then
			return player
		end
		for _, fake in ipairs(SSEmu.getFakePlayers()) do
			if fake.UserId == value.id or fake.Name == value.name then
				return fake
			end
		end
		return nil
	elseif kind == "tbl" then
		local result = {}
		for _, entry in ipairs(value.e or {}) do
			local key = decodeValue(entry.k)
			if key ~= nil then
				result[key] = decodeValue(entry.v)
			end
		end
		return result
	end
	return nil
end

---Encode a vararg list, holes included.
---@return table
local function encodeArgs(...)
	local packed = table.pack(...)
	local list = {}
	for index = 1, packed.n do
		local encoded = encodeValue(packed[index], 0)
		if encoded ~= nil then
			table.insert(list, { i = index, v = encoded })
		end
	end
	return { n = packed.n, list = list }
end

---Decode a list made by encodeArgs.
---@param encoded table
---@return table
local function decodeArgs(encoded)
	local args = { n = encoded.n or 0 }
	for _, entry in ipairs(encoded.list or {}) do
		args[entry.i] = decodeValue(entry.v)
	end
	return args
end

---Send a remote call to the other clients, they run their copy of the server logic.
---@param data table
---@param method string
---@param target number? UserId of the client a FireClient call is aimed at.
function SSEmu.replicateRemote(data, method, target, ...)
	if not replication.enabled or not data.inst then
		return
	end
	local ok, path = pcall(encodePath, data.inst)
	-- The mirror id finds the very same remote on every client (a path can differ in sibling order).
	local sid = SSEmu.remoteSid and SSEmu.remoteSid(data.inst) or nil
	if (not ok or not path) and not sid then
		return
	end
	SSEmu.replicate("remote", {
		path = ok and path or nil,
		sid = sid,
		method = method,
		target = target,
		args = encodeArgs(...),
		_from = { userId = localPlayer.UserId, name = localPlayer.Name },
	})
end

---RemoteFunction:InvokeServer on another client's remote: the call goes to its owner, whose
---OnServerInvoke runs with us as the player, and the results come back. Returns handled, results.
---@param data table
---@return boolean, table?
function SSEmu.remoteInvoke(data, ...)
	if not (replication.enabled and replication.connected) or not SSEmu.remoteSid then
		return false
	end
	local sid, own = SSEmu.remoteSid(data.inst)
	if not sid or own then
		return false
	end
	SSEmu.invokeCounter = (SSEmu.invokeCounter or 0) + 1
	local requestId = tostring(localPlayer.UserId) .. ":" .. SSEmu.invokeCounter
	SSEmu.pendingInvokes = SSEmu.pendingInvokes or {}
	local pending = { done = false }
	SSEmu.pendingInvokes[requestId] = pending
	SSEmu.replicate("remote", {
		sid = sid, method = "InvokeServer", requestId = requestId,
		args = encodeArgs(...), _from = { userId = localPlayer.UserId, name = localPlayer.Name },
	})
	-- Same 10s patience the engine roughly has before a script gives up on a server.
	local deadline = os.clock() + 10
	while not pending.done and os.clock() < deadline do
		task.wait(0.03)
	end
	SSEmu.pendingInvokes[requestId] = nil
	if not pending.done then
		log("InvokeServer: no answer from the remote's owner within 10s", WARN_COLOR)
		return true, { n = 0 }
	end
	return true, pending.results
end

-- ═══════════════════════════════════════════════════════════════════
-- WORLD MIRROR: what the origin's scripts do to the world reaches the other clients as instance
-- state (like FE disabled) instead of every client running its own copy of the script.
-- Origin side: instances a script puts into Workspace are tracked, their property writes, physics
-- motion and Destroy/PivotTo calls are batched and pushed. Replica side: the same instances are
-- rebuilt as anchored, replica tagged copies and kept in step.
-- Disable with shared.SSEmuConfig.mirror = false or /mirror off (old behaviour: replicas run scripts).
-- ═══════════════════════════════════════════════════════════════════

local SYNC_ID_ATTRIBUTE = "_sse_sid"
local SYNC_OPS_PER_PUSH = 150
local SYNC_MAX_TRACKED = 2500
local SYNC_DEFER_LIMIT = 30
local SYNC_SKIP_CLASSES = { Script = true, LocalScript = true, ModuleScript = true, Terrain = true, Camera = true }
local SYNC_POSITION_KEYS = { Position = true, Orientation = true, Rotation = true, CFrame = true }
-- Velocity only travels for real instances (a fling of another player's character), mirrored copies are anchored.
local SYNC_VELOCITY_KEYS = { AssemblyLinearVelocity = true, AssemblyAngularVelocity = true, Velocity = true, RotVelocity = true }
local SYNC_TOUCH_COOLDOWN = 0.25
local SYNC_DRIVE_RATE = 0.05
-- Read only, derived or noisy properties, never worth a trip.
local SYNC_SKIP_PROPERTIES = {
	Parent = true, ClassName = true, Archivable = true, Mass = true, AssemblyMass = true,
	Throttle = true, Steer = true, ThrottleFloat = true, SteerFloat = true, AssemblyCenterOfMass = true, CenterOfMass = true, ExtentsSize = true, AbsoluteSize = true,
	AbsolutePosition = true, AbsoluteRotation = true, MoveDirection = true, FloorMaterial = true,
	SeatPart = true, Jump = true, CameraOffset = true, TargetPoint = true, RootPart = true,
	WorldPivot = true, ReceiveAge = true, Occupant = true, PlaybackLoudness = true, TimeLength = true,
	IsPlaying = true, IsPaused = true, IsLoaded = true, Origin = true, Magnitude = true,
}
-- Snapshot of a freshly added instance, read with pcall so a property a class lacks is skipped.
-- FULL FE-DISABLED: every visual, physical and audio property that can diverge between clients.
local SYNC_PROPERTIES = {
	-- Core.
	"Name", "CFrame", "Size", "Color", "Color3", "Material", "Transparency", "Reflectance", "Anchored",
	"CanCollide", "CanTouch", "CanQuery", "CastShadow", "Shape", "Locked", "Massless", "TopSurface",
	"BottomSurface", "LeftSurface", "RightSurface", "FrontSurface", "BackSurface",
	"CollisionGroup", "CollisionGroupId", "RootPriority", "PivotOffset", "EnableFluidForces",
	-- MeshPart / SpecialMesh / FileMesh / BlockMesh / CylinderMesh.
	"MeshId", "TextureId", "TextureID", "Texture", "Scale", "Offset", "MeshType",
	"VertexColor", "DoubleSided", "RenderFidelity",
	-- SurfaceAppearance (PBR).
	"ColorMap", "NormalMap", "MetalnessMap", "RoughnessMap", "AlphaMode", "UsePartColor",
	-- MaterialVariant.
	"BaseMaterial", "MaterialPattern", "StudsPerTile",
	-- Decal / Texture.
	"Face", "StudsPerTileU", "StudsPerTileV", "OffsetStudsU", "OffsetStudsV", "ZIndexBehavior",
	-- Light.
	"Brightness", "Range", "Enabled", "Shadows", "Angle", "LightEmission", "LightInfluence",
	"InnerAngle", "OuterAngle",
	-- Humanoid.
	"Health", "MaxHealth", "DisplayName", "WalkSpeed", "JumpPower", "JumpHeight", "HipHeight",
	"RigType", "AutoRotate", "AutomaticScalingEnabled", "RequiresNeck", "BreakJointsOnDeath",
	"EvaluateStateMachine", "HealthDisplayType", "NameDisplayDistance", "HealthDisplayDistance",
	"CameraOffset",
	-- Welds / Motors / Constraints.
	"Part0", "Part1", "C0", "C1", "Attachment0", "Attachment1", "PrimaryPart", "WorldPivot",
	"MaxForce", "MaxTorque", "Responsiveness", "RotationType", "Position", "Visible",
	"TargetPosition", "TargetAngle", "LimitsEnabled", "UpperAngle", "LowerAngle",
	"MotorMaxTorque", "MotorMaxAngularAcceleration",
	-- UI / Gui.
	"Adornee", "StudsOffset", "AlwaysOnTop", "MaxDistance", "SizeOffset", "StudsOffsetWorldSpace",
	"Text", "TextColor3", "TextSize", "TextScaled", "TextStrokeTransparency", "TextStrokeColor3",
	"TextTransparency", "Font", "FontFace", "RichText", "LineHeight", "TextWrapped",
	"BackgroundColor3", "BackgroundTransparency", "BorderSizePixel", "BorderColor3", "BorderMode",
	"ZIndex", "Rotation", "AnchorPoint", "AutomaticSize", "ClipsDescendants",
	"Image", "ImageColor3", "ImageTransparency", "ImageRectOffset", "ImageRectSize",
	"ScaleType", "SliceCenter", "SliceScale", "TileSize", "ResampleMode",
	-- Audio.
	"SoundId", "Volume", "Playing", "Looped", "PlaybackSpeed", "RollOffMinDistance",
	"RollOffMaxDistance", "RollOffMode", "SoundGroup", "TimePosition",
	-- Values.
	"Value",
	-- ParticleEmitter / Trail / Beam / Smoke / Fire / Sparkles / Explosion.
	"Heat", "Rate", "Opacity", "RiseVelocity", "SparkleColor", "FillColor", "OutlineColor",
	"FillTransparency", "OutlineTransparency",
	"Disabled", "Style", "Thickness", "Radius", "Height", "Width", "Length", "Axis",
	"WorldPivotOverride", "ActionText", "ObjectText", "HoldDuration",
	"RequiresLineOfSight", "KeyboardKeyCode", "Speed", "Steer", "Throttle", "MaxSpeed", "Torque",
	"TurnSpeed", "Decoration",
	"BlastRadius", "BlastPressure", "DestroyJointRadiusPercent", "ExplosionType",
	"ZOffset", "LockedToPart", "Lifetime", "SpreadAngle", "Acceleration", "Drag", "Squash",
	"Faces", "PlaneOffset", "EmissionDirection", "Orientation", "FlipbookFramerate",
	"FlipbookLayout", "FlipbookMode", "ShapeStyle", "ShapePartial", "ShapeInOut",
	"TimeScale", "TextureMode", "LightEmission",
	-- Attachment.
	"WorldPosition", "WorldAxis", "WorldSecondaryAxis", "WorldOrientation",
	-- Sky / Atmosphere / Clouds / Bloom / Blur / ColorCorrection / DepthOfField / SunRays.
	"SkyboxBk", "SkyboxDn", "SkyboxFt", "SkyboxLf", "SkyboxRt", "SkyboxUp",
	"SunTextureId", "MoonTextureId", "StarCount", "CelestialBodiesShown",
	"Density", "Haze", "Glare", "Decay", "Contrast", "Saturation", "TintColor",
	"Intensity", "Spread", "Threshold",
	"Cover", "Color", "Density", "CoverShape",
	-- Accessory / Hat / Clothing.
	"AttachmentForward", "AttachmentPoint", "AttachmentPos", "AttachmentRight", "AttachmentUp",
	"AccessoryType", "ShirtTemplate", "PantsTemplate", "Graphic",
	"HeadColor3", "LeftArmColor3", "RightArmColor3", "TorsoColor3", "LeftLegColor3", "RightLegColor3",
	-- BodyMover (legacy).
	"Velocity", "MaxForce", "D", "P",
	-- Camera (per-user cosmetic).
	"FieldOfView", "FocalDistance",
	-- Teams and team spawns.
	"TeamColor", "AutoAssignable", "Neutral", "AllowTeamChangeOnTouch", "Duration",
}

-- Lighting + its postprocess children: every property that changes the look of the world.
local LIGHTING_PROPERTIES = {
	"Ambient", "Brightness", "ColorShift_Bottom", "ColorShift_Top", "OutdoorAmbient",
	"ClockTime", "GeographicLatitude", "TimeOfDay",
	"EnvironmentDiffuseScale", "EnvironmentSpecularScale", "ExposureCompensation",
	"FogColor", "FogEnd", "FogStart", "GlobalShadows", "Technology",
	"ShadowSoftness", "LightingStyle",
}

-- FilteringEnabled off: every change a client makes to Workspace / Lighting reaches the others, not only
-- what the sandbox scripts make. scope "executor" = executor + sandbox threads, "all" = game LocalScripts too.
local FE_SKIP_PROPERTIES = { LocalTransparencyModifier = true }
-- FULL FE-DISABLED: journal'ı pratik olarak sınırsıza çıkar (büyük hub'lar binlerce sunucu
-- instance'ı değiştirir, geç bağlanan replica hepsini almak zorunda).
local FE_JOURNAL_LIMIT = 250000
local FE_JOURNAL_METHODS = {
	Destroy = true, Remove = true, ClearAllChildren = true, BreakJoints = true, PivotTo = true,
	SetPrimaryPartCFrame = true, MoveTo = true, TranslateBy = true, SetAttribute = true,
}
local lightingService = realGame:GetService("Lighting")
-- FULL FE-DISABLED: Teams + StarterPack + StarterPlayer mirror scope'a dahil edilir.
local teamsService = realGame:GetService("Teams")
local starterPackService = realGame:GetService("StarterPack")
local starterPlayerService = realGame:GetService("StarterPlayer")
local isDescendantOfFn = realGame.IsDescendantOf
local fe = {
	-- FULL FE-DISABLED default: FilteringEnabled is off from boot, scope "all" (every client's world
	-- changes replicate). Re-enable normal filtering with shared.SSEmuConfig.filteringEnabled = true or
	-- the proxy .fe enable command. A standalone converted build keeps normal filtering (no relay).
	off = config.filteringEnabled ~= false and config.noProxy ~= true,
	-- FULL FE-DISABLED default: filteringEnabled=false denince scope "executor" değil, en güçlü
	-- mod olan "all" devreye girer (game LocalScript'leri dahil her değişim replike).
	-- Eski davranış için shared.SSEmuConfig.feScope = "executor" verilebilir.
	scope = (config.feScope == "executor") and "executor" or "all",
	created = setmetatable({}, { __mode = "k" }),
	journal = {},
	journalIndex = {},
	newHooked = false,
	-- "mirror" (default): only the origin runs commands, everything it makes streams to the others,
	-- the same object in the same place (real replication, what filming needs).
	-- "convert": every client runs .require/.give/.load itself, the mirror only carries cross-player
	-- state (equipped gear, damage, team, .exec content).
	mode = config.feMode == "convert" and "convert" or "mirror",
}
SSEmu.feMode = fe.mode
SSEmu.diagStats = { sent = 0, received = 0, pushErrors = 0, applyErrors = 0, lastError = "none" }



---True when every client builds this instance itself (convert mode), so mirroring it would duplicate it.
---@param inst Instance
---@return boolean
local function isDispatchedContent(inst)
	if fe.mode ~= "convert" then
		return false
	end
	local ok, origin = pcall(inst.GetAttribute, inst, ORIGIN_ATTRIBUTE)
	if not (ok and type(origin) == "string") then
		return false
	end
	-- Origin prefix prepareAsset gives content of a command the proxy broadcast to every client.
	return origin:sub(1, 9) == "dispatch:"
end
local fixAnchor

-- State.
local sync = {
	enabled = config.mirror ~= false,
	applying = false,
	running = false,
	count = 0,
	counter = 0,
	refCounter = 0,
	tracked = setmetatable({}, { __mode = "k" }),
	refKeys = setmetatable({}, { __mode = "k" }),
	lastCFrame = setmetatable({}, { __mode = "k" }),
	ownById = setmetatable({}, { __mode = "v" }),
	originAnchored = setmetatable({}, { __mode = "k" }),
	touchTimes = setmetatable({}, { __mode = "k" }),
	lastDrive = nil,
	lastDriveAt = 0,
	echo = setmetatable({}, { __mode = "k" }),
	byId = {},
	ops = {},
	opIndex = {},
	deferred = {},
	-- Latest Size / Scale the origin sent per mirrored instance, the guards hold exactly this.
	sizeTargets = setmetatable({}, { __mode = "k" }),
	scaleTargets = setmetatable({}, { __mode = "k" }),
	-- Latest encoded value per instance and property, re-applies never restore a stale one.
	latest = setmetatable({}, { __mode = "k" }),
}

---One line on the mirror's health, for the .diag console command.
---@return string
function SSEmu.diagReport()
	local stats = SSEmu.diagStats
	local tracked = 0
	for _ in pairs(sync.tracked) do
		tracked = tracked + 1
	end
	local sources, ready = 0, 0
	for _, entry in pairs(sync.cloneSources or {}) do
		sources = sources + 1
		if entry.state == "ready" then
			ready = ready + 1
		end
	end
	return string.format(
		"replication %s (%s) | mirror %s | FE %s scope %s mode %s | tracked %d | queued %d | sent %d | received %d | push errors %d | apply errors %d | exact sources %d/%d ready | last error: %s",
		replication.enabled and "on" or "OFF", replication.connected and "connected" or "NOT connected",
		sync.enabled and "on" or "OFF", fe.off and "disabled" or "enabled", fe.scope, fe.mode,
		tracked, #sync.ops, stats.sent, stats.received, stats.pushErrors, stats.applyErrors,
		ready, sources, stats.lastError)
end

---Encode a UDim/UDim2 or defer to the remote encoder.
---@param value any
---@return any
local function encodeSyncValue(value)
	local kind = realTypeof(value)
	if kind == "UDim2" then
		return { t = "u2", xs = value.X.Scale, xo = value.X.Offset, ys = value.Y.Scale, yo = value.Y.Offset }
	elseif kind == "UDim" then
		return { t = "u1", s = value.Scale, o = value.Offset }
	elseif kind == "Instance" then
		local entry = sync.tracked[value]
		if entry then
			return { t = "sid", id = entry.id }
		end
		local okId, sid = pcall(value.GetAttribute, value, SYNC_ID_ATTRIBUTE)
		if okId and type(sid) == "string" and sync.byId[sid] == value then
			return { t = "sid", id = sid }
		end
	end
	return encodeValue(value, 0)
end

---Decode a value made by encodeSyncValue.
---@param value any
---@return any
local function decodeSyncValue(value)
	if type(value) ~= "table" then
		return value
	end
	if value.t == "u2" then
		return UDim2.new(value.xs, value.xo, value.ys, value.yo)
	elseif value.t == "u1" then
		return UDim.new(value.s, value.o)
	elseif value.t == "sid" then
		-- A mirrored copy here, or our own original when another client refers back to it.
		return sync.byId[value.id] or sync.ownById[value.id]
	end
	return decodeValue(value)
end

---Reference to a world instance: its mirror id when tracked, its path in the game tree otherwise.
---@param inst Instance?
---@return table?
local function syncRef(inst)
	if realTypeof(inst) ~= "Instance" then
		return nil
	end
	local encoded = encodeSyncValue(inst)
	if type(encoded) == "table" and (encoded.t == "sid" or (encoded.t == "inst" and encoded.p.root == "game")) then
		return encoded
	end
	return nil
end

---Coalescing key of an untracked instance, so repeated writes of one property collapse into one op.
---@param inst Instance
---@return string
local function refKeyOf(inst)
	local key = sync.refKeys[inst]
	if not key then
		sync.refCounter = sync.refCounter + 1
		key = "r" .. sync.refCounter
		sync.refKeys[inst] = key
	end
	return key
end

---Queue an op, replacing an earlier op with the same key (last write wins inside a batch).
---@param key string?
---@param op table
local function pushOp(key, op)
	-- The key rides on the op so ops held back by the flush budget keep coalescing.
	op._key = key
	local index = key and sync.opIndex[key]
	if index then
		sync.ops[index] = op
		return
	end
	table.insert(sync.ops, op)
	if key then
		sync.opIndex[key] = #sync.ops
	end
end

---Whether an instance sits where world changes travel: Workspace, plus Workspace / Lighting themselves
---and Lighting's children while FilteringEnabled is off.
---@param inst Instance
---@return boolean
-- TOTAL FilteringDisabled scope: Roblox'un mirror edilmeye değer tüm servisleri.
-- Native map içeriği (SOURCE_TAG'siz) burada bile mirror'a girmez; sadece hub/script'in oluşturduğu
-- tagged content gider → lag yok.
local MIRROR_SERVICES = nil
local function getMirrorServices()
	if MIRROR_SERVICES then return MIRROR_SERVICES end
	MIRROR_SERVICES = {}
	local names = {
		"Teams", "Lighting", "StarterPack", "StarterPlayer", "StarterGui",
		"ReplicatedStorage", "ReplicatedFirst", "SoundService", "Chat", "TextChatService",
		"MaterialService", "InsertService", "MarketplaceService", "BadgeService",
		"PhysicsService", "Debris", "CollectionService", "HttpService",
	}
	for _, name in ipairs(names) do
		local okSvc, svc = pcall(realGame.GetService, realGame, name)
		if okSvc and svc then MIRROR_SERVICES[svc] = true end
	end
	return MIRROR_SERVICES
end

local function inScope(inst)
	local ok, result = pcall(function()
		-- Ezproxy iç konteynerleri + Workspace her zaman kapsam içinde.
		if inst == serverRoot or inst == serverScriptService or inst == serverStorage
			or inst == moduleHolder then
			return true
		end
		if isDescendantOfFn(inst, serverRoot) or isDescendantOfFn(inst, moduleHolder) then
			return true
		end
		if isDescendantOfFn(inst, workspaceService) then
			return true
		end
		-- PlayerGui/PlayerScripts/Backpack stay out (each client has its own).
		-- Teams, Lighting, StarterPack, StarterPlayer, ReplicatedStorage...: always in scope, FE disabled
		-- or not. Only script made (tagged) content ever travels from them, native content never.
		-- LAG FIX: one walk up to the top service instead of an IsDescendantOf per service.
		local services = getMirrorServices()
		local node = inst
		local depth = 0
		while node and depth < 64 do
			if services[node] then return true end
			local parent = node.Parent
			if parent == nil or parent == realGame then break end
			node = parent
			depth = depth + 1
		end
		return false
	end)
	return ok and result == true
end

---Whether a node or one of its ancestors is something that never travels (the camera, terrain).
---@param inst Instance
---@return boolean
local function inSkippedBranch(inst)
	local node = inst
	while node and node ~= workspaceService and node ~= lightingService do
		local okClass, className = pcall(function() return node.ClassName end)
		if okClass and (className == "Camera" or className == "Terrain") then
			return true
		end
		node = node.Parent
	end
	return false
end

---Whether an instance is part of a mirrored copy of another client's world content.
---@param inst Instance
---@return boolean
local function isReplicaContent(inst)
	local node = inst
	while node and node ~= workspaceService and node ~= lightingService do
		if isReplica(node) then
			return true
		end
		node = node.Parent
	end
	return false
end

---Whether an instance is inside a real player's character (characters replicate natively).
---@param inst Instance
---@return boolean, boolean
local function inCharacter(inst)
	local okModel, model = pcall(inst.FindFirstAncestorOfClass, inst, "Model")
	model = okModel and model or nil
	while model do
		local player = playersService:GetPlayerFromCharacter(model)
		if player then
			return true, player == localPlayer
		end
		model = model:FindFirstAncestorOfClass("Model")
	end
	return false, false
end

-- Karakter iskelet part'ları (R6 + R15 + body parça isimleri). Mirror'a girmez, çünkü Roblox
-- karakterleri zaten native replike eder; mirror'a atmak ağır lag yaratır.
local CHARACTER_LIMB_NAMES = {
	-- R6.
	HumanoidRootPart = true, Torso = true, Head = true,
	["Left Arm"] = true, ["Right Arm"] = true, ["Left Leg"] = true, ["Right Leg"] = true,
	-- R15.
	UpperTorso = true, LowerTorso = true,
	LeftUpperArm = true, LeftLowerArm = true, LeftHand = true,
	RightUpperArm = true, RightLowerArm = true, RightHand = true,
	LeftUpperLeg = true, LeftLowerLeg = true, LeftFoot = true,
	RightUpperLeg = true, RightLowerLeg = true, RightFoot = true,
}
local CHARACTER_ATTACH_NAMES = {
	-- Motor6D'ler ve karakter'in standart eklemleri.
	RootJoint = true, Neck = true, Waist = true,
	["Left Shoulder"] = true, ["Right Shoulder"] = true,
	["Left Hip"] = true, ["Right Hip"] = true,
	LeftShoulder = true, RightShoulder = true, LeftElbow = true, RightElbow = true,
	LeftWrist = true, RightWrist = true, LeftHip = true, RightHip = true,
	LeftKnee = true, RightKnee = true, LeftAnkle = true, RightAnkle = true,
}

---Karakter iskelet part'ı/joint'i mi: mirror atlanır (Roblox native replike eder).
---Humanoid, Animator, HumanoidDescription, BodyColors BU LİSTEDE DEĞİL — Humanoid.Health,
---WalkSpeed, state değişiklikleri vuruş/damage için mirror'dan gitmeli.
---@param inst Instance
---@return boolean
local function isNativeCharacterPart(inst)
	local okName, name = pcall(function() return inst.Name end)
	if not okName then return false end
	-- Sadece bedensel parça veya Motor6D eklem isimleri. Humanoid hariç.
	if not (CHARACTER_LIMB_NAMES[name] or CHARACTER_ATTACH_NAMES[name]) then
		return false
	end
	-- Direkt karakter modelinin child'ı mı (veya Motor6D case'inde limb içinde)?
	local okParent, parent = pcall(function() return inst.Parent end)
	if not (okParent and parent) then return false end
	for _ = 1, 2 do
		if parent and playersService:GetPlayerFromCharacter(parent) then
			return true
		end
		local okNext, next_ = pcall(function() return parent.Parent end)
		parent = okNext and next_ or nil
	end
	return false
end

---Whether a world instance belongs to the local emulation (not a mirrored copy of another client's).
---@param inst Instance
---@return boolean
local function isOwnWorldInstance(inst)
	if not inScope(inst) or inSkippedBranch(inst) then
		return false
	end
	-- Anything inside a mirrored copy (the seat weld we sit on) belongs to the copy's owner.
	return not isReplicaContent(inst)
end

---Keep an op that changed a real (server) instance, so a client joining later gets the same world.
---@param key string?
---@param op table
local function feRecord(key, op)
	if not fe.off then
		return
	end
	local index = key and fe.journalIndex[key]
	if index then
		fe.journal[index] = op
		return
	end
	if #fe.journal >= FE_JOURNAL_LIMIT then
		return warnRelayOnce("FE: more than " .. FE_JOURNAL_LIMIT .. " changes on server instances, late joiners miss the rest")
	end
	table.insert(fe.journal, op)
	if key then
		fe.journalIndex[key] = #fe.journal
	end
end

---Where an instance stood before a Parent write.
---@param inst Instance
---@return table
function SSEmu.feBefore(inst)
	local before = { inScope = inScope(inst) and not inSkippedBranch(inst) }
	if before.inScope then
		before.ref = syncRef(inst)
		before.foreign = isReplicaContent(inst)
		before.character = inCharacter(inst)
	end
	return before
end

---Full property snapshot of an instance for an add op.
---@param inst Instance
---@return table
local function snapshotInstance(inst, light)
	local props = {}
	local isPart = inst:IsA("BasePart")
	local seen = {}
	local function dump(list)
		for _, name in ipairs(list) do
			if not seen[name] and not (isPart and (name == "Position" or name == "Orientation"))
				and name:sub(-7) ~= "Content" then
				seen[name] = true
				local ok, value = pcall(function() return inst[name] end)
				if ok and value ~= nil and type(value) ~= "function" then
					local encoded = encodeSyncValue(value)
					if encoded ~= nil then
						table.insert(props, { k = name, v = encoded })
					end
				end
			end
		end
	end
	dump(SYNC_PROPERTIES)
	-- Lighting + alt servislerinin property'leri için ikinci bir geçiş.
	local okClass, className = pcall(function() return inst.ClassName end)
	if okClass and (className == "Lighting" or className == "Atmosphere" or className == "Sky"
		or className == "BloomEffect" or className == "BlurEffect" or className == "ColorCorrectionEffect"
		or className == "DepthOfFieldEffect" or className == "SunRaysEffect" or className == "Clouds") then
		dump(LIGHTING_PROPERTIES)
	end
	-- FULL COPY: when the executor can enumerate every property (getproperties), every property the
	-- list above misses is taken too, so a piece rebuilt from scratch is a full copy of the original.
	if type(getproperties) == "function" and not light then
		local okAll, all = pcall(getproperties, inst)
		if okAll and type(all) == "table" then
			local function take(name, value, haveValue)
				if type(name) ~= "string" or seen[name] or SYNC_SKIP_PROPERTIES[name] or FE_SKIP_PROPERTIES[name]
					or name == "Parent" or name == "ClassName" or name:sub(1, 1) == "_"
					or name:sub(-7) == "Content"
					or (isPart and (name == "Position" or name == "Orientation")) then
					return
				end
				seen[name] = true
				if not haveValue then
					local okRead, read = pcall(function() return inst[name] end)
					if not okRead then
						return
					end
					value = read
				end
				if value ~= nil and type(value) ~= "function" then
					local encoded = encodeSyncValue(value)
					if encoded ~= nil then
						table.insert(props, { k = name, v = encoded })
					end
				end
			end
			for key, value in pairs(all) do
				if type(key) == "string" then
					take(key, value, true)
				elseif type(value) == "string" then
					take(value, nil, false)
				end
			end
		end
	end
	-- FULL FE-DISABLED: user attribute'ları da gidiyor (hub'lar durum bilgisini orada tutuyor).
	local okAttrs, attrs = pcall(function() return inst:GetAttributes() end)
	if okAttrs and type(attrs) == "table" then
		local attrList = {}
		for name, value in pairs(attrs) do
			if type(name) == "string" and name:sub(1, 4) ~= "_sse" and name:sub(1, 3) ~= "_cv" then
				local encoded = encodeSyncValue(value)
				if encoded ~= nil then
					table.insert(attrList, { k = name, v = encoded })
				end
			end
		end
		if #attrList > 0 then
			table.insert(props, { k = "__attributes", v = { t = "attrs", list = attrList } })
		end
	end
	return props
end

---Queue one property of a world instance.
---@param inst Instance
---@param property string
local function queueSet(inst, property, executorCaller)
	if type(property) ~= "string" or SYNC_SKIP_PROPERTIES[property] or FE_SKIP_PROPERTIES[property] then
		return
	end
	-- KORUPSİYON FIX: karakter iskelet part'ı ve Humanoid'e DOĞRUDAN yazma YOK. Humanoid property'leri
	-- özel "humanoid" op'u ile gider (bkz. watchHumanoid). Native limb'ler native replike eder.
	if isNativeCharacterPart(inst) then
		return
	end
	local okClass, className = pcall(function() return inst.ClassName end)
	if okClass and (className == "Humanoid" or className == "Animator"
		or className == "HumanoidDescription" or className == "BodyColors") then
		return
	end
	local entry = sync.tracked[inst]
	local foreign = false
	if not entry and not isOwnWorldInstance(inst) then
		-- FE off: a change on another client's mirrored copy goes back to its owner and everyone else.
		if not (fe.off and inScope(inst) and isReplicaContent(inst)) then
			return
		end
		foreign = true
	end
	if SYNC_SKIP_CLASSES[inst.ClassName] then
		return
	end
	local isPart = inst:IsA("BasePart")
	if isPart and SYNC_POSITION_KEYS[property] then
		property = "CFrame"
	end
	-- A mirrored tween animates this property on the other clients already: its frames are not sent.
	local tweening = sync.tweening[inst]
	if tweening and tweening.props[property] then
		if os.clock() < tweening.untilClock then
			return
		end
		sync.tweening[inst] = nil
	end
	if fe.off and not entry and not foreign then
		local underCharacter, ownCharacter = inCharacter(inst)
		-- FULL FE-DISABLED: scope "all" karakter property'lerini de replicate eder (mesh, accessory,
		-- Humanoid.WalkSpeed, body colors, shirt/pants template, vb.). Sadece kendi gövdemizin CFrame /
		-- Velocity'si doğal olarak zaten replike oluyor, onlar skip.
		if underCharacter then
			if ownCharacter and (property == "CFrame" or SYNC_VELOCITY_KEYS[property]) then
				return
			end
			if fe.scope ~= "all" and executorCaller == false then
				return
			end
		end
	end
	local ref = entry and { t = "sid", id = entry.id } or syncRef(inst)
	if not ref then
		return
	end
	if (entry or foreign) and SYNC_VELOCITY_KEYS[property] then
		return
	end
	local ok, value = pcall(function() return inst[property] end)
	if not ok or type(value) == "function" then
		return
	end
	-- A value another client just set here comes back through Changed, it is not sent again.
	local echo = sync.echo[inst]
	if echo and echo[property] ~= nil then
		local applied = echo[property]
		echo[property] = nil
		if applied == value then
			return
		end
	end
	local encoded = encodeSyncValue(value)
	if value ~= nil and encoded == nil then
		return
	end
	if isPart and property == "CFrame" then
		sync.lastCFrame[inst] = value
	end
	local key = (entry and entry.id or refKeyOf(inst)) .. "|" .. property
	local op = { a = "set", ref = ref, k = property, v = encoded }
	pushOp(key, op)
	if not entry and not foreign then
		feRecord(key, op)
	end
end

local queueAdd

---Forget a tracked instance and tell the other clients to drop their copy.
---@param inst Instance
local function untrackInstance(inst, silent)
	local entry = sync.tracked[inst]
	if not entry then
		return
	end
	sync.tracked[inst] = nil
	sync.lastCFrame[inst] = nil
	sync.ownById[entry.id] = nil
	sync.count = sync.count - 1
	for _, connection in ipairs(entry.connections) do
		pcall(function() connection:Disconnect() end)
	end
	if not silent then
		pushOp(nil, { a = "remove", id = entry.id })
	end
end

---Start tracking one world instance: property changes and ancestry changes are queued from now on.
---@param inst Instance
---@return table
local function trackInstance(inst)
	sync.counter = sync.counter + 1
	local entry = { id = replication.clientId .. ":" .. sync.counter, connections = {} }
	sync.tracked[inst] = entry
	sync.ownById[entry.id] = inst
	sync.count = sync.count + 1
	pcall(inst.SetAttribute, inst, SYNC_ID_ATTRIBUTE, entry.id)

	local isValue = inst:IsA("ValueBase")
	pcall(function()
		table.insert(entry.connections, inst.Changed:Connect(function(property)
			if sync.applying or not sync.enabled then
				return
			end
			-- ValueBase.Changed carries the value, every other Changed carries the property name.
			queueSet(inst, isValue and "Value" or property)
		end))
	end)

	-- FULL FE-DISABLED: user attribute'ları Changed'te görünmez, ayrı sinyal lazım.
	pcall(function()
		table.insert(entry.connections, inst.AttributeChanged:Connect(function(name)
			if sync.applying or not sync.enabled or type(name) ~= "string" then
				return
			end
			if name:sub(1, 4) == "_sse" or name:sub(1, 3) == "_cv" then
				return
			end
			local ok, value = pcall(function() return inst:GetAttribute(name) end)
			if not ok then return end
			local ref = { t = "sid", id = entry.id }
			local op = {
				a = "set",
				ref = ref,
				k = "__attributes",
				v = { t = "attrs", list = { { k = name, v = encodeSyncValue(value) } } },
			}
			pushOp(entry.id .. "|attr|" .. name, op)
			if not isOwnWorldInstance(inst) then return end
			if fe.off then feRecord(entry.id .. "|attr|" .. name, op) end
		end))
	end)
	pcall(function()
		table.insert(entry.connections, inst.AncestryChanged:Connect(function(_, parent)
			if not sync.enabled or sync.tracked[inst] ~= entry then
				return
			end
			-- Another client already told everyone, only our bookkeeping follows.
			if sync.applying then
				if not parent or not inScope(inst) then
					untrackInstance(inst, true)
				end
				return
			end
			if not parent or not inScope(inst) then
				untrackInstance(inst)
				return
			end
			pushOp(entry.id .. "|parent", { a = "parent", id = entry.id, parent = syncRef(parent) })
		end))
	end)
	if inst:IsA("BasePart") then
		pcall(function() sync.lastCFrame[inst] = inst.CFrame end)
	end
	return entry
end

---EXACT COPY: for every piece of a tracked subtree that came from a shared source (an asset or an
---instance of the game), send a "clone" op. The other client clones that very source piece (meshes,
---unions, textures, everything 1:1), maps our ids onto the clone by address and swaps it in for the
---approximate rebuild. Pieces a script made itself keep the rebuild.
---@param root Instance
local function pushCloneOps(root)
	local okNodes, nodes = pcall(function() return root:GetDescendants() end)
	if not okNodes then
		return
	end
	table.insert(nodes, 1, root)
	for _, node in ipairs(nodes) do
		local entry = sync.tracked[node]
		local okSrc, src = pcall(node.GetAttribute, node, "_sse_src")
		local okKey, key = pcall(node.GetAttribute, node, "_sse_key")
		if entry and okSrc and type(src) == "string" and okKey and type(key) == "string" then
			-- Only the top of each same-source block gets an op, its descendants ride in its map.
			local parent = node.Parent
			local okP, parentSrc = pcall(function() return parent and parent:GetAttribute("_sse_src") end)
			local okPK, parentKey = pcall(function() return parent and parent:GetAttribute("_sse_key") end)
			local topOfBlock = not (sync.tracked[parent] and okP and parentSrc == src and okPK
				and type(parentKey) == "string" and key:sub(1, #parentKey + 1) == parentKey .. "/")
			if topOfBlock then
				local map = {}
				local okSub, sub = pcall(function() return node:GetDescendants() end)
				sub = okSub and sub or {}
				table.insert(sub, 1, node)
				for _, piece in ipairs(sub) do
					local pieceEntry = sync.tracked[piece]
					local okA, pieceSrc = pcall(piece.GetAttribute, piece, "_sse_src")
					local okB, pieceKey = pcall(piece.GetAttribute, piece, "_sse_key")
					if pieceEntry and okA and pieceSrc == src and okB and type(pieceKey) == "string"
						and (pieceKey == key or pieceKey:sub(1, #key + 1) == key .. "/") then
						table.insert(map, { id = pieceEntry.id, key = pieceKey })
					end
				end
				pushOp(nil, { a = "clone", src = src, key = key, id = entry.id, map = map })
			end
		end
	end
end

---Mirror id of a remote: ours when we track it (we own it), the one our copy carries otherwise.
---@param inst Instance
---@return string?, boolean
function SSEmu.remoteSid(inst)
	local entry = sync.tracked[inst]
	if entry then
		return entry.id, true
	end
	local ok, sid = pcall(inst.GetAttribute, inst, SYNC_ID_ATTRIBUTE)
	if ok and type(sid) == "string" then
		return sid, sync.ownById[sid] == inst
	end
	return nil, false
end

---The remote a mirror id points at here: our own original, or our copy of someone else's.
---@param sid string
---@return Instance?, boolean
function SSEmu.remoteBySid(sid)
	local own = sync.ownById[sid]
	if own then
		return own, true
	end
	return sync.byId[sid], false
end

---Origin side: once the engine has welded an equipped emulated tool into our hand, send that grip
---(which limb, C0, C1) so the other clients weld their copy of the tool to the same hand.
---@param tool Instance
function SSEmu.sendGrip(tool)
	-- The engine makes the grip weld a frame or two after the equip.
	for _ = 1, 40 do
		if not (active and sync.enabled and replication.enabled) then
			return
		end
		local character = localPlayer.Character
		if not (character and tool.Parent == character) then
			return
		end
		local handle = tool:FindFirstChild("Handle")
		local toolEntry = sync.tracked[tool]
		local handleEntry = handle and sync.tracked[handle]
		if toolEntry and handleEntry then
			for _, node in ipairs(character:GetDescendants()) do
				local okJoint, limb, c0, c1 = pcall(function()
					if node:IsA("JointInstance") and node.Part1 == handle and node.Part0
						and not node.Part0:IsDescendantOf(tool) then
						return node.Part0, node.C0, node.C1
					end
					return nil
				end)
				if okJoint and limb then
					pushOp("grip|" .. toolEntry.id, {
						a = "grip", uid = localPlayer.UserId, handle = handleEntry.id,
						limb = limb.Name, c0 = encodeValue(c0, 0), c1 = encodeValue(c1, 0),
					})
					return
				end
			end
		end
		task.wait(0.05)
	end
end

---Another player picked up our dropped emulated tool: tell them to take it (with its source, so they
---get the real working tool), then remove ours. The remove op follows the pickup op, in order.
---@param tool Instance
---@param picker Player
---@return boolean
function SSEmu.handOver(tool, picker)
	if not (sync.enabled and replication.enabled and replication.connected) then
		return false
	end
	local okSrc, src = pcall(tool.GetAttribute, tool, "_sse_src")
	local okKey, key = pcall(tool.GetAttribute, tool, "_sse_key")
	local entry = sync.tracked[tool]
	pushOp(nil, {
		a = "pickup", uid = picker.UserId, name = tool.Name, id = entry and entry.id,
		src = (okSrc and type(src) == "string") and src or nil,
		key = (okKey and type(key) == "string") and key or nil,
	})
	log(picker.Name .. " picked up " .. tool.Name, INFO_COLOR)
	task.defer(function()
		pcall(function() tool:Destroy() end)
	end)
	return true
end

-- ═══ Tweens: one op per Play instead of a property stream ═══
SSEmu.tweenService = realGame:GetService("TweenService")
SSEmu.tweens = setmetatable({}, { __mode = "k" })
sync.tweening = setmetatable({}, { __mode = "k" })
sync.tweenCounter = 0

---Remember a tween made on a world instance (from TweenService:Create in the namecall hook).
---@param tween Instance
---@param target Instance
---@param info TweenInfo
---@param goals table
function SSEmu.onTweenCreated(tween, target, info, goals)
	if realTypeof(tween) ~= "Instance" or realTypeof(target) ~= "Instance" or type(goals) ~= "table" then
		return
	end
	if not (inScope(target) and not inSkippedBranch(target)) or isNativeCharacterPart(target) then
		return
	end
	sync.tweenCounter = sync.tweenCounter + 1
	SSEmu.tweens[tween] = {
		id = replication.clientId .. ":t" .. sync.tweenCounter,
		target = target, info = info, goals = goals,
	}
end

---Send the final value of every tweened property once (Completed / Cancel / Pause).
---@param record table
local function settleTween(record)
	local target = record.target
	local state = sync.tweening[target]
	if state and state.record == record then
		sync.tweening[target] = nil
	end
	for property in pairs(record.goals) do
		pcall(queueSet, target, property, true)
	end
end

---Play / Pause / Cancel of a remembered tween: the other clients run the very same tween.
---@param tween Instance
---@param method string
function SSEmu.onTweenControl(tween, method)
	local record = SSEmu.tweens[tween]
	if not (record and sync.enabled and replication.enabled) then
		return
	end
	if method == "Play" then
		local ref = syncRef(record.target)
		local info = encodeValue(record.info, 0)
		local goals = encodeValue(record.goals, 0)
		if not (ref and info and goals) then
			return
		end
		pushOp("tween|" .. record.id, { a = "tween", id = record.id, ref = ref, info = info, goals = goals })
		-- While it runs, its per-frame property changes are not sent (the others animate it themselves).
		local props = {}
		for property in pairs(record.goals) do
			props[property] = true
		end
		if props.Position or props.Orientation or props.Rotation then
			props.CFrame = true
		end
		local okLength, length = pcall(function()
			local repeats = record.info.RepeatCount
			if repeats < 0 then
				return math.huge
			end
			return record.info.DelayTime + record.info.Time * (repeats + 1) * (record.info.Reverses and 2 or 1)
		end)
		sync.tweening[record.target] = {
			record = record, props = props,
			untilClock = os.clock() + ((okLength and length) or 1) + 0.25,
		}
		if not record.completedHooked then
			record.completedHooked = true
			pcall(function()
				track(tween.Completed:Connect(function()
					settleTween(record)
				end))
			end)
		end
	elseif method == "Pause" or method == "Cancel" then
		pushOp("tween|" .. record.id .. "|ctl", { a = "tweenctl", id = record.id, m = method })
		task.defer(settleTween, record)
	end
end

---Queue an instance and everything under it, parents first so the replica can rebuild the tree.
---@param inst Instance
queueAdd = function(inst, executorCaller, force)
	if not sync.enabled or sync.applying or realTypeof(inst) ~= "Instance" then
		return
	end
	if sync.tracked[inst] or SYNC_SKIP_CLASSES[inst.ClassName] or not isOwnWorldInstance(inst) then
		return
	end
	-- Convert mode: the other clients built this same content from their own convert, sending it
	-- again would duplicate it. Equipped gear passes force, others must see it in our hands.
	if not force and isDispatchedContent(inst) then
		return
	end
	-- KORUPSİYON FIX: karakter iskeleti ve Humanoid/Animator/HumanoidDescription/BodyColors
	-- native replike oluyor — mirror'a eklenmezler. Humanoid property'leri özel op ile gider.
	if isNativeCharacterPart(inst) then
		return
	end
	local okClass, className = pcall(function() return inst.ClassName end)
	if okClass and (className == "Humanoid" or className == "Animator"
		or className == "HumanoidDescription" or className == "BodyColors") then
		return
	end
	-- FULL FE-DISABLED: scope "all" ise karakterlere eklenen her şey (hat, accessory, mesh, decal)
	-- her client'a gönderilir; scope "executor" eski davranışta kalır.
	if fe.off and executorCaller == false and fe.scope ~= "all" and inCharacter(inst) then
		return
	end
	local nodes = inst:GetDescendants()
	table.insert(nodes, 1, inst)
	for _, node in ipairs(nodes) do
		if sync.count >= SYNC_MAX_TRACKED then
			return warnRelayOnce("Mirror: more than " .. SYNC_MAX_TRACKED .. " instances, the rest is not mirrored")
		end
		if not sync.tracked[node] and not SYNC_SKIP_CLASSES[node.ClassName] then
			local entry = trackInstance(node)
			pushOp(nil, {
				a = "add", id = entry.id, class = node.ClassName,
				parent = syncRef(node.Parent), props = snapshotInstance(node),
			})
		end
	end
	-- The rebuild shows up at once, the exact copy replaces it as soon as the other side has the source.
	pushCloneOps(inst)
end

---Called from the __newindex hook for every accepted sandbox write.
---@param inst Instance
---@param key any
-- Humanoid properties a script may set on any player (damage, heal, speed, scale).
-- Effect methods game scripts may call inside a character (FE disabled): visuals and sound only.
SSEmu.effectMethods = { Emit = true, Play = true, Stop = true, Pause = true, Resume = true, Clear = true }

-- Purely visual body part properties: safe to copy onto another client's view of a character.
SSEmu.limbVisualKeys = {
	Color = true, BrickColor = true, Transparency = true, Material = true, MaterialVariant = true,
	Reflectance = true, CastShadow = true,
}

-- Per-frame motion keys: game LocalScripts write these every frame (camera rigs, bobbing, look-at),
-- they never travel from game scripts. Our own scripts' motion still does.
SSEmu.gameMotionKeys = {
	CFrame = true, Position = true, Orientation = true, Rotation = true, Transform = true,
	Velocity = true, RotVelocity = true, AssemblyLinearVelocity = true, AssemblyAngularVelocity = true,
	PivotOffset = true, WorldPivot = true,
}

-- Sit / PlatformStand / HipHeight / AutoRotate are NOT here: hubs set them on every player, and
-- forwarding that to a player's real character knocks tools out of their hand and breaks movement.
SSEmu.humanoidSyncKeys = {
	Health = true, MaxHealth = true, WalkSpeed = true, JumpPower = true, JumpHeight = true,
	DisplayName = true,
}

SSEmu.noisy = setmetatable({}, { __mode = "k" })

---Whether a game-script write to inst.key is part of a hot loop (more than 5 a second).
---@param inst Instance
---@param key string
---@return boolean
function SSEmu.noisyWrite(inst, key)
	local limit = tonumber(config.mirrorNoisyLimit) or 5
	if limit <= 0 then
		return false
	end
	local now = os.clock()
	local perInst = SSEmu.noisy[inst]
	if not perInst then
		perInst = {}
		SSEmu.noisy[inst] = perInst
	end
	local entry = perInst[key]
	if not entry then
		perInst[key] = { n = 1, t = now, mute = 0 }
		return false
	end
	if entry.mute > now then
		return true
	end
	if now - entry.t > 1 then
		entry.n, entry.t = 1, now
		return false
	end
	entry.n = entry.n + 1
	if entry.n > limit then
		entry.mute = now + (tonumber(config.mirrorNoisyMute) or 10)
		return true
	end
	return false
end

function SSEmu.worldWrite(inst, key, executorCaller, before)
	if sync.applying or not (sync.enabled and replication.enabled) or realTypeof(inst) ~= "Instance" then
		return
	end
	-- Team assignment on any real player (a hub sorting players into teams): every client sets the
	-- same Team on that Player, so names, colors and the leaderboard match everywhere.
	if executorCaller and (key == "Team" or key == "TeamColor" or key == "Neutral") then
		local okPlayer, isPlayer = pcall(function() return inst:IsA("Player") end)
		if okPlayer and isPlayer then
			local okVal, value = pcall(function() return inst[key] end)
			if okVal then
				local encoded = encodeSyncValue(value)
				-- Team = nil (unassigned) travels as false.
				local op = { a = "team", uid = inst.UserId, k = key, v = encoded == nil and false or encoded }
				local opKey = "team|" .. inst.UserId .. "|" .. key
				pushOp(opKey, op)
				-- Kept for clients that join later (resendAll).
				sync.teamState = sync.teamState or {}
				sync.teamState[opKey] = op
			end
			return
		end
	end
	-- Damage / heal / speed on ANY player's Humanoid: addressed to that player, their own client
	-- applies it to their own Humanoid (the only client whose write really counts).
	if executorCaller and SSEmu.humanoidSyncKeys[key] then
		local okClass, className = pcall(function() return inst.ClassName end)
		if okClass and className == "Humanoid" then
			local okPlayer, player = pcall(function()
				return inst.Parent and playersService:GetPlayerFromCharacter(inst.Parent)
			end)
			if okPlayer and player then
				local okVal, value = pcall(function() return inst[key] end)
				local encoded = okVal and encodeSyncValue(value) or nil
				if encoded ~= nil then
					pushOp("humanoid|" .. player.UserId .. "|" .. key, {
						a = "humanoid", uid = player.UserId, k = key, v = encoded,
					})
				end
			end
			return
		end
	end
	-- LAG FIX: a game script hammering one property (day cycles, rainbow loops, per-frame effects)
	-- is muted for that property a while: every client runs that same loop itself anyway.
	if executorCaller == false and key ~= "Parent" and SSEmu.noisyWrite(inst, key) then
		return
	end
	-- Game LocalScripts write GUIs and other local state constantly, only the world is looked at.
	if executorCaller == false and not inScope(inst) and not (before and before.inScope) then
		return
	end
	-- LAG FIX: game LocalScript tag'siz bir instance'a yazıyorsa (ve tracked de değilse) mirror'a
	-- girme. Hub'ın game içinde kendi ağacına yazdığı şeyler zaten native replike. Sadece script
	-- (SOURCE_TAG'li) veya tracked instance'a yazılan'a mirror ilgi duysun.
	if executorCaller == false and not sync.tracked[inst] then
		local okT, tagged = pcall(inst.GetAttribute, inst, SOURCE_TAG)
		local okR, isRep = pcall(inst.GetAttribute, inst, REPLICA_ATTRIBUTE)
		if not ((okT and tagged) or (okR and isRep)) then
			-- FE disabled (scope all): what the game's own LocalScripts do on this client travels too,
			-- effects they parent into the world, colors, materials, lights, sizes. Per-frame motion
			-- stays out (that was the lag), the flush budget caps the rest.
			if not (fe.off and fe.scope == "all") or SSEmu.gameMotionKeys[key] then
				return
			end
		end
	end
	-- Body parts: their structure stays native (that is what kept characters from breaking), but how
	-- they LOOK travels: invisibility, ghost, rainbow body, glowing limbs. Sent as a "limb" op that the
	-- other clients apply to the same player's same body part, nothing else is touched there.
	if isNativeCharacterPart(inst) then
		if SSEmu.limbVisualKeys[key] then
			local okOwner, owner = pcall(function()
				return inst.Parent and playersService:GetPlayerFromCharacter(inst.Parent)
			end)
			local okVal, value = pcall(function() return inst[key] end)
			local encoded = okVal and encodeSyncValue(value) or nil
			if okOwner and owner and encoded ~= nil then
				pushOp("limb|" .. owner.UserId .. "|" .. inst.Name .. "|" .. key, {
					a = "limb", uid = owner.UserId, name = inst.Name, k = key, v = encoded,
				})
			end
		end
		return
	end
	if key == "Parent" then
		if fe.off and before and not sync.tracked[inst] then
			return SSEmu.feParent(inst, executorCaller, before)
		end
		-- Something a script parented into the world (a clone of a real part too) is sent whole.
		if not sync.tracked[inst] then
			queueAdd(inst, executorCaller)
		end
		return
	end
	queueSet(inst, key, executorCaller)
	-- A mirrored copy stays anchored here, its owner simulates it and streams the motion.
	if fe.off and key == "Anchored" and isReplica(inst) and inst:IsA("BasePart") then
		sync.originAnchored[inst] = inst.Anchored == true
		sync.applying = true
		pcall(fixAnchor, inst)
		sync.applying = false
	end
end

---FE off: an untracked world instance changed parent. Into the world it is sent whole, inside the world
---it is moved on every client, out of the world it is taken out on every client.
---@param inst Instance
---@param executorCaller boolean
---@param before table
function SSEmu.feParent(inst, executorCaller, before)
	local nowIn = inScope(inst) and not inSkippedBranch(inst)
	if not before.inScope then
		if nowIn then
			queueAdd(inst, executorCaller)
		end
		return
	end
	if not before.ref or (executorCaller == false and before.character) then
		return
	end
	local op = { a = "reparent", ref = before.ref }
	if nowIn then
		op.parent = syncRef(inst.Parent)
		if not op.parent then
			return
		end
	else
		op.detach = true
	end
	local key = refKeyOf(inst) .. "|parent"
	pushOp(key, op)
	if not before.foreign then
		feRecord(key, op)
	end
end

---Called from the __namecall hook before a sandbox Destroy / PivotTo / MoveTo on a world instance.
---@param inst Instance
---@param method string
---@param executorCaller boolean
function SSEmu.worldCall(inst, method, executorCaller, ...)
	if sync.applying or not (sync.enabled and replication.enabled) or realTypeof(inst) ~= "Instance" then
		return
	end
	-- A tween our scripts (or, FE disabled, the game's) made: Play / Pause / Cancel travel as one op,
	-- the other clients run the same tween, smooth, instead of 30 property jumps a second.
	if SSEmu.tweens[inst] then
		return SSEmu.onTweenControl(inst, method)
	end
	-- Game LocalScript calls on untagged instances only travel with FE disabled (scope all).
	if executorCaller == false and not sync.tracked[inst] then
		local okT, tagged = pcall(inst.GetAttribute, inst, SOURCE_TAG)
		local okR, isRep = pcall(inst.GetAttribute, inst, REPLICA_ATTRIBUTE)
		if not ((okT and tagged) or (okR and isRep)) and not (fe.off and fe.scope == "all") then
			return
		end
	end
	if isNativeCharacterPart(inst) then
		return
	end
	if method == "AddItem" then
		-- Debris removes the item later on the engine side where no hook sees it, so it is sent then.
		local item, lifetime = ...
		if not fe.off or realTypeof(item) ~= "Instance" or sync.tracked[item] then
			return
		end
		local before = SSEmu.feBefore(item)
		if not (before.inScope and before.ref) or (executorCaller == false and before.character) then
			return
		end
		task.delay(tonumber(lifetime) or 10, function()
			if active and fe.off and replication.enabled then
				local op = { a = "call", ref = before.ref, m = "Destroy", args = { n = 0, list = {} } }
				pushOp(nil, op)
				if not before.foreign then
					feRecord(nil, op)
				end
			end
		end)
		return
	end
	if method == "SetAttribute" then
		-- Our own bookkeeping attributes never travel.
		local name = ...
		if type(name) ~= "string" or name:sub(1, 4) == "_sse" or name:sub(1, 3) == "_cv" then
			return
		end
	end
	local entry = sync.tracked[inst]
	local foreign = false
	if not entry and not isOwnWorldInstance(inst) then
		if not (fe.off and inScope(inst) and isReplicaContent(inst)) then
			return
		end
		foreign = true
	end
	if SYNC_SKIP_CLASSES[inst.ClassName] then
		return
	end
	-- Game scripts inside a character: effects travel (FE disabled, scope all), a hit spark :Emit(), an
	-- aura :Play(). Structural calls (ChangeState, Destroy, impulses) stay native, they broke characters.
	if fe.off and executorCaller == false and not entry and not foreign and inCharacter(inst)
		and not (fe.scope == "all" and SSEmu.effectMethods[method]) then
		return
	end
	local ref = entry and { t = "sid", id = entry.id } or syncRef(inst)
	if not ref then
		return
	end
	local packed = table.pack(...)
	local args = { n = packed.n, list = {} }
	for index = 1, packed.n do
		local encoded = encodeSyncValue(packed[index])
		if encoded ~= nil then
			table.insert(args.list, { i = index, v = encoded })
		end
	end
	local op = { a = "call", ref = ref, m = method, args = args }
	pushOp(nil, op)
	if not entry and not foreign and FE_JOURNAL_METHODS[method] then
		local key = refKeyOf(inst) .. "|call|" .. method
		if method == "SetAttribute" then
			key = key .. "|" .. tostring((...))
		end
		feRecord(key, op)
	end
end

---A server-only action on another player (Kick, LoadCharacter) is carried out by that player's own client.
---@param kind string
---@param player any
---@param reason string?
function SSEmu.worldPlayer(kind, player, reason)
	if not (sync.enabled and replication.enabled) or fakeObjects[player] then
		return
	end
	local okId, userId = pcall(function() return player.UserId end)
	if okId and type(userId) == "number" then
		pushOp(nil, { a = kind, user = userId, reason = tostring(reason or "") })
	end
end

---Replica side: while sitting in a mirrored seat, our input goes to the client that owns the seat.
local function pollDriving()
	local character = localPlayer.Character
	local humanoid = character and character:FindFirstChildOfClass("Humanoid")
	local seat = (SSEmu.seats and SSEmu.seats.current and SSEmu.seats.current.seat) or (humanoid and humanoid.SeatPart)
	local sid = seat and isReplica(seat) and seat:GetAttribute(SYNC_ID_ATTRIBUTE)

	if not sid then
		if sync.lastDrive then
			pushOp(nil, { a = "drive", id = sync.lastDrive.id, user = localPlayer.UserId, seated = false })
			sync.lastDrive = nil
		end
		return
	end

	local throttle, steer = 0, 0
	if seat:IsA("VehicleSeat") then
		throttle, steer = seat.ThrottleFloat ~= 0 and seat.ThrottleFloat or seat.Throttle, seat.SteerFloat ~= 0 and seat.SteerFloat or seat.Steer
	end
	local last = sync.lastDrive
	local now = os.clock()
	if last and last.id == sid and last.throttle == throttle and last.steer == steer and now - sync.lastDriveAt < 1 then
		return
	end
	if last and last.id ~= sid then
		pushOp(nil, { a = "drive", id = last.id, user = localPlayer.UserId, seated = false })
	end
	sync.lastDrive = { id = sid, throttle = throttle, steer = steer }
	sync.lastDriveAt = now
	pushOp("drive|" .. sid, { a = "drive", id = sid, user = localPlayer.UserId, seated = true, throttle = throttle, steer = steer })
end

---Whether two CFrames differ enough to be worth a trip.
local function cframeMoved(a, b)
	return (a.Position - b.Position).Magnitude > 0.01
		or (a.LookVector - b.LookVector).Magnitude > 0.002
		or (a.UpVector - b.UpVector).Magnitude > 0.002
end

---Physics moves parts without any property event, so tracked parts are compared every tick.
-- LAG FIX: anchored part'ları ve karakter iskelet part'larını pollleme — bunlar ya hiç hareket
-- etmez ya da zaten native replike oluyor.
local function pollMotion()
	for inst, entry in pairs(sync.tracked) do
		local last = sync.lastCFrame[inst]
		if last then
			local okA, anchored = pcall(function() return inst.Anchored end)
			if okA and anchored then
				-- Anchored part hareket etmez; hiç okuma yapma.
			elseif isNativeCharacterPart(inst) then
				-- Karakter iskeleti zaten native replike oluyor.
			else
				local ok, now = pcall(function() return inst.CFrame end)
				local tweening = sync.tweening[inst]
				if tweening and tweening.props.CFrame and os.clock() < tweening.untilClock then
					-- A mirrored tween moves it on the other clients, only its end position is sent.
					ok = false
				end
				if ok and now and cframeMoved(last, now) then
					sync.lastCFrame[inst] = now
					pushOp(entry.id .. "|CFrame", { a = "set", ref = { t = "sid", id = entry.id }, k = "CFrame", v = encodeValue(now, 0) })
				end
			end
		end
	end
end

---Send every tracked instance again, for a client that joined after they were made.
local function resendAll()
	-- Every tracked tree, wherever it lives (Workspace, Lighting, Teams, the emulated server folders),
	-- parents first, then its exact copy ops.
	local roots = {}
	for inst in pairs(sync.tracked) do
		local okParent, parent = pcall(function() return inst.Parent end)
		if okParent and parent and not sync.tracked[parent] then
			table.insert(roots, inst)
		end
	end
	for _, root in ipairs(roots) do
		local okList, nodes = pcall(function() return root:GetDescendants() end)
		nodes = okList and nodes or {}
		table.insert(nodes, 1, root)
		for _, node in ipairs(nodes) do
			local entry = sync.tracked[node]
			if entry then
				pushOp(nil, {
					a = "add", id = entry.id, class = node.ClassName,
					parent = syncRef(node.Parent), props = snapshotInstance(node),
				})
			end
		end
		pushCloneOps(root)
	end
	-- Team assignments our scripts made, after the teams themselves.
	for _, op in pairs(sync.teamState or {}) do
		pushOp(nil, op)
	end
	-- FE off: what this client did to server instances (deleted parts, recolors, moved models) too.
	if fe.off then
		for _, op in ipairs(fe.journal) do
			pushOp(nil, op)
		end
	end
end

---Mirror an instance and everything under it right now, whatever made it (.share).
---@param inst Instance
---@return boolean
function SSEmu.share(inst)
	if not (inScope(inst) and not inSkippedBranch(inst)) then
		return false
	end
	queueAdd(inst, true, true)
	return true
end

---CONTINUOUS COPY: every second a slice of everything we track is sent again with its full current
---state, walking the trees parents first. A client that lost or missed anything (a failed request, a
---reference that came too late, a copy destroyed on its side) is put right within one round, so the
---other clients keep matching ours instead of drifting forever. Paused while the queue is busy.
function SSEmu.refreshTick()
	if not (sync.enabled and replication.enabled and replication.connected) then
		return
	end
	if #sync.ops > (tonumber(config.mirrorBudget) or 600) then
		return
	end
	local list = sync.refreshList
	if not list or sync.refreshIndex > #list then
		-- New round: a fresh parents-first list of every tracked tree (characters' gear excluded,
		-- held tools are welded on the other side and a refresh would unweld them).
		list = {}
		for inst in pairs(sync.tracked) do
			local okParent, parent = pcall(function() return inst.Parent end)
			if okParent and parent and not sync.tracked[parent] and not inCharacter(inst) then
				local okNodes, nodes = pcall(function() return inst:GetDescendants() end)
				table.insert(list, inst)
				for _, node in ipairs(okNodes and nodes or {}) do
					if sync.tracked[node] then
						table.insert(list, node)
					end
				end
			end
		end
		sync.refreshList = list
		sync.refreshIndex = 1
	end
	local count = tonumber(config.mirrorRefresh) or 10
	while count > 0 and sync.refreshIndex <= #list do
		local node = list[sync.refreshIndex]
		sync.refreshIndex = sync.refreshIndex + 1
		local entry = sync.tracked[node]
		if entry and node.Parent then
			pushOp(nil, {
				a = "add", id = entry.id, class = node.ClassName, refresh = true,
				parent = syncRef(node.Parent), props = snapshotInstance(node, true),
			})
			-- A root: its exact copy again too (a no-op where the copy is already exact).
			if not sync.tracked[node.Parent] then
				pushCloneOps(node)
			end
			count = count - 1
		end
	end
end

---Push the queued ops in order. Sequential on purpose: parallel requests would reorder add/remove.
local function flushWorld()
	if #sync.ops == 0 or not replication.connected then
		return
	end
	-- Budget: at most 600 ops per flush. The rest stays queued in order and keeps coalescing (a property
	-- written again replaces its queued value), so a game script recoloring hundreds of parts every frame
	-- cannot flood the relay, and the final state still always arrives.
	local budget = tonumber(config.mirrorBudget) or 600
	local ops = sync.ops
	if #ops > budget then
		local rest = {}
		for index = budget + 1, #ops do
			table.insert(rest, ops[index])
		end
		local now = {}
		for index = 1, budget do
			now[index] = ops[index]
		end
		ops = now
		sync.ops, sync.opIndex = rest, {}
		for index, op in ipairs(rest) do
			local key = op._key
			if key then
				sync.opIndex[key] = index
			end
		end
	else
		sync.ops, sync.opIndex = {}, {}
	end
	for start = 1, #ops, SYNC_OPS_PER_PUSH do
		local chunk = {}
		for index = start, math.min(start + SYNC_OPS_PER_PUSH - 1, #ops) do
			table.insert(chunk, ops[index])
		end
		local _, err = relayRequest("POST", "/push", {
			room = RELAY_ROOM,
			client = replication.clientId,
			type = "world",
			payload = { ops = chunk },
		})
		if err then
			warnRelayOnce("Mirror push failed: " .. err)
			SSEmu.diagStats.pushErrors = SSEmu.diagStats.pushErrors + 1
			SSEmu.diagStats.lastError = "push: " .. tostring(err)
		else
			SSEmu.diagStats.sent = SSEmu.diagStats.sent + #chunk
		end
	end
end

---Tick loop: motion poll, then flush.
-- Motion poll 30Hz (hem CPU hem HTTP rahat), HTTP flush ayrı thread'de 10Hz default.
-- config.mirrorRate ile ayarlanabilir, 0 verirsen Heartbeat'e geçer.
local function syncLoop()
	if sync.running then
		return
	end
	sync.running = true

	-- Low latency defaults: motion read every frame, changes sent ~30 times a second. Only script made
	-- content travels and an empty queue sends nothing, so this costs nothing while idle.
	local flushRate = tonumber(config.mirrorRate) or 0.03
	local pollRate = tonumber(config.mirrorPollRate) or 0

	task.spawn(function()
		while active and replication.enabled and sync.enabled do
			pcall(flushWorld)
			task.wait(sync.lastDrive and SYNC_DRIVE_RATE or flushRate)
		end
	end)

	-- Continuous copy: a slice of the tracked world re-sent every second (anti-drift).
	sync.refreshIndex = sync.refreshIndex or 1
	task.spawn(function()
		while active and replication.enabled and sync.enabled do
			task.wait(1)
			if config.mirrorRefresh ~= 0 then
				local ok, err = pcall(SSEmu.refreshTick)
				if not ok then
					SSEmu.diagStats.lastError = "refresh: " .. tostring(err)
				end
			end
		end
	end)

	while active and replication.enabled and sync.enabled do
		pcall(pollMotion)
		pcall(pollDriving)
		if pollRate <= 0 then
			runService.Heartbeat:Wait()
		else
			task.wait(pollRate)
		end
	end
	sync.running = false
end

-- ═══ Replica side ═══

---Resolve a reference sent by another client.
---@param ref any
---@return Instance?
local function resolveRef(ref)
	local value = decodeSyncValue(ref)
	return realTypeof(value) == "Instance" and value or nil
end

---Whether a value is an instance reference that may resolve later.
local function isPendingRef(value)
	return type(value) == "table" and (value.t == "sid" or value.t == "inst")
end

---Whether an instance sits inside the character of a real player (a hat or weld the origin put on us).
---@param inst Instance
---@return boolean
local function underRealCharacter(inst)
	local model = inst:FindFirstAncestorOfClass("Model")
	while model do
		if playersService:GetPlayerFromCharacter(model) then
			return true
		end
		model = model:FindFirstAncestorOfClass("Model")
	end
	return false
end

---Mirrored scenery is anchored and moved by the origin. A part welded onto a real character keeps the
---origin's Anchored, otherwise it would freeze that character.
---@param inst Instance
fixAnchor = function(inst)
	-- Only mirrored copies are pinned, a real part another client moved keeps its physics.
	if not inst:IsA("BasePart") or not isReplica(inst) then
		return
	end
	local anchored = true
	if underRealCharacter(inst) then
		anchored = sync.originAnchored[inst] == true
	end
	pcall(function() inst.Anchored = anchored end)
end

---Replica side: walking into a mirrored part touches the origin's part with our character.
---@param inst Instance
local function armMirrorTouch(inst)
	if not inst:IsA("BasePart") then
		return
	end
	track(inst.Touched:Connect(function(hit)
		local character = localPlayer.Character
		if not (character and hit:IsDescendantOf(character)) then
			return
		end
		local now = os.clock()
		if now - (sync.touchTimes[inst] or 0) < SYNC_TOUCH_COOLDOWN then
			return
		end
		sync.touchTimes[inst] = now
		local sid = inst:GetAttribute(SYNC_ID_ATTRIBUTE)
		if sid then
			pushOp(nil, { a = "touch", id = sid, user = localPlayer.UserId, part = hit.Name })
		end
	end))
end

---Apply one property on a mirrored instance. Returns false when the value refers to something missing.
---@param inst Instance
---@param key string
---@param value any
---@return boolean
sync.smooth = setmetatable({}, { __mode = "k" })
sync.smoothSeen = setmetatable({}, { __mode = "k" })

---Glide an anchored mirrored part to a new CFrame over the time since its last update.
---Returns false (the caller sets it directly) for the first placement, unanchored parts and teleports.
---@param part BasePart
---@param target CFrame
---@return boolean
function SSEmu.smoothTo(part, target)
	local okState, anchored, current, parent = pcall(function()
		return part.Anchored, part.CFrame, part.Parent
	end)
	local now = os.clock()
	local lastSeen = sync.smoothSeen[part]
	sync.smoothSeen[part] = now
	if not (okState and anchored and parent and lastSeen) or (current.Position - target.Position).Magnitude > 40 then
		sync.smooth[part] = nil
		return false
	end
	sync.smooth[part] = { from = current, to = target, start = now, length = math.clamp(now - lastSeen, 1 / 60, 0.12) }
	if not sync.smoothConnection then
		sync.smoothConnection = runService.Heartbeat:Connect(function()
			if next(sync.smooth) == nil then
				return
			end
			local clock = os.clock()
			-- Our own writes: never sent back out by the mirror.
			sync.applying = true
			for glide, entry in pairs(sync.smooth) do
				local alpha = (clock - entry.start) / entry.length
				if alpha >= 1 then
					pcall(function() glide.CFrame = entry.to end)
					sync.smooth[glide] = nil
				else
					pcall(function() glide.CFrame = entry.from:Lerp(entry.to, alpha) end)
				end
			end
			sync.applying = false
		end)
		track(sync.smoothConnection)
	end
	return true
end

SSEmu.assetKeys = {
	MeshId = true, TextureId = true, TextureID = true, Texture = true, Image = true,
	ColorMap = true, NormalMap = true, MetalnessMap = true, RoughnessMap = true,
	ShirtTemplate = true, PantsTemplate = true, Graphic = true, SoundId = true,
}

local function applyProperty(inst, key, value)
	-- FULL FE-DISABLED: attribute toplu uygulaması.
	if key == "__attributes" and type(value) == "table" and value.t == "attrs" then
		for _, entry in ipairs(value.list or {}) do
			pcall(function() inst:SetAttribute(entry.k, decodeSyncValue(entry.v)) end)
		end
		return true
	end
	-- WHITE FIX: Content-typed properties are never written (a bad value blanks the mesh/texture).
	if type(key) == "string" and key:sub(-7) == "Content" then
		return true
	end
	local isPart = inst:IsA("BasePart")
	local replica = isReplica(inst)
	if key == "Anchored" and isPart and replica then
		sync.originAnchored[inst] = value == true
		fixAnchor(inst)
		return true
	end
	-- An unanchored part (welded onto a real character, our own body) moves with its assembly.
	-- FE off: a real part another client moved (a teleport, a fling) is moved here too.
	if key == "CFrame" and isPart and not inst.Anchored and (replica or not fe.off) then
		return true
	end
	local decoded = decodeSyncValue(value)
	if value ~= nil and decoded == nil then
		return not isPendingRef(value)
	end
	-- WHITE FIX: an empty asset id never wipes a texture/mesh that is already showing here.
	if decoded == "" and SSEmu.assetKeys[key] then
		local okCur, current = pcall(function() return inst[key] end)
		if okCur and type(current) == "string" and current ~= "" then
			return true
		end
	end
	if sync.tracked[inst] then
		sync.echo[inst] = sync.echo[inst] or {}
		sync.echo[inst][key] = decoded
	end
	local latest = sync.latest[inst]
	if not latest then
		latest = {}
		sync.latest[inst] = latest
	end
	latest[key] = value
	-- The size guards follow the newest value the origin sent, never a stale first one.
	if key == "Size" and realTypeof(decoded) == "Vector3" then
		sync.sizeTargets[inst] = decoded
	elseif key == "Scale" and realTypeof(decoded) == "Vector3" then
		sync.scaleTargets[inst] = decoded
	end
	-- SMOOTH: a mirrored, anchored part glides to its new CFrame over one update interval instead of
	-- jumping 30 times a second (made for filming). First placement and teleports still snap.
	if key == "CFrame" and isPart and replica and config.mirrorSmooth ~= false
		and realTypeof(decoded) == "CFrame" and SSEmu.smoothTo(inst, decoded) then
		return true
	end
	-- TEXTURE FIX: Content property'leri (TextureContent/MeshContent/ColorMap/NormalMap/MetalnessMap/
	-- RoughnessMap) bazı Roblox sürümlerinde string atamayı reddedip Content tipi istiyor; önce string
	-- dene, olmazsa Content.fromUri ile sar. Decal.Texture ikisi de kabul.
	local CONTENT_KEYS = {
		MeshContent = true, TextureContent = true,
		ColorMap = true, NormalMap = true, MetalnessMap = true, RoughnessMap = true,
		ColorMapContent = true, NormalMapContent = true,
		MetalnessMapContent = true, RoughnessMapContent = true,
	}
	local ok = pcall(function() inst[key] = decoded end)
	if not ok and CONTENT_KEYS[key] and type(decoded) == "string" and Content then
		pcall(function()
			local wrapped = Content.fromUri(decoded)
			inst[key] = wrapped
		end)
	end
	return true
end

---Owner side: a mirrored client sat down in, drove or left one of our seats.
---@param op table
local function applyDrive(op)
	local seat = sync.ownById[op.id]
	local player = seat and playersService:GetPlayerByUserId(op.user)
	if not (player and SSEmu.seats.isSeat(seat)) then
		return
	end
	-- We sit in it ourselves, our own input wins.
	local own = localPlayer.Character and localPlayer.Character:FindFirstChildOfClass("Humanoid")
	if (SSEmu.seats.current and SSEmu.seats.current.seat == seat) or (own and own.SeatPart == seat) then
		return
	end
	SSEmu.remoteOccupants = SSEmu.remoteOccupants or setmetatable({}, { __mode = "k" })
	local humanoid = player.Character and player.Character:FindFirstChildOfClass("Humanoid")
	local previous = SSEmu.remoteOccupants[seat]

	if op.seated and humanoid then
		SSEmu.remoteOccupants[seat] = humanoid
		if previous ~= humanoid then
			SSEmu.seats.announce(seat, humanoid, true)
			log("[mirror] " .. player.Name .. " sat in " .. seat.Name, INFO_COLOR)
		end
		if seat:IsA("VehicleSeat") then
			local throttle, steer = tonumber(op.throttle) or 0, tonumber(op.steer) or 0
			pcall(function()
				seat.ThrottleFloat, seat.SteerFloat = throttle, steer
				seat.Throttle, seat.Steer = math.sign(throttle), math.sign(steer)
			end)
		end
	else
		SSEmu.remoteOccupants[seat] = nil
		if previous then
			SSEmu.seats.announce(seat, previous, false)
		end
		if seat:IsA("VehicleSeat") then
			pcall(function()
				seat.ThrottleFloat, seat.SteerFloat, seat.Throttle, seat.Steer = 0, 0, 0, 0
			end)
		end
	end
end

---Owner side: a mirrored client touched one of our parts, the touch is fired here with its character.
---@param op table
local function applyTouch(op)
	local part = sync.ownById[op.id]
	local player = part and playersService:GetPlayerByUserId(op.user)
	local character = player and player.Character
	if not (character and part:IsA("BasePart") and firetouchinterest) then
		return
	end
	local limb = character:FindFirstChild(tostring(op.part)) or character:FindFirstChild("HumanoidRootPart")
	if not (limb and limb:IsA("BasePart")) then
		return
	end
	pcall(firetouchinterest, limb, part, 0)
	task.wait()
	pcall(firetouchinterest, limb, part, 1)
end

---Retry property and parent assignments that referred to instances that did not exist yet.
local function retryDeferred()
	local remaining = {}
	for _, item in ipairs(sync.deferred) do
		local done = true
		if item.parent ~= nil then
			local parent = resolveRef(item.parent)
			if parent then
				pcall(function() item.inst.Parent = parent end)
				fixAnchor(item.inst)
			else
				done = false
			end
		else
			done = applyProperty(item.inst, item.key, item.value)
		end
		item.tries = (item.tries or 0) + 1
		if not done and item.tries < SYNC_DEFER_LIMIT then
			table.insert(remaining, item)
		end
	end
	sync.deferred = remaining
end

-- ═══ Exact copy (replica side) ═══
-- src -> { state = "loading" | "ready" | "failed", index = { [key] = node }, pending = { op, ... } }
sync.cloneSources = {}
sync.cloneSkipKeys = { MeshId = true, MeshContent = true }

---We picked up another player's dropped tool: build our own working copy and equip it, like Roblox.
---From its source when it has one (scripts included, it really works), otherwise from the mirrored
---copy (looks right, no scripts). Once in our hand it is mirrored as ours.
---@param op table
---@param fallback Instance?
function SSEmu.receiveTool(op, fallback)
	local function deliver(tool)
		local nodes = tool:GetDescendants()
		table.insert(nodes, 1, tool)
		for _, node in ipairs(nodes) do
			pcall(node.SetAttribute, node, REPLICA_ATTRIBUTE, nil)
			pcall(node.SetAttribute, node, SYNC_ID_ATTRIBUTE, nil)
			pcall(node.SetAttribute, node, "_sse_exact", nil)
			if node:IsA("Weld") and node.Name == "RightGrip" then
				pcall(function() node:Destroy() end)
			elseif node:IsA("BasePart") then
				pcall(function()
					node.Anchored = false
					node.Massless = false
				end)
			end
		end
		pcall(tool.SetAttribute, tool, SOURCE_TAG, true)
		giveTool(tool)
		task.defer(function()
			local character = localPlayer.Character
			local humanoid = character and character:FindFirstChildOfClass("Humanoid")
			if humanoid and tool.Parent then
				pcall(function() humanoid:EquipTool(tool) end)
			end
			log("Picked up " .. tool.Name, INFO_COLOR)
		end)
	end

	local function fromSource(entry)
		local source = entry and entry.index[op.key]
		if not source then
			return false
		end
		pcall(function() source.Archivable = true end)
		local okClone, copy = pcall(function() return source:Clone() end)
		if not (okClone and copy) then
			return false
		end
		-- Same addresses as the original, so our mirror sends exact copies of it too.
		for _, pair in ipairs(SSEmu.keyTree(copy, op.key)) do
			pcall(pair[1].SetAttribute, pair[1], "_sse_src", op.src)
			pcall(pair[1].SetAttribute, pair[1], "_sse_key", pair[2])
		end
		prepareAsset(copy, false, op.src:sub(1, 2) == "a:" and ("give:" .. op.src:sub(3)) or ("convert:" .. op.src:sub(3)))
		deliver(copy)
		return true
	end

	if type(op.src) == "string" and type(op.key) == "string" then
		local entry = sync.cloneSources[op.src] or sync.loadCloneSource(op.src)
		if entry.state == "ready" and fromSource(entry) then
			return
		end
		if entry.state == "loading" then
			task.spawn(function()
				local deadline = os.clock() + 10
				while entry.state == "loading" and os.clock() < deadline do
					task.wait(0.1)
				end
				if not (entry.state == "ready" and fromSource(entry)) and fallback then
					deliver(fallback)
				end
			end)
			return
		end
	end
	if fallback then
		deliver(fallback)
	end
end

-- handle sid -> last grip op, so the weld is made again when the exact copy replaces the handle.
sync.grips = {}

---Weld our copy of another player's held tool to that player's hand, so it moves with the arm.
---@param op table
---@return boolean
function sync.applyGrip(op)
	local player = playersService:GetPlayerByUserId(tonumber(op.uid) or 0)
	local character = player and player.Character
	local limb = character and character:FindFirstChild(tostring(op.limb), true)
	local handle = sync.byId[op.handle]
	if not (limb and limb:IsA("BasePart") and handle and handle:IsA("BasePart")) then
		return false
	end
	sync.grips[op.handle] = op
	-- The whole tool copy hangs off the hand: unanchored, massless, never pushing anyone.
	local parts = { handle }
	local tool = handle.Parent
	if tool then
		for _, node in ipairs(tool:GetDescendants()) do
			if node:IsA("BasePart") and node ~= handle then
				table.insert(parts, node)
			end
		end
	end
	for _, part in ipairs(parts) do
		sync.originAnchored[part] = false
		pcall(function()
			part.Anchored = false
			part.Massless = true
			part.CanCollide = false
		end)
	end
	for _, child in ipairs(handle:GetChildren()) do
		local okRep, rep = pcall(child.GetAttribute, child, REPLICA_ATTRIBUTE)
		if child:IsA("Weld") and child.Name == "RightGrip" and okRep and rep then
			pcall(function() child:Destroy() end)
		end
	end
	local weld = realInstance.new("Weld")
	weld.Name = "RightGrip"
	pcall(weld.SetAttribute, weld, SOURCE_TAG, true)
	pcall(weld.SetAttribute, weld, REPLICA_ATTRIBUTE, true)
	weld.Part0 = limb
	weld.Part1 = handle
	local c0, c1 = decodeValue(op.c0), decodeValue(op.c1)
	weld.C0 = realTypeof(c0) == "CFrame" and c0 or CFrame.new()
	weld.C1 = realTypeof(c1) == "CFrame" and c1 or CFrame.new()
	-- Under the handle: it goes away with the tool copy on unequip.
	weld.Parent = handle
	return true
end

---Replace the approximate rebuild of a piece with a clone of its real source: a 1:1 copy.
---@param op table
function sync.swapInClone(op)
	local entry = sync.cloneSources[op.src]
	local source = entry and entry.index[op.key]
	local approxRoot = sync.byId[op.id]
	if not (source and approxRoot) then
		return
	end
	local okExact, exact = pcall(approxRoot.GetAttribute, approxRoot, "_sse_exact")
	if okExact and exact then
		return
	end
	-- Still waiting for its parent: try again shortly instead of cloning into nothing.
	if not approxRoot.Parent then
		op.tries = (op.tries or 0) + 1
		if op.tries <= 20 then
			task.delay(0.25, function()
				sync.applying = true
				pcall(sync.swapInClone, op)
				sync.applying = false
			end)
		end
		return
	end

	local okArchivable, wasArchivable = pcall(function() return source.Archivable end)
	pcall(function() source.Archivable = true end)
	local okClone, copy = pcall(function() return source:Clone() end)
	if okArchivable then
		pcall(function() source.Archivable = wasArchivable end)
	end
	if not (okClone and copy) then
		return
	end

	local byKey = {}
	for _, pair in ipairs(SSEmu.keyTree(copy, op.key)) do
		byKey[pair[2]] = pair[1]
	end
	local wanted = {}
	for _, item in ipairs(op.map or {}) do
		if type(item.key) == "string" and item.id then
			wanted[item.key] = item.id
		end
	end
	-- What the origin no longer has, and every script, leaves the copy before it is ever parented:
	-- a copy is scenery, its owner runs the logic.
	for key, node in pairs(byKey) do
		-- Real remotes in the asset are dropped too: the emulated remote rebuilt from the add op stays
		-- in their place (moved under the copy below), the only kind another client can fire.
		local okClass, nodeClass = pcall(function() return node.ClassName end)
		local isRemote = okClass and REMOTE_CLASSES[nodeClass]
		if node ~= copy and (not wanted[key] or node:IsA("LuaSourceContainer") or isRemote) then
			started[node] = true
			pcall(function() node:Destroy() end)
			byKey[key] = nil
		end
	end

	-- Map our ids onto the copy, by address.
	local cloneOf = {}
	for key, sid in pairs(wanted) do
		local node = byKey[key]
		local approx = sync.byId[sid]
		if node then
			pcall(node.SetAttribute, node, SOURCE_TAG, true)
			pcall(node.SetAttribute, node, REPLICA_ATTRIBUTE, true)
			pcall(node.SetAttribute, node, SYNC_ID_ATTRIBUTE, sid)
			if node:IsA("BasePart") then
				pcall(function() node.Anchored = true end)
			end
			if approx then
				cloneOf[approx] = node
			end
		end
	end

	-- Pieces a script added under a rebuilt piece move over to its exact twin.
	for approx, node in pairs(cloneOf) do
		for _, child in ipairs(approx:GetChildren()) do
			if not cloneOf[child] then
				pcall(function() child.Parent = node end)
			end
		end
	end

	-- The origin's current state on top (size it scaled to, colors, position): last values it sent.
	for approx, node in pairs(cloneOf) do
		local latest = sync.latest[approx]
		if latest then
			for key, value in pairs(latest) do
				if not sync.cloneSkipKeys[key] and key ~= "CFrame" and key ~= "Anchored" then
					pcall(applyProperty, node, key, value)
				end
			end
			if latest.CFrame ~= nil then
				pcall(applyProperty, node, "CFrame", latest.CFrame)
			end
			if latest.Anchored ~= nil then
				pcall(applyProperty, node, "Anchored", latest.Anchored)
			end
		end
	end

	-- Swap: the exact copy takes the rebuild's place, every id now points at the copy.
	for key, sid in pairs(wanted) do
		local node = byKey[key]
		if node then
			sync.byId[sid] = node
			armMirrorTouch(node)
		end
	end
	pcall(copy.SetAttribute, copy, "_sse_exact", true)
	copy.Parent = approxRoot.Parent
	for _, pair in ipairs(SSEmu.keyTree(copy, op.key)) do
		pcall(fixAnchor, pair[1])
	end
	pcall(function() approxRoot:Destroy() end)
	-- A held tool: its new exact handle gets welded to the hand again.
	for _, sid in pairs(wanted) do
		local grip = sync.grips[sid]
		if grip then
			pcall(sync.applyGrip, grip)
		end
	end
end

---Download (asset) or find (game path) a source once, index it by address, then run waiting swaps.
---@param src string
---@return table
function sync.loadCloneSource(src)
	local entry = { state = "loading", index = {}, pending = {} }
	sync.cloneSources[src] = entry
	task.spawn(function()
		local roots
		if src:sub(1, 2) == "a:" then
			local id = tonumber(src:sub(3))
			roots = id and fetchObjects(id, 2) or nil
		else
			local okPath, inst = pcall(resolvePath, src:sub(3))
			roots = (okPath and inst) and { inst } or nil
		end
		if not roots then
			entry.state = "failed"
			entry.pending = {}
			return log("Exact copy: source " .. src .. " unavailable, the rebuild stays", WARN_COLOR)
		end
		for index, root in ipairs(roots) do
			for _, pair in ipairs(SSEmu.keyTree(root, tostring(index))) do
				entry.index[pair[2]] = pair[1]
			end
		end
		entry.state = "ready"
		local pending = entry.pending
		entry.pending = {}
		for _, op in ipairs(pending) do
			sync.applying = true
			local ok, err = pcall(sync.swapInClone, op)
			sync.applying = false
			if not ok then
				log("Exact copy failed: " .. tostring(err), WARN_COLOR)
			end
		end
	end)
	return entry
end

---Apply one op from another client.
---@param op table
local function applyOp(op)
	local action = op.a
	if action == "add" then
		if SYNC_SKIP_CLASSES[op.class] then
			return
		end
		local inst = sync.byId[op.id]
		-- Refresh of something we lost along the way (destroyed, or its parent never arrived): rebuild it.
		if inst and op.refresh and not inst.Parent then
			sync.byId[op.id] = nil
			inst = nil
		end
		if not inst then
			-- A remote another client made: an emulated remote here too (a real one would talk to the
			-- Roblox server, which never heard of it). Its FireServer reaches the owner's server logic.
			local ok, created
			if REMOTE_CLASSES[op.class] then
				ok, created = pcall(createMockRemote, op.class)
			else
				ok, created = pcall(realInstance.new, op.class)
			end
			if not ok or not created then
				return
			end
			inst = created
			sync.byId[op.id] = inst
			pcall(inst.SetAttribute, inst, SOURCE_TAG, true)
			pcall(inst.SetAttribute, inst, REPLICA_ATTRIBUTE, true)
			pcall(inst.SetAttribute, inst, SYNC_ID_ATTRIBUTE, op.id)
			armMirrorTouch(inst)
		end
		if inst:IsA("BasePart") and not op.refresh then
			pcall(function() inst.Anchored = true end)
		end
		-- SCALE FIX: MeshPart'ta MeshContent yüklendiğinde part'in Size'ı otomatik mesh'in default
		-- boyutuna döner. Bu yüzden Size'ı MeshContent'TEN SONRA set etmek şart. Yoksa Size önce
		-- yazılır, MeshContent sonra yüklenip auto-resize Size'ı eziyor.
		-- SpecialMesh'te önce MeshType=FileMesh gelmeli ki MeshId geçerli olsun.
		local PROP_PRIORITY = {
			-- 1) Enum/tip property'leri: mesh/font/shape kimliği önce belirlensin.
			MeshType = 120, AlphaMode = 120, RigType = 120, Shape = 120,
			Font = 120, FontFace = 120, ScaleType = 115, Technology = 115,
			LightInfluence = 110,
			-- 2) Mesh/texture IÇERİĞİ yüklensin: MeshContent/MeshId önce ki mesh load olsun,
			-- Size sonradan uygulansın da auto-resize Size'ı ezmesin.
			MeshContent = 100, MeshId = 100, TextureContent = 95, TextureId = 95, TextureID = 95,
			ColorMap = 95, NormalMap = 95, MetalnessMap = 95, RoughnessMap = 95,
			Texture = 95, Image = 95, SoundId = 95,
			ShirtTemplate = 95, PantsTemplate = 95, Graphic = 95,
			-- 3) Material + Face + EmissionDirection.
			Material = 85, MaterialPattern = 85, BaseMaterial = 85,
			Face = 85, EmissionDirection = 85,
			-- 4) Size: mesh yüklendikten SONRA. Bu origin'in verdiği gerçek boyut.
			Size = 70,
			-- 5) Scale ve diğer visual property'ler.
			Scale = 60, VertexColor = 60,
			-- 6) Color/renk.
			BrickColor = 55, Color = 50, Color3 = 50, Transparency = 50, Reflectance = 50,
			-- 7) Weld/Motor/Attachment referansları (diğer part'ların yüklendiğinden emin ol).
			Part0 = 30, Part1 = 30, Attachment0 = 30, Attachment1 = 30, PrimaryPart = 30,
			-- 8) Pozisyon en son.
			CFrame = 10, Position = 10, Orientation = 10,
			-- Attributes en son.
			__attributes = -10,
		}
		local orderedProps = {}
		for _, prop in ipairs(op.props or {}) do
			table.insert(orderedProps, prop)
		end
		table.sort(orderedProps, function(a, b)
			local pa = PROP_PRIORITY[a.k] or 60
			local pb = PROP_PRIORITY[b.k] or 60
			return pa > pb
		end)
		for _, prop in ipairs(orderedProps) do
			local same = false
			if op.refresh and prop.k ~= "__attributes" then
				local decodedRefresh = decodeSyncValue(prop.v)
				local okCur, current = pcall(function() return inst[prop.k] end)
				same = okCur and decodedRefresh ~= nil and current == decodedRefresh
			end
			if not same and not applyProperty(inst, prop.k, prop.v) then
				table.insert(sync.deferred, { inst = inst, key = prop.k, value = prop.v })
			end
		end
		-- TEXTURE/SIZE FIX: mesh asset asenkron yüklendiği için ilk uygulamada Scale/Size/TextureId
		-- kaybolabilir (mesh daha gelmemişken Scale set edilirse engine değeri siliyor). Kritik
		-- property'leri bir frame sonra ve sonra yine 0.5s sonra tekrar uygula; mesh yüklendikten
		-- sonra boyut doğru oturur.
		local CRITICAL = { "MeshId", "TextureId", "TextureID",
			"Texture", "Image", "ColorMap", "NormalMap", "MetalnessMap", "RoughnessMap",
			"Size", "Scale", "Offset", "VertexColor", "Color", "Color3", "Transparency",
			"StudsPerTileU", "StudsPerTileV", "OffsetStudsU", "OffsetStudsV",
			"ImageRectOffset", "ImageRectSize", "ScaleType", "SliceCenter", "SliceScale", "TileSize",
			"MeshType", "Face" }
		local critValues = {}
		for _, prop in ipairs(op.refresh and {} or orderedProps) do
			for _, k in ipairs(CRITICAL) do
				if prop.k == k then
					critValues[prop.k] = prop.v
					break
				end
			end
		end
		if next(critValues) ~= nil then
			local function reapply()
				if not inst or not inst.Parent then return end
				sync.applying = true
				local latest = sync.latest[inst]
				for k, v in pairs(critValues) do
					-- The newest value the origin sent for this property, the snapshot only as fallback.
					local current = latest and latest[k]
					if current == nil then
						current = v
					end
					pcall(applyProperty, inst, k, current)
				end
				sync.applying = false
			end
			task.defer(reapply)
			task.delay(0.1, reapply)
			task.delay(0.5, reapply)
			task.delay(1.5, reapply)
			task.delay(3, reapply)
			task.delay(6, reapply)
			-- PERSISTENT SIZE GUARD: MeshPart'ta MeshContent async yüklenir ve engine Size'ı mesh'in
			-- default boyutuna reset edebiliyor. Size Changed'i izle, hedeften saparsa hemen geri yaz.
			-- 15 saniye boyunca aktif → her mesh load tamamlanana kadar koruma var.
			-- Size / Scale guard: the engine resizes a MeshPart when its mesh finishes loading. For 15s
			-- any drift is put back to the NEWEST value the origin sent (sync.sizeTargets), so a real
			-- resize from the origin is kept and only the engine's auto-resize is undone.
			local function guard(property, targets)
				if not critValues[property] or not targets[inst] then
					return
				end
				pcall(function()
					local conn
					local guardUntil = os.clock() + 15
					conn = inst:GetPropertyChangedSignal(property):Connect(function()
						local target = targets[inst]
						if os.clock() > guardUntil or not target then
							if conn then conn:Disconnect() end
							return
						end
						local ok, current = pcall(function() return inst[property] end)
						if ok and current and (current - target).Magnitude > 0.01 then
							sync.applying = true
							pcall(function() inst[property] = target end)
							sync.applying = false
						end
					end)
					track(conn)
				end)
			end
			guard("Size", sync.sizeTargets)
			guard("Scale", sync.scaleTargets)
		end
		local parent = resolveRef(op.parent)
		if parent then
			pcall(function() inst.Parent = parent end)
			fixAnchor(inst)
		else
			table.insert(sync.deferred, { inst = inst, parent = op.parent })
		end
	elseif action == "set" then
		local inst = resolveRef(op.ref)
		if inst and not applyProperty(inst, op.k, op.v) then
			table.insert(sync.deferred, { inst = inst, key = op.k, value = op.v })
		end
	elseif action == "parent" then
		local inst = sync.byId[op.id] or sync.ownById[op.id]
		if not inst then
			return
		end
		local parent = resolveRef(op.parent)
		if parent then
			pcall(function() inst.Parent = parent end)
			fixAnchor(inst)
			-- A held tool copy that was dropped: off the arm, anchored, following the owner's drop.
			if not underRealCharacter(inst) then
				for _, node in ipairs(inst:GetDescendants()) do
					local okRep, rep = pcall(node.GetAttribute, node, REPLICA_ATTRIBUTE)
					if node:IsA("Weld") and node.Name == "RightGrip" and okRep and rep then
						pcall(function() node:Destroy() end)
					elseif node:IsA("BasePart") then
						pcall(fixAnchor, node)
					end
				end
			end
		else
			table.insert(sync.deferred, { inst = inst, parent = op.parent })
		end
	elseif action == "reparent" then
		local inst = resolveRef(op.ref)
		if not inst then
			return
		end
		if op.detach then
			pcall(function() inst.Parent = nil end)
			return
		end
		local parent = resolveRef(op.parent)
		if parent then
			pcall(function() inst.Parent = parent end)
			fixAnchor(inst)
		else
			table.insert(sync.deferred, { inst = inst, parent = op.parent })
		end
	elseif action == "drive" then
		-- Deferred: the owner's scripts react to it and their writes must be mirrored, not swallowed.
		task.defer(applyDrive, op)
	elseif action == "touch" then
		task.defer(applyTouch, op)
	elseif action == "kick" then
		if op.user == localPlayer.UserId then
			log("[mirror] kicked by the origin: " .. tostring(op.reason), WARN_COLOR)
			task.delay(0.2, function() localPlayer:Kick(tostring(op.reason)) end)
		end
	elseif action == "respawn" then
		local humanoid = op.user == localPlayer.UserId and localPlayer.Character
			and localPlayer.Character:FindFirstChildOfClass("Humanoid")
		if humanoid then
			pcall(function() humanoid.Health = 0 end)
		end
	elseif action == "remove" then
		local inst = sync.byId[op.id]
		sync.byId[op.id] = nil
		sync.grips[op.id] = nil
		if inst then
			pcall(function() inst:Destroy() end)
		end
	elseif action == "call" then
		local inst = resolveRef(op.ref)
		if not inst or not (WORLD_CALL_METHODS[op.m] or (FE_CALL_METHODS[op.m] and op.m ~= "AddItem")) then
			return
		end
		local encoded = op.args or {}
		local args = { n = encoded.n or 0 }
		for _, item in ipairs(encoded.list or {}) do
			args[item.i] = decodeSyncValue(item.v)
		end
		pcall(function() inst[op.m](inst, table.unpack(args, 1, args.n)) end)
		if op.m == "Destroy" or op.m == "Remove" then
			local okId, sid = pcall(inst.GetAttribute, inst, SYNC_ID_ATTRIBUTE)
			if okId and sid then
				sync.byId[sid] = nil
			end
		end
	elseif action == "request" then
		-- A client that just joined wants everything we track.
		resendAll()
	elseif action == "limb" then
		-- How someone's body part looks (invisible, ghost, rainbow): same part, same player, visuals only.
		if not SSEmu.limbVisualKeys[op.k] then
			return
		end
		local player = playersService:GetPlayerByUserId(tonumber(op.uid) or 0)
		local character = player and player.Character
		local part = character and character:FindFirstChild(tostring(op.name))
		local decoded = part and part:IsA("BasePart") and decodeSyncValue(op.v)
		if decoded ~= nil then
			pcall(function() part[op.k] = decoded end)
		end
	elseif action == "pickup" then
		-- Someone's dropped tool was picked up. Not us: its remove op follows and it disappears here.
		if tonumber(op.uid) ~= localPlayer.UserId then
			return
		end
		-- Us: copy the mirrored tool now, the remove op right behind this one destroys it.
		local mirrored = op.id and sync.byId[op.id]
		local fallback
		if mirrored then
			pcall(function()
				mirrored.Archivable = true
				fallback = mirrored:Clone()
			end)
		end
		task.defer(SSEmu.receiveTool, op, fallback)
	elseif action == "tween" then
		-- The origin played a tween: the same tween runs here, smooth, on our copy of the target.
		local target = resolveRef(op.ref)
		local info = decodeValue(op.info)
		local goals = decodeValue(op.goals)
		if not (target and realTypeof(info) == "TweenInfo" and type(goals) == "table") then
			return
		end
		sync.remoteTweens = sync.remoteTweens or {}
		local previous = sync.remoteTweens[op.id]
		if previous then
			pcall(function() previous:Cancel() end)
		end
		local ok, tween = pcall(function()
			return SSEmu.tweenService:Create(target, info, goals)
		end)
		if ok and tween then
			sync.remoteTweens[op.id] = tween
			pcall(function() tween:Play() end)
			pcall(function()
				tween.Completed:Connect(function()
					if sync.remoteTweens[op.id] == tween then
						sync.remoteTweens[op.id] = nil
					end
				end)
			end)
		end
	elseif action == "tweenctl" then
		local tween = sync.remoteTweens and sync.remoteTweens[op.id]
		if tween and (op.m == "Pause" or op.m == "Cancel") then
			pcall(function() tween[op.m](tween) end)
		end
	elseif action == "team" then
		-- A script put a player in a team: the same Player gets the same Team here.
		local player = playersService:GetPlayerByUserId(tonumber(op.uid) or 0)
		if not player or (op.k ~= "Team" and op.k ~= "TeamColor" and op.k ~= "Neutral") then
			return
		end
		local value = op.v
		local decoded
		if value == false and op.k == "Team" then
			decoded = nil
		else
			decoded = decodeSyncValue(value)
			-- The Team itself may still be on its way (mirrored in the same batch): try again shortly.
			if decoded == nil and isPendingRef(value) then
				op.tries = (op.tries or 0) + 1
				if op.tries <= 25 then
					task.delay(0.2, function()
						sync.applying = true
						pcall(applyOp, op)
						sync.applying = false
					end)
				end
				return
			end
		end
		pcall(function() player[op.k] = decoded end)
	elseif action == "grip" then
		-- Another player holds an emulated tool: weld our copy into their hand.
		if not sync.applyGrip(op) then
			op.tries = (op.tries or 0) + 1
			if op.tries <= 20 then
				task.delay(0.2, function()
					sync.applying = true
					pcall(applyOp, op)
					sync.applying = false
				end)
			end
		end
	elseif action == "clone" then
		-- Exact copy of a piece: swapped in now if its source is here, after the download otherwise.
		if type(op.src) ~= "string" or type(op.key) ~= "string" then
			return
		end
		local entry = sync.cloneSources[op.src] or sync.loadCloneSource(op.src)
		if entry.state == "ready" then
			sync.swapInClone(op)
		elseif entry.state == "loading" then
			table.insert(entry.pending, op)
		end
	elseif action == "humanoid" then
		local player = playersService:GetPlayerByUserId(tonumber(op.uid) or 0)
		local character = player and player.Character
		local humanoid = character and character:FindFirstChildOfClass("Humanoid")
		local decoded = humanoid and decodeSyncValue(op.v)
		if decoded == nil then
			return
		end
		if player == localPlayer then
			-- Addressed to us (we were hit, slowed, healed): our own Humanoid, the write is real.
			pcall(function() humanoid[op.k] = decoded end)
			return
		end
		-- Someone else's character: we do not simulate it, only the health bar and name follow.
		-- Death, sitting, hip height and speed come natively from its owner, writing them here
		-- would break that character on our screen.
		if op.k == "MaxHealth" or op.k == "DisplayName" or (op.k == "Health" and type(decoded) == "number" and decoded > 0) then
			pcall(function() humanoid[op.k] = decoded end)
		end
	end
end

---Apply a batch of ops. The applying flag keeps our own writes from being sent back out.
---@param ops table
local function applyWorld(ops)
	sync.applying = true
	for _, op in ipairs(ops or {}) do
		SSEmu.diagStats.received = SSEmu.diagStats.received + 1
		local ok, err = pcall(applyOp, op)
		if not ok then
			SSEmu.diagStats.applyErrors = SSEmu.diagStats.applyErrors + 1
			SSEmu.diagStats.lastError = tostring(op.a) .. ": " .. tostring(err)
			log("[mirror] " .. tostring(op.a) .. " failed: " .. tostring(err), WARN_COLOR)
		end
	end
	pcall(retryDeferred)
	sync.applying = false
end

-- Instances the emulation parents into the world by itself (an equipped tool, a delivered map) go through
-- here, the __newindex hook only sees what a script wrote.
---Instances added to the world without a script Parent write: emulation content, and while FE is off
---anything made on this client (Instance.new with a parent argument).
---@param node Instance
local function onWorldDescendant(node)
	if sync.applying or not (sync.enabled and replication.enabled) then
		return
	end
	-- LAG FIX: karakter iskelet part'ı YENİ eklendiğinde mirror'a atma (karakter spawn'ı Roblox
	-- native replike eder; limb eklenmesi başlı başına 20+ snapshot demek). Property değişimleri
	-- ise queueSet'ten (tracked olmasalar da takip ediliyorlarsa) geçer.
	if isNativeCharacterPart(node) then
		return
	end
	if isReplica(node) then
		return
	end
	-- Gear on our own character always travels (forced): the others must see what we hold and wear,
	-- even when every client got the same tool from its own convert.
	local okClass, className = pcall(function() return node.ClassName end)
	if not okClass then return end
	local isGear = className == "Tool" or className == "HopperBin" or className == "Accessory"
		or className == "Hat" or className == "Accoutrement"
		or className == "Shirt" or className == "Pants" or className == "ShirtGraphic"
		or className == "CharacterMesh"
	if isGear then
		local okParent, parent = pcall(function() return node.Parent end)
		local okTag, gearTagged = pcall(node.GetAttribute, node, SOURCE_TAG)
		if okParent and parent and playersService:GetPlayerFromCharacter(parent) == localPlayer then
			-- Native avatar items replicate by themselves: never copied, that is what broke avatars.
			if okTag and gearTagged then
				task.defer(queueAdd, node, false, true)
			end
			return
		end
	end
	-- Script made content (tagged) travels; untagged native map content never does.
	local ok, tagged = pcall(node.GetAttribute, node, SOURCE_TAG)
	local made = fe.off and fe.created[node]
	if (ok and tagged) or made then
		task.defer(queueAdd, node, made ~= "game")
	end
end

track(workspaceService.DescendantAdded:Connect(onWorldDescendant))
local function hookService(svc)
	if not svc or svc == workspaceService then return end
	pcall(function()
		track(svc.DescendantAdded:Connect(onWorldDescendant))
	end)
end
for svc in pairs(getMirrorServices()) do
	hookService(svc)
end
-- Full-convert mode: PlayerGui/PlayerScripts/Backpack mirror hook'u yok, her client kendi
-- convert'inden kendi içeriğini oluşturuyor.
-- Ezproxy iç konteynerlerine (Re2lua/Modules) eklenen non-script içeriği de mirror'a al.
local function onInternalDescendant(node)
	if sync.applying or not (sync.enabled and replication.enabled) then return end
	if isReplica(node) then return end
	if SYNC_SKIP_CLASSES[node.ClassName] then return end
	-- Araba direksiyon GUI template'leri, part'lar, remote'lar, mesh'ler — hepsi geçer.
	task.defer(queueAdd, node, true)
end
track(serverRoot.DescendantAdded:Connect(onInternalDescendant))
track(moduleHolder.DescendantAdded:Connect(onInternalDescendant))
-- Teams / StarterPack / StarterPlayer go through hookService (tagged content only): queueing their
-- untagged children re-sent the game's own native teams and tools, a duplicate on every client.
-- Backpack/Character'a tool eklenince (gear) her client'a replika gönder: tool'un parent'ı
-- Players.<name>.Backpack veya .Character olduğu için encodePath origin'in UserId'si ile paketler,
-- decode replica'da aynı oyuncunun Backpack'ini / Character'ını bulur.
-- Sadece karaktere eklenmiş (equipped) gear/accessory/shirt/pants mirror'a atılır.
-- Backpack'e eklenenler mirror'a girmez çünkü her client kendi convert'ini çalıştırıyor zaten,
-- tool kendi Backpack'inde var. Mirror sadece "YOUR character şu anda bunu taşıyor" bilgisini yayar.
-- Scoped: Luau allows 200 locals per function, these watchers only need theirs inside.
do
local function watchPlayerForGear(player)
	local function onChild(child)
		if not (sync.enabled and replication.enabled) then return end
		if isReplica(child) then return end
		local okClass, className = pcall(function() return child.ClassName end)
		if not okClass then return end
		if className == "Tool" or className == "HopperBin" or className == "Accessory"
			or className == "Hat" or className == "Accoutrement"
			or className == "Shirt" or className == "Pants" or className == "ShirtGraphic"
			or className == "CharacterMesh" then
			-- Native avatar items and real tools are already shown to everyone by Roblox; sending them
			-- again stacks a second, unattached copy on the character. Only emulated gear travels.
			local okTag, tagged = pcall(child.GetAttribute, child, SOURCE_TAG)
			if not (okTag and tagged) then
				return
			end
			task.defer(queueAdd, child, false, true)
			if className == "Tool" then
				task.defer(SSEmu.sendGrip, child)
			end
		end
	end
	local function onCharacter(character)
		if not character then return end
		track(character.ChildAdded:Connect(onChild))
		for _, c in ipairs(character:GetChildren()) do onChild(c) end
	end
	if player.Character then onCharacter(player.Character) end
	track(player.CharacterAdded:Connect(onCharacter))
end
-- Sadece kendi localPlayer'ımız için izle; diğer oyuncuların tool'u zaten bize onların mirror'ından gelir.
task.defer(watchPlayerForGear, localPlayer)

-- HUMANOID STATE MIRROR: sadece Humanoid state property'leri (Health, WalkSpeed, JumpPower,
-- scale, etc.) mirror'a gider. Native limb'lere YAZMIYORUZ — karakter korupsiyonu önlenir,
-- Roblox karakter iskeletini kendi native replication ile hallediyor. Özel "humanoid" op'u
-- gönderilir; replica origin'in UserId'sine göre Humanoid'i bulup property yazar.
local HUMANOID_WATCH_PROPS = {
	"Health", "MaxHealth", "WalkSpeed", "JumpPower", "JumpHeight", "HipHeight",
	"DisplayName", "AutoRotate", "CameraOffset", "BreakJointsOnDeath",
	"HealthDisplayType", "NameDisplayDistance", "HealthDisplayDistance",
	"BodyHeightScale", "BodyWidthScale", "BodyDepthScale", "HeadScale",
}
local function sendHumanoidState(humanoid, prop)
	if sync.applying or not (sync.enabled and replication.enabled) then return end
	local okVal, value = pcall(function() return humanoid[prop] end)
	if not okVal then return end
	local encoded = encodeSyncValue(value)
	if encoded == nil then return end
	pushOp("humanoid|" .. prop, {
		a = "humanoid", uid = localPlayer.UserId, k = prop, v = encoded,
	})
end
local function watchHumanoid(character)
	if not character then return end
	local humanoid = character:FindFirstChildOfClass("Humanoid")
	if not humanoid then
		local conn
		conn = character.ChildAdded:Connect(function(child)
			if child:IsA("Humanoid") then
				if conn then pcall(function() conn:Disconnect() end) end
				watchHumanoid(character)
			end
		end)
		track(conn)
		return
	end
	-- İlk state'i gönder.
	for _, prop in ipairs(HUMANOID_WATCH_PROPS) do
		sendHumanoidState(humanoid, prop)
	end
	-- Her property Changed'ini dinle.
	for _, prop in ipairs(HUMANOID_WATCH_PROPS) do
		pcall(function()
			track(humanoid:GetPropertyChangedSignal(prop):Connect(function()
				sendHumanoidState(humanoid, prop)
			end))
		end)
	end
end
if localPlayer.Character then
	task.defer(watchHumanoid, localPlayer.Character)
end
track(localPlayer.CharacterAdded:Connect(function(character)
	task.defer(function()
		task.wait(0.3)
		watchHumanoid(character)
	end)
end))
end

-- Player.Team / TeamColor / Neutral travel as "team" ops from SSEmu.worldWrite (any player a script
-- assigns, ours included). The old per-property watcher never sent: a Player has no path reference.

---FE off with scope "all": Instance.new from game LocalScripts goes through a Parent write, so the
---__newindex hook sees what they make even when the parent is passed to the constructor.
local function installCreationHook()
	if fe.newHooked or not (hookfunction and newcclosure) then
		return
	end
	fe.newHooked = true
	local oldNew
	local ok, err = pcall(function()
		oldNew = hookfunction(realInstance.new, newcclosure(function(className, parent, ...)
			if not (active and fe.off and fe.scope == "all") or parent == nil then
				return oldNew(className, parent, ...)
			end
			local created = oldNew(className)
			fe.created[created] = checkcaller() and "exec" or "game"
			created.Parent = parent
			return created
		end))
	end)
	if not ok then
		fe.newHooked = false
		log("FE: Instance.new hook failed, constructor parents are caught through DescendantAdded only (" .. tostring(err) .. ")", WARN_COLOR)
	end
end

---Start mirroring: pick up what is already in the world, start the tick loop, ask for the others' state.
function SSEmu.startMirror()
	if not (sync.enabled and replication.enabled) then
		return
	end
	pcall(function()
		local nodes = workspaceService:GetDescendants()
		-- Ezproxy iç konteynerlerindeki non-script içerik (araba parçaları, template GUI'ler) snapshot'a dahil.
		for _, node in ipairs(serverRoot:GetDescendants()) do
			if not SYNC_SKIP_CLASSES[node.ClassName] then
				table.insert(nodes, node)
			end
		end
		for _, node in ipairs(moduleHolder:GetDescendants()) do
			if not SYNC_SKIP_CLASSES[node.ClassName] then
				table.insert(nodes, node)
			end
		end
		-- Every mirrored service (Teams, Lighting, StarterPack, ...), FE disabled or not; only its tagged
		-- (script made) content is taken below.
		for svc in pairs(getMirrorServices()) do
			if svc ~= workspaceService then
				for _, node in ipairs(svc:GetDescendants()) do
					if not SYNC_SKIP_CLASSES[node.ClassName] then
						table.insert(nodes, node)
					end
				end
			end
		end
		for _, node in ipairs(nodes) do
			-- Only tagged (script made) content, native map content never travels.
			local ok, tagged = pcall(node.GetAttribute, node, SOURCE_TAG)
			if ok and tagged and not sync.tracked[node] then
				queueAdd(node)
			end
		end
		-- Gear already on our character is forced through, convert mode or not.
		if localPlayer.Character then
			for _, child in ipairs(localPlayer.Character:GetChildren()) do
				local okClass, className = pcall(function() return child.ClassName end)
				if okClass and (className == "Tool" or className == "HopperBin" or className == "Accessory"
					or className == "Hat" or className == "Accoutrement" or className == "Shirt"
					or className == "Pants" or className == "ShirtGraphic" or className == "CharacterMesh")
					and not sync.tracked[child] and not isReplica(child) then
					local okTag, gearTagged = pcall(child.GetAttribute, child, SOURCE_TAG)
					if okTag and gearTagged then
						queueAdd(child, false, true)
						if className == "Tool" then
							task.defer(SSEmu.sendGrip, child)
						end
					end
				end
			end
		end
	end)
	task.spawn(syncLoop)
	task.delay(1, function()
		if sync.enabled and replication.enabled then
			pushOp(nil, { a = "request" })
		end
	end)
end

---Switch the mirror on or off at run time.
---@param enabled boolean
function SSEmu.setMirror(enabled)
	if not enabled and fe.off then
		return log("Mirror stays on while FilteringEnabled is off, run .fe enable first", WARN_COLOR)
	end
	sync.enabled = enabled == true
	if sync.enabled then
		SSEmu.startMirror()
	end
end

---Whether the mirror is on (replicas then wait for world state instead of running scripts).
---@return boolean
function SSEmu.isMirror()
	return sync.enabled
end

---Turn FilteringEnabled on or off. Off = FE disabled: every client's world changes reach every client.
---@param enabled boolean
---@param scope string? "executor" (executor + sandbox) or "all" (game LocalScripts too)
function SSEmu.setFilteringEnabled(enabled, scope)
	if scope == "all" or scope == "executor" then
		fe.scope = scope
	end
	fe.off = enabled == false
	SSEmu.feOff = fe.off
	SSEmu.feOffAll = fe.off and fe.scope == "all"
	if not fe.off then
		table.clear(fe.journal)
		table.clear(fe.journalIndex)
		return
	end
	if fe.scope == "all" then
		installCreationHook()
	end
	if not replication.enabled then
		SSEmu.startReplication()
	end
	sync.enabled = true
	SSEmu.startMirror()
end

SSEmu.feOff = fe.off
SSEmu.feOffAll = fe.off and fe.scope == "all"
if fe.off then
	-- shared.SSEmuConfig.filteringEnabled = false starts with FE disabled once everything is defined.
	task.defer(SSEmu.setFilteringEnabled, false)
end

---Switch between convert mode (every client runs broadcast commands, mirror carries cross-player
---state) and mirror mode (only the origin runs them, everything it makes streams).
---@param mode string
function SSEmu.setFeMode(mode)
	if mode ~= "convert" and mode ~= "mirror" then
		return
	end
	fe.mode = mode
	SSEmu.feMode = mode
end

---FilteringEnabled state and scope.
---@return boolean, string
function SSEmu.getFilteringEnabled()
	return not fe.off, fe.scope
end

---Resend everything we track and ask the others for theirs.
function SSEmu.resync()
	resendAll()
	pushOp(nil, { a = "request" })
end

-- Handlers for events coming from other clients, all run as replicas without GUIs.
local replicaHandlers = {
	script = function(payload)
		-- Mirror mode: the origin runs the script, its world state arrives through "world" events.
		if sync.enabled then
			return
		end
		SSEmu.execute(payload.source, "Replica", true, true, payload.origin)
	end,
	give = function(payload)
		if sync.enabled then
			return
		end
		giveAsset(payload.id, true)
	end,
	convert = function(payload)
		if sync.enabled then
			return
		end
		local target = resolvePath(payload.path)
		if target then
			SSEmu.convert(target, true)
		end
	end,
	world = function(payload)
		applyWorld(payload.ops)
	end,
	remote = function(payload)
		-- An answer to our InvokeServer on someone else's remote.
		if payload.method == "InvokeResult" then
			local pending = SSEmu.pendingInvokes and SSEmu.pendingInvokes[payload.requestId]
			if pending and payload.target == localPlayer.UserId then
				pending.results = decodeArgs(payload.args or {})
				pending.done = true
			end
			return
		end

		-- By mirror id first (exactly the same remote everywhere), the path for older clients.
		local inst, own
		if type(payload.sid) == "string" then
			inst, own = SSEmu.remoteBySid(payload.sid)
		end
		if not inst then
			inst = decodePath(payload.path)
			own = nil
		end
		local data = inst and lookupRemote(inst, true)
		if not data then
			return
		end

		local args = decodeArgs(payload.args or {})
		local sender = payload._from and playersService:GetPlayerByUserId(payload._from.userId) or localPlayer

		-- Another client invoked our RemoteFunction: our OnServerInvoke answers, with them as the player.
		if payload.method == "InvokeServer" then
			if own == false or not data.serverInvoke then
				return
			end
			task.spawn(function()
				local results = table.pack(pcall(data.serverInvoke, sender, table.unpack(args, 1, args.n)))
				if not results[1] then
					log("OnServerInvoke failed for " .. sender.Name .. ": " .. tostring(results[2]), ERROR_COLOR)
					results = { n = 1, true }
				end
				SSEmu.replicate("remote", {
					sid = payload.sid, method = "InvokeResult", requestId = payload.requestId,
					target = sender.UserId, args = encodeArgs(table.unpack(results, 2, results.n)),
				})
			end)
			return
		end

		-- Fire the signals directly so the replica never sends the call back out.
		if payload.method == "FireServer" then
			-- Only the remote's owner runs its server side, the others would run it a second time.
			if own == false then
				return
			end
			data.serverSignal:Fire(sender, table.unpack(args, 1, args.n))
		elseif payload.method == "FireClient" then
			if payload.target == localPlayer.UserId then
				data.clientSignal:Fire(table.unpack(args, 1, args.n))
			end
		elseif payload.method == "FireAllClients" then
			data.clientSignal:Fire(table.unpack(args, 1, args.n))
		end
	end,
}

---Apply one incoming event safely.
---@param event table
function applyEvent(event)
	local handler = replicaHandlers[event.type]
	if not handler then
		return
	end

	local ok, err = pcall(handler, event.payload or {})
	if not ok then
		log("[replica] " .. event.type .. " failed: " .. tostring(err), ERROR_COLOR)
	end
end

---Long-poll the relay until detach or disable.
local function pollLoop()
	while active and replication.enabled do
		local path = string.format(
			"/poll?room=%s&since=%d&client=%s&wait=15",
			httpService:UrlEncode(RELAY_ROOM),
			replication.since,
			httpService:UrlEncode(replication.clientId)
		)

		local response, err = relayRequest("GET", path)
		if not response then
			replication.connected = false
			replication.failures = replication.failures + 1
			warnRelayOnce("Relay unreachable (" .. tostring(err) .. "), retrying quietly.")
			-- Back off up to 30 seconds so a dead relay does not spam requests.
			task.wait(math.min(3 * replication.failures, 30))
			continue
		end

		if not replication.connected then
			replication.connected = true
			replication.warned = false
			replication.failures = 0
			log("Relay connected, room: " .. RELAY_ROOM, INFO_COLOR)
		end

		for _, event in ipairs(response.events or {}) do
			replication.since = math.max(replication.since, event.seq)
			if event.client ~= replication.clientId then
				task.spawn(applyEvent, event)
			end
		end
		replication.since = math.max(replication.since, response.last or -1)
	end
end

---Start replication when it is not already running.
function SSEmu.startReplication()
	if replication.enabled then
		return
	end
	replication.enabled = true
	replication.since = -1
	replication.warned = false
	replication.failures = 0
	if RELAY_URL == PROXY_URL then
		-- The proxy relays events over the command channel.
		replication.connected = true
	else
		task.spawn(pollLoop)
	end
	SSEmu.startMirror()
end

---Stop replication.
function SSEmu.stopReplication()
	replication.enabled = false
	replication.connected = false
end

commandHandlers.rep = function(argument)
	if argument == "off" then
		SSEmu.stopReplication()
	elseif argument == "on" then
		SSEmu.startReplication()
	end
	log("Replication: " .. (replication.enabled and "on" or "off") .. ", room " .. RELAY_ROOM
		.. ", relay " .. (replication.connected and "connected" or "not connected"), INFO_COLOR)
end

commandHandlers.mirror = function(argument)
	if argument == "on" or argument == "off" then
		SSEmu.setMirror(argument == "on")
	end
	log("Mirror: " .. (sync.enabled and "on (world state is sent, replicas do not run scripts)" or "off (replicas run the scripts)"), INFO_COLOR)
end

commandHandlers.fe = function(argument)
	local action, scope = argument:match("^(%S*)%s*(%S*)")
	if action == "disable" or action == "off" then
		SSEmu.setFilteringEnabled(false, scope ~= "" and scope or nil)
	elseif action == "enable" or action == "on" then
		SSEmu.setFilteringEnabled(true)
	end
	local enabled, current = SSEmu.getFilteringEnabled()
	log("FilteringEnabled: " .. tostring(enabled) .. (enabled and "" or " (scope " .. current .. ", " .. #fe.journal .. " server change(s) kept)"), INFO_COLOR)
end

commandHandlers.resync = function()
	SSEmu.resync()
	log("Mirror: resent " .. sync.count .. " tracked instance(s)", INFO_COLOR)
end

commandHandlers.room = function(argument)
	if argument == "" then
		return log("Room: " .. RELAY_ROOM, INFO_COLOR)
	end
	SSEmu.stopReplication()
	RELAY_ROOM = argument
	task.wait(0.2)
	SSEmu.startReplication()
	log("Joined room " .. RELAY_ROOM, INFO_COLOR)
end

end

-- ═══════════════════════════════════════════════════════════════════
-- EZPROXY: headless console bridge, replaces the old GUI
-- ═══════════════════════════════════════════════════════════════════

local Proxy = {
	queue = {},
	handlers = {},
	maxScripts = 1500,
	maxDecompiles = 150,
	chunkSize = 150,
	clientId = tostring(localPlayer.UserId) .. "-" .. tostring(math.random(100000, 999999)),
}

-- Pushed events and proxy clients share one id so the proxy never echoes an event back.
replication.clientId = Proxy.clientId

---Call the proxy and decode its JSON answer.
---@param method string
---@param path string
---@param body table?
---@return table?
function Proxy.send(method, path, body)
	local ok, response = pcall(executorRequest, {
		Url = PROXY_URL .. path,
		Method = method,
		Headers = { ["Content-Type"] = "application/json" },
		Body = SSEmu.encodeJson(body),
	})
	if not ok or not response or (response.StatusCode or response.Status) ~= 200 then
		return nil
	end

	local decoded, result = pcall(httpService.JSONDecode, httpService, response.Body)
	return decoded and result or nil
end

Proxy.hidden = hiddenNames
Proxy.clean = cleanText

---Queue a console line for the proxy.
---@param text string
---@param kind string?
function Proxy.emit(text, kind)
	text = Proxy.clean(tostring(text))
	if text == "" then
		return
	end
	if #Proxy.queue > 1000 then
		table.remove(Proxy.queue, 1)
	end
	table.insert(Proxy.queue, { text = tostring(text), kind = kind or "print" })
end

---Map the internal log colors to proxy line kinds.
---@param color Color3?
---@return string
function Proxy.kindOf(color)
	if not color then
		return "print"
	end
	local red, green = math.floor(color.R * 255 + 0.5), math.floor(color.G * 255 + 0.5)
	if red == 255 and green == 90 then
		return "error"
	elseif red == 255 and green == 200 then
		return "warn"
	elseif green == 220 then
		return "info"
	end
	return "trace"
end

---Collect every script the client can see.
---@return table
function Proxy.collect()
	local list, seen = {}, {}

	local function add(inst)
		if seen[inst] or #list >= Proxy.maxScripts or not inst:IsA("LuaSourceContainer") then
			return
		end
		seen[inst] = true

		local ok, path = pcall(inst.GetFullName, inst)
		path = ok and path or inst.Name
		if path:find(CONTAINER_NAME, 1, true) then
			return
		end
		table.insert(list, { path = path, class = inst.ClassName, inst = inst })
	end

	pcall(function()
		for _, inst in ipairs(realGame:GetDescendants()) do
			add(inst)
		end
	end)
	if getnilinstances then
		pcall(function()
			for _, inst in ipairs(getnilinstances()) do
				add(inst)
			end
		end)
	end

	-- Modules first so their requires are decompiled within the budget.
	table.sort(list, function(a, b)
		if (a.class == "ModuleScript") ~= (b.class == "ModuleScript") then
			return a.class == "ModuleScript"
		end
		return a.path < b.path
	end)
	return list
end

---Read require targets out of decompiled source.
---@param inst Instance
---@return table
function Proxy.extractRequires(inst)
	if not decompile then
		return {}
	end
	local ok, source = pcall(decompile, inst)
	if not ok or type(source) ~= "string" then
		return {}
	end

	local found, seen = {}, {}
	for argument in source:gmatch("require%s*%(([^%)\n]+)%)") do
		argument = argument:match("^%s*(.-)%s*$"):sub(1, 120)
		if not seen[argument] and #found < 40 then
			seen[argument] = true
			table.insert(found, argument)
		end
	end
	return found
end

---Rebuild the script tree and send it to the proxy in chunks.
function Proxy.reconstruct()
	local list = Proxy.collect()
	local chunk, first = {}, true

	local function flush(last)
		Proxy.send("POST", "/scripts", { reset = first, items = chunk, last = last })
		chunk, first = {}, false
	end

	for index, entry in ipairs(list) do
		local requires = {}
		if index <= Proxy.maxDecompiles then
			requires = Proxy.extractRequires(entry.inst)
			if index % 5 == 0 then
				task.wait()
			end
		end
		table.insert(chunk, { path = entry.path, class = entry.class, requires = requires })
		if #chunk >= Proxy.chunkSize then
			flush(false)
		end
	end
	flush(true)
end

---Register this client with the proxy.
function Proxy.applyState(state)
	if type(state) ~= "table" then
		return
	end
	if type(state.feMode) == "string" and state.feMode ~= SSEmu.feMode then
		SSEmu.setFeMode(state.feMode)
	end
	if state.filteringEnabled ~= nil then
		local enabled, scope = SSEmu.getFilteringEnabled()
		if state.filteringEnabled ~= enabled or (not state.filteringEnabled and state.feScope and state.feScope ~= scope) then
			SSEmu.setFilteringEnabled(state.filteringEnabled, state.feScope)
		end
	end
	if state.replication == nil then
		return
	end
	if state.replication and not replication.enabled then
		SSEmu.startReplication()
	elseif not state.replication and replication.enabled then
		SSEmu.stopReplication()
	end
end

function Proxy.hello()
	Proxy.applyState(Proxy.send("POST", "/hello", {
		client = Proxy.clientId,
		name = localPlayer.Name,
		userId = localPlayer.UserId,
		placeId = realGame.PlaceId,
		jobId = realGame.JobId,
		hidden = Proxy.hidden,
	}))
end

---FULL-CONVERT MODE: convert/require/give/load dispatch EVERY client'ta koşar (her oyuncu kendi
---kopyasını çalıştırır) — GUI'ler lokal olarak çalışır, scale/mesh asenkron sorunu yok çünkü asset
---her client'ta kendi tarafında yüklenir. Mirror SADECE karakter üstündeki görünür gear +
---Humanoid.Health/scale + Player.Team'i taşır. Workspace'teki içeriği her client ayrı spawn eder.
---Exec komutları mirror modunda sadece origin'de koşar (one-shot).
---@param command table
---@return boolean
local function mirroredReplica(command)
	-- Convert mode: convert/require/give/load run on every client, like a real server handing
	-- each player the same thing. Mirror mode: only the origin runs them, the world streams.
	if SSEmu.feMode ~= "mirror" and (command.type == "convert" or command.type == "require"
		or command.type == "give" or command.type == "load") then
		return false
	end
	if command.replica and SSEmu.isMirror() then
		Proxy.emit("Mirror: origin runs it, state follows", "trace")
		return true
	end
	return false
end

---Run a broadcast command (require / give / load). In convert mode every client really owns its copy:
---no replica flag (its GUIs work), and the content is marked so the mirror does not send it twice.
---@param command table
---@param fn function
---@return boolean, any
function Proxy.runBroadcast(command, fn, ...)
	local thread = coroutine.running()
	local convertMode = SSEmu.feMode ~= "mirror"
	if convertMode and replication.enabled then
		SSEmu.dispatchThreads[thread] = true
	end
	local results = table.pack(pcall(fn, ...))
	SSEmu.dispatchThreads[thread] = nil
	return table.unpack(results, 1, results.n)
end

---Replica flag for a broadcast command: only mirror mode replicas are viewers, convert mode clients own it.
---@param command table
---@return boolean
function Proxy.replicaFlag(command)
	return command.replica == true and SSEmu.feMode == "mirror"
end

Proxy.handlers.exec = function(command)
	if mirroredReplica(command) then
		return
	end
	local ok = SSEmu.execute(command.source, "Ezproxy", command.replica, true, command.origin)
	Proxy.emit(ok and "Script executed" or "Script failed to run", ok and "info" or "error")
end

Proxy.handlers.mirror = function(command)
	SSEmu.setMirror(command.on == true)
	Proxy.emit("Mirror " .. (command.on and "on: world state is sent, replicas do not run scripts" or "off: replicas run the scripts"), "info")
end

Proxy.handlers.fe = function(command)
	SSEmu.setFilteringEnabled(command.enabled ~= false, command.scope)
	local enabled, scope = SSEmu.getFilteringEnabled()
	Proxy.emit(enabled and "FilteringEnabled on: normal filtering, only emulated content is mirrored"
		or ("FilteringEnabled off (" .. scope .. "): every client's world changes replicate to every client"), enabled and "info" or "warn")
end

Proxy.handlers.resync = function()
	SSEmu.resync()
	Proxy.emit("Mirror: world state resent", "info")
end

-- .share <path>: push something this client sees to everyone by hand (content the game built locally
-- before the engine loaded carries no tag and cannot be told apart from the map on its own).
Proxy.handlers.share = function(command)
	if command.replica then
		return
	end
	local target = tostring(command.target or "")
	local ok, inst = pcall(resolvePath, target)
	if not ok or realTypeof(inst) ~= "Instance" or inst == realGame then
		return Proxy.emit("Share: nothing at " .. target, "warn")
	end
	local nodes = inst:GetDescendants()
	table.insert(nodes, 1, inst)
	for _, node in ipairs(nodes) do
		pcall(node.SetAttribute, node, SOURCE_TAG, true)
	end
	if not SSEmu.share(inst) then
		return Proxy.emit("Share: " .. target .. " is not in a mirrored place (Workspace, Lighting, Teams, ReplicatedStorage...)", "warn")
	end
	Proxy.emit("Shared " .. inst:GetFullName() .. " (" .. #nodes .. " instances)", "info")
end

Proxy.handlers.diag = function()
	Proxy.emit("[" .. localPlayer.Name .. "] " .. SSEmu.diagReport(), "server")
end

Proxy.handlers.femode = function(command)
	SSEmu.setFeMode(command.mode)
	Proxy.emit("FE mode: " .. SSEmu.feMode .. (SSEmu.feMode == "mirror"
		and " (origin runs commands, everything streams)"
		or " (every client runs commands, mirror carries cross-player state)"), "info")
end

Proxy.handlers.require = function(command)
	if mirroredReplica(command) then
		return
	end
	local target = tonumber(command.target)
	if not target then
		target = resolvePath(tostring(command.target)) or command.target
	end

	local ok, result
	if type(target) == "number" then
		ok, result = Proxy.runBroadcast(command, loadAsset, target, Proxy.replicaFlag(command))
	else
		ok, result = Proxy.runBroadcast(command, smartRequire, target, nil)
	end
	if ok then
		Proxy.emit("Required " .. tostring(command.target) .. " -> " .. type(result), "info")
	else
		Proxy.emit("Require failed: " .. tostring(result), "error")
	end
end

Proxy.handlers.replication = function(command)
	if command.on then
		SSEmu.startReplication()
	else
		SSEmu.stopReplication()
	end
	Proxy.emit("Replication " .. (command.on and "enabled" or "disabled"), "info")
end

Proxy.handlers.give = function(command)
	if mirroredReplica(command) then
		return
	end
	local assetId = tonumber(command.target)
	if not assetId then
		return Proxy.emit("Usage: .give <assetId>", "warn")
	end
	local ok, err = Proxy.runBroadcast(command, giveAsset, assetId, Proxy.replicaFlag(command))
	if not ok then
		Proxy.emit("Give failed: " .. tostring(err), "error")
	end
end

do
-- Runtime appended to every converted script, placeholders are filled by the bundler.
local BUNDLE_RUNTIME = [=====[
-- Converted by Ezproxy: standalone client-sided server emulation (lite runtime v2).
local MAIN_TAG = __TAG__
local TREES = {
__TREES__
}
local ENTRIES = {
__DATA__
}
-- The original loader line (require(id).load("name")), false when only the asset itself was converted.
local ENTRY = __ENTRY__

-- When the live SSEmu is already attached it owns the globals, so the asset is handed to it instead
-- of stacking a second emulation on top of its mocks.
do
	local live = type(shared) == "table" and rawget(shared, "SSEmu")
	if type(live) == "table" and live.running then
		local main
		for _, t in ipairs(TREES) do if t.tag == MAIN_TAG then main = t end end
		if main and main.id and type(live.runConverted) == "function" then
			return live.runConverted(main.id, ENTRY or nil)
		end
		if main and main.path and type(live.convert) == "function" then
			local cur = game
			for seg in main.path:gmatch("[^%./]+") do
				if seg ~= "game" then cur = cur and cur:FindFirstChild(seg) end
			end
			if cur and type(cur) ~= "table" then
				return live.convert(cur)
			end
		end
		return warn("[Converted] SSEmu is attached but the source could not be resolved")
	end
end

-- Native references captured before any takeover.
local realGame = game
local realInstance = Instance
local realTypeof = typeof
local realRequire = require
local realLoadstring = loadstring
local genv = (getgenv and getgenv()) or _G
local renv = (getrenv and getrenv()) or _G

-- Services.
local playersService = realGame:GetService("Players")
local runService = realGame:GetService("RunService")
local httpService = realGame:GetService("HttpService")
local insertService = realGame:GetService("InsertService")
local workspaceService = realGame:GetService("Workspace")
local localPlayer = playersService.LocalPlayer

local requestFn = request or http_request or (syn and syn.request) or (http and http.request)
local canHook = hookmetamethod and getnamecallmethod and checkcaller and newcclosure and getrawmetatable
local hooksReady = false

-- Attributes survive Clone, so a cloned script still knows which embedded entry it came from.
local KEY_ATTRIBUTE = "_cv_key"
local OFF_ATTRIBUTE = "_cv_off"
local TAG_ATTRIBUTE = "_cv"
local REMOTE_ATTRIBUTE = "_cv_remote"
local MODULE_TIMEOUT = 120

-- One running copy per converted source: running the file again shuts the previous copy down first.
local sharedTable = type(shared) == "table" and shared or genv
local registry = rawget(sharedTable, "__EzConverted")
if type(registry) ~= "table" then
	registry = {}
	rawset(sharedTable, "__EzConverted", registry)
end
local previousRun = registry[MAIN_TAG]
if type(previousRun) == "table" and type(previousRun.stop) == "function" then
	pcall(previousRun.stop)
end

local active = true
local connections = {}
local function track(connection)
	table.insert(connections, connection)
	return connection
end

-- Hidden holder, converted trees live here so nothing auto-runs.
local holder = realInstance.new("Folder")
holder.Name = "Converted"
pcall(function() holder.Parent = (gethui and gethui()) or realGame:GetService("CoreGui") end)
local serverScriptService = realInstance.new("Folder")
serverScriptService.Name = "ServerScriptService"
serverScriptService.Parent = holder
local serverStorage = realInstance.new("Folder")
serverStorage.Name = "ServerStorage"
serverStorage.Parent = holder

local function stop()
	if not active then return end
	active = false
	for _, connection in ipairs(connections) do
		pcall(function() connection:Disconnect() end)
	end
	table.clear(connections)
	pcall(function() holder:Destroy() end)
end

local REMOTE_CLASSES = { RemoteEvent = true, RemoteFunction = true, UnreliableRemoteEvent = true }
local TAGGED_CLASSES = { ScreenGui = true, BillboardGui = true, SurfaceGui = true, Tool = true }
local proxyTargets = setmetatable({}, { __mode = "k" })

local function unwrap(v) return proxyTargets[v] or v end

local function getAttr(inst, name)
	local ok, value = pcall(function() return inst:GetAttribute(name) end)
	if ok then return value end
	return nil
end

local function setAttr(inst, name, value)
	pcall(function() inst:SetAttribute(name, value) end)
end

-- Signal with Connect/Once/Wait/Fire. A buffered signal queues fires that happen before the first
-- listener connects, so a handshake sent too early is delivered instead of lost.
local function newSignal(buffered)
	local handlers, signal = {}, { count = 0 }
	local pending = buffered and {} or nil
	function signal:Connect(cb)
		local c = { Connected = true }
		handlers[c] = cb
		signal.count = signal.count + 1
		function c:Disconnect()
			if not self.Connected then return end
			self.Connected = false
			handlers[self] = nil
			signal.count = signal.count - 1
		end
		c.disconnect = c.Disconnect
		if pending and #pending > 0 then
			local queued = pending
			pending = {}
			for _, packed in ipairs(queued) do
				task.spawn(cb, table.unpack(packed, 1, packed.n))
			end
		end
		return c
	end
	function signal:Once(cb)
		local c
		c = signal:Connect(function(...) c:Disconnect() cb(...) end)
		return c
	end
	function signal:Wait()
		local t = coroutine.running()
		signal:Once(function(...) task.spawn(t, ...) end)
		return coroutine.yield()
	end
	function signal:Fire(...)
		local snap = {}
		for _, cb in pairs(handlers) do table.insert(snap, cb) end
		if #snap == 0 and pending then
			if #pending < 64 then table.insert(pending, table.pack(...)) end
			return
		end
		for _, cb in ipairs(snap) do task.spawn(cb, ...) end
	end
	signal.connect, signal.once, signal.wait = signal.Connect, signal.Once, signal.Wait
	return signal
end

-- Remote emulation.
local remotes = setmetatable({}, { __mode = "k" })
local REMOTE_KEYS = {
	ClassName = true, OnServerEvent = true, OnClientEvent = true, OnServerInvoke = true, OnClientInvoke = true,
	FireServer = true, FireClient = true, FireAllClients = true, InvokeServer = true, InvokeClient = true,
}
local oldIndex, oldNamecall, oldNewIndex, getAttributeFn
local restoreMethod = setnamecallmethod or function() end

local function remoteData(class, real, inst)
	return { class = class, real = real, inst = inst, serverSignal = newSignal(true), clientSignal = newSignal(true) }
end

local function mockRemote(class)
	local backing = realInstance.new(class == "RemoteFunction" and "BindableFunction" or "BindableEvent")
	backing.Name = class
	remotes[backing] = remoteData(class, false, backing)
	setAttr(backing, REMOTE_ATTRIBUTE, class)
	return backing
end

local function adoptRemote(inst)
	if realTypeof(inst) ~= "Instance" then return nil end
	local ok, class = pcall(oldIndex, inst, "ClassName")
	if not ok or not REMOTE_CLASSES[class] then return nil end
	local data = remoteData(class, true, inst)
	remotes[inst] = data
	return data
end

local function lookupRemote(inst, adopt)
	local data = remotes[inst]
	if data then return data end
	-- A cloned mock remote keeps the attribute, its state is rebuilt here.
	if getAttributeFn then
		local ok, class = pcall(getAttributeFn, inst, REMOTE_ATTRIBUTE)
		if ok and type(class) == "string" then
			data = remoteData(class, false, inst)
			remotes[inst] = data
			return data
		end
	end
	if adopt then return adoptRemote(inst) end
	return nil
end

local function dispatchRemote(method, data, ...)
	local sandbox = not data.real or checkcaller()
	if method == "FireServer" then
		if data.real and data.serverSignal.count == 0 then return false end
		data.serverSignal:Fire(localPlayer, ...)
		return sandbox
	elseif method == "FireClient" then
		if not sandbox then return false end
		data.clientSignal:Fire(select(2, ...))
		return true
	elseif method == "FireAllClients" then
		if not sandbox then return false end
		data.clientSignal:Fire(...)
		return true
	elseif method == "InvokeServer" then
		if not sandbox then return false end
		if data.serverInvoke then return true, data.serverInvoke(localPlayer, ...) end
		if data.real then return false end
		return true
	elseif method == "InvokeClient" then
		if not data.clientInvoke then return not data.real end
		if not sandbox then return false end
		return true, data.clientInvoke(select(2, ...))
	end
	return false
end

local function makeClientSignal(inst, data)
	if not data.real then return data.clientSignal end
	local merged = {}
	function merged:Connect(cb)
		local emu = data.clientSignal:Connect(cb)
		local ok, eng = pcall(function() return oldIndex(inst, "OnClientEvent"):Connect(cb) end)
		return { Connected = true, Disconnect = function(self)
			self.Connected = false
			emu:Disconnect()
			if ok and eng then eng:Disconnect() end
		end }
	end
	function merged:Once(cb)
		local c
		c = merged:Connect(function(...) c:Disconnect() cb(...) end)
		return c
	end
	function merged:Wait() return data.clientSignal:Wait() end
	merged.connect, merged.once, merged.wait = merged.Connect, merged.Once, merged.Wait
	return merged
end

local function indexRemote(self, data, key)
	local sandbox = not data.real or checkcaller()
	if key == "ClassName" then return not data.real, data.class end
	if not sandbox then return false end
	if key == "OnServerEvent" then return true, data.serverSignal
	elseif key == "OnClientEvent" then return true, makeClientSignal(self, data)
	elseif key == "OnServerInvoke" then return true, data.serverInvoke
	elseif key == "OnClientInvoke" then return true, data.clientInvoke end
	return true, function(target, ...)
		local r = table.pack(dispatchRemote(key, data, ...))
		if r[1] then return table.unpack(r, 2, r.n) end
		return oldIndex(target, key)(target, ...)
	end
end

-- Server-only methods a client cannot call, answered for sandbox threads instead of erroring.
local function isPart(inst) return (pcall(oldIndex, inst, "Anchored")) end
local function isPlayer(inst) return (pcall(oldIndex, inst, "UserId")) end
local EMULATED_METHODS = {
	SetNetworkOwner = { check = isPart, run = function() end },
	SetNetworkOwnershipAuto = { check = isPart, run = function() end },
	GetNetworkOwner = { check = isPart, run = function() return localPlayer end },
	Kick = {
		check = function(inst) return inst ~= localPlayer and isPlayer(inst) end,
		run = function() end,
	},
	LoadCharacter = {
		check = function(inst) return inst == localPlayer end,
		run = function()
			local character = localPlayer.Character
			local humanoid = character and character:FindFirstChildOfClass("Humanoid")
			if humanoid then humanoid.Health = 0 end
		end,
	},
}

local function installHook(name, handler)
	local ok, old = pcall(hookmetamethod, realGame, name, newcclosure(handler))
	if ok and old then return old end
	local mt = getrawmetatable(realGame)
	local old2 = rawget(mt, name)
	if setreadonly then pcall(setreadonly, mt, false) elseif make_writeable then pcall(make_writeable, mt) end
	rawset(mt, name, newcclosure(handler))
	return old2
end

local function indexHandler(self, key)
	if active and REMOTE_KEYS[key] then
		local data
		if key == "ClassName" then
			data = remotes[self]
		else
			data = lookupRemote(self, checkcaller())
		end
		if data then
			local handled, value = indexRemote(self, data, key)
			if handled then return value end
		end
	end
	return oldIndex(self, key)
end

local function namecallInner(self, method, sandbox, ...)
	local emulated = sandbox and EMULATED_METHODS[method]
	if emulated and emulated.check(self) then
		return emulated.run(self, ...)
	end

	local data = remotes[self]
	if not data and REMOTE_KEYS[method] then
		data = lookupRemote(self, sandbox)
	end
	if not data then
		restoreMethod(method)
		return oldNamecall(self, ...)
	end

	if REMOTE_KEYS[method] then
		local r = table.pack(dispatchRemote(method, data, ...))
		if r[1] then return table.unpack(r, 2, r.n) end
	elseif method == "IsA" and not data.real then
		local class = ...
		if class == data.class or class == "BaseRemoteEvent" or class == "Instance" then return true end
	elseif method == "Clone" and not data.real then
		restoreMethod(method)
		local copy = oldNamecall(self, ...)
		if copy then remotes[copy] = remoteData(data.class, false, copy) end
		return copy
	end
	restoreMethod(method)
	return oldNamecall(self, ...)
end

local function namecallHandler(self, ...)
	if not active then return oldNamecall(self, ...) end
	local method = getnamecallmethod()
	local sandbox = checkcaller()

	-- Service proxies passed as arguments are swapped for the real objects before the engine sees them.
	if sandbox then
		for index = 1, select("#", ...) do
			local value = (select(index, ...))
			if type(value) == "table" and proxyTargets[value] then
				local args = table.pack(...)
				for at = index, args.n do
					local target = type(args[at]) == "table" and proxyTargets[args[at]]
					if target then args[at] = target end
				end
				return namecallInner(self, method, sandbox, table.unpack(args, 1, args.n))
			end
		end
	end
	return namecallInner(self, method, sandbox, ...)
end

local function newIndexHandler(self, key, value)
	if not active then return oldNewIndex(self, key, value) end
	if type(value) == "table" and proxyTargets[value] and checkcaller() then
		value = proxyTargets[value]
	end
	if key == "OnServerInvoke" or key == "OnClientInvoke" then
		local sandbox = checkcaller()
		local data = lookupRemote(self, sandbox)
		if data and (not data.real or sandbox) then
			if key == "OnServerInvoke" then
				data.serverInvoke = value
			else
				data.clientInvoke = value
				if data.real then pcall(oldNewIndex, self, key, value) end
			end
			return
		end
	end
	return oldNewIndex(self, key, value)
end

if canHook then
	local ok, err = pcall(function()
		oldIndex = installHook("__index", indexHandler)
		oldNamecall = installHook("__namecall", namecallHandler)
		oldNewIndex = installHook("__newindex", newIndexHandler)
		getAttributeFn = oldIndex(realGame, "GetAttribute")
	end)
	hooksReady = ok and oldIndex ~= nil and oldNamecall ~= nil and oldNewIndex ~= nil
	if not ok then warn("[Converted] hook install failed: " .. tostring(err)) end
end
if not hooksReady then
	warn("[Converted] no metamethod hooks in this executor, remotes are not emulated")
end

-- Fake players: stand-ins server scripts see as real players.
local fakeObjects = setmetatable({}, { __mode = "k" })
local fakeList = {}
local fakeAddedSignal = newSignal()
local fakeRemovingSignal = newSignal()
local fakeCounter = 0
local fakeMethods, fakeMeta = {}, {}

local function removeFake(fake)
	local i = table.find(fakeList, fake)
	if not i then return end
	table.remove(fakeList, i)
	fakeRemovingSignal:Fire(fake)
	pcall(function() rawget(fake, "backing"):Destroy() end)
end

fakeMeta.__index = function(self, key)
	local m = fakeMethods[key]
	if m ~= nil then return m end
	if type(key) == "string" then
		local child = rawget(self, "backing"):FindFirstChild(key)
		if child then return child end
	end
	error(tostring(key) .. " is not a valid member of Player \"" .. rawget(self, "Name") .. "\"", 2)
end
fakeMeta.__tostring = function(self) return rawget(self, "Name") end

fakeMethods.IsA = function(_, class) return class == "Player" or class == "Instance" or class == "Object" end
fakeMethods.GetAttribute = function(self, n) return rawget(self, "attributes")[n] end
fakeMethods.SetAttribute = function(self, n, v) rawget(self, "attributes")[n] = v end
fakeMethods.FindFirstChild = function(self, n) return rawget(self, "backing"):FindFirstChild(n) end
fakeMethods.WaitForChild = fakeMethods.FindFirstChild
fakeMethods.GetChildren = function(self) return rawget(self, "backing"):GetChildren() end
fakeMethods.Chat = function(self, msg) rawget(self, "Chatted"):Fire(tostring(msg)) end
fakeMethods.Kick = function(self) removeFake(self) end
fakeMethods.Destroy = function(self) removeFake(self) end
fakeMethods.IsFriendsWith = function() return false end
fakeMethods.IsInGroup = function() return false end
fakeMethods.GetRankInGroup = function() return 0 end

local function createFakePlayer(name, userId)
	name = tostring(name)
	for _, e in ipairs(fakeList) do if rawget(e, "Name") == name then return e end end
	fakeCounter = fakeCounter + 1
	local backing = realInstance.new("Folder")
	backing.Name = "Player_" .. name
	backing.Parent = serverStorage
	for _, f in ipairs({ "Backpack", "PlayerGui", "StarterGear" }) do
		local sub = realInstance.new("Folder")
		sub.Name = f
		sub.Parent = backing
	end
	local fake = setmetatable({
		Name = name, DisplayName = name, UserId = userId or -(100 + fakeCounter),
		ClassName = "Player", AccountAge = 365, Neutral = true,
		Chatted = newSignal(), CharacterAdded = newSignal(), CharacterRemoving = newSignal(),
		attributes = {}, backing = backing,
	}, fakeMeta)
	fakeObjects[fake] = true
	proxyTargets[fake] = backing
	table.insert(fakeList, fake)
	fakeAddedSignal:Fire(fake)
	return fake
end

local function allPlayers()
	local list = playersService:GetPlayers()
	for _, f in ipairs(fakeList) do table.insert(list, f) end
	return list
end

local function mergedPlayerSignal(realSignal, fakeSignal, fireExisting)
	local function connect(cb, existing)
		if existing then for _, p in ipairs(allPlayers()) do task.spawn(cb, p) end end
		local rc = realSignal:Connect(cb)
		local fc = fakeSignal:Connect(cb)
		return { Connected = true, Disconnect = function(self) self.Connected = false rc:Disconnect() fc:Disconnect() end }
	end
	local merged = {}
	function merged:Connect(cb) return connect(cb, fireExisting) end
	function merged:Once(cb)
		local c
		c = connect(function(...) c:Disconnect() cb(...) end, false)
		return c
	end
	function merged:Wait()
		local t = coroutine.running()
		merged:Once(function(...) task.spawn(t, ...) end)
		return coroutine.yield()
	end
	merged.connect, merged.once, merged.wait = merged.Connect, merged.Once, merged.Wait
	return merged
end

-- Service mocks.
local function proxy(target, overrides)
	local p = setmetatable({}, {
		__index = function(_, k)
			local o = overrides[k]
			if o ~= nil then return o end
			local ok, v = pcall(function() return target[k] end)
			if not ok then return nil end
			if type(v) == "function" then return function(_, ...) return v(target, ...) end end
			return v
		end,
		__newindex = function(_, k, v) pcall(function() target[k] = v end) end,
		__tostring = function() return target.Name end,
	})
	proxyTargets[p] = target
	return p
end

local function newDataStore(data)
	local s = {}
	function s:GetAsync(k) return data[k] end
	function s:SetAsync(k, v) data[k] = v return "ok" end
	function s:UpdateAsync(k, f) local u = f(data[k]) if u ~= nil then data[k] = u end return data[k] end
	function s:IncrementAsync(k, d) data[k] = (data[k] or 0) + (d or 1) return data[k] end
	function s:RemoveAsync(k) local o = data[k] data[k] = nil return o end
	function s:GetSortedAsync() return { GetCurrentPage = function() return {} end, IsFinished = true, AdvanceToNextPageAsync = function() end } end
	function s:OnUpdate() return { Disconnect = function() end } end
	return s
end
local stores = {}
local dataStoreMock = {
	GetDataStore = function(_, n) stores[n] = stores[n] or {} return newDataStore(stores[n]) end,
	GetGlobalDataStore = function() stores.g = stores.g or {} return newDataStore(stores.g) end,
	GetRequestBudgetForRequestType = function() return math.huge end,
}
dataStoreMock.GetOrderedDataStore = dataStoreMock.GetDataStore

local messagingTopics = {}
local messagingMock = {
	SubscribeAsync = function(_, topic, cb)
		messagingTopics[topic] = messagingTopics[topic] or {}
		table.insert(messagingTopics[topic], cb)
		return { Disconnect = function()
			local i = table.find(messagingTopics[topic], cb)
			if i then table.remove(messagingTopics[topic], i) end
		end }
	end,
	PublishAsync = function(_, topic, msg)
		for _, cb in ipairs(messagingTopics[topic] or {}) do task.spawn(cb, { Data = msg, Sent = os.time() }) end
	end,
}

local function execRequest(opt)
	if not requestFn then error("No request function in this executor.", 3) end
	return requestFn(opt)
end
local httpMock = proxy(httpService, {
	HttpEnabled = true,
	GetAsync = function(_, url, _, headers) return execRequest({ Url = url, Method = "GET", Headers = headers }).Body end,
	PostAsync = function(_, url, body, ct, _, headers)
		local h = headers or {}
		h["Content-Type"] = h["Content-Type"] or "application/json"
		return execRequest({ Url = url, Method = "POST", Headers = h, Body = body }).Body
	end,
	RequestAsync = function(_, opt)
		local r = execRequest(opt)
		local st = r.StatusCode or r.Status or 0
		return { Success = st >= 200 and st < 300, StatusCode = st, StatusMessage = r.StatusMessage or "", Headers = r.Headers or {}, Body = r.Body }
	end,
})

local runMock = proxy(runService, {
	IsServer = function() return true end,
	IsClient = function() return false end,
	IsStudio = function() return false end,
	IsRunMode = function() return true end,
})

local playersMock = proxy(playersService, {
	PlayerAdded = mergedPlayerSignal(playersService.PlayerAdded, fakeAddedSignal, true),
	PlayerRemoving = mergedPlayerSignal(playersService.PlayerRemoving, fakeRemovingSignal, false),
	GetPlayers = function() return allPlayers() end,
	GetChildren = function() return allPlayers() end,
	GetPlayerByUserId = function(_, id)
		for _, p in ipairs(allPlayers()) do if p.UserId == id then return p end end
		return nil
	end,
	GetPlayerFromCharacter = function(_, char) return playersService:GetPlayerFromCharacter(char) end,
	FindFirstChild = function(_, n)
		for _, f in ipairs(fakeList) do if rawget(f, "Name") == n then return f end end
		return playersService:FindFirstChild(n)
	end,
	BanAsync = function() end,
	UnbanAsync = function() end,
	CharacterAutoLoads = true,
})

local teleportMock = proxy(realGame:GetService("TeleportService"), {
	Teleport = function() end,
	TeleportAsync = function(_, placeId) return { PlaceId = placeId } end,
	TeleportToPlaceInstance = function() end,
	TeleportToPrivateServer = function() end,
	ReserveServer = function() return "sse", "sse" end,
})

-- Embedded tree bookkeeping. A script is found by the key the bundler gave it.
local byKey = {}
for _, e in ipairs(ENTRIES) do byKey[e.key] = e end
local positionCache = setmetatable({}, { __mode = "k" })
local rootIndex = setmetatable({}, { __mode = "k" })
local treeOfRoot = setmetatable({}, { __mode = "k" })
local loadedTrees, loadingTrees = {}, {}
local treeById = {}
for _, t in ipairs(TREES) do if t.id then treeById[t.id] = t end end

local function fetchRoots(tree)
	if tree.path then
		local cur = realGame
		for seg in tree.path:gmatch("[^%./]+") do
			if seg ~= "game" then cur = cur and cur:FindFirstChild(seg) end
		end
		if not cur or cur == realGame then return nil end
		-- Non-archivable instances clone as nil, so the flag is lifted for the copy only.
		local okFlag, was = pcall(function() return cur.Archivable end)
		pcall(function() cur.Archivable = true end)
		local okClone, copy = pcall(function() return cur:Clone() end)
		if okFlag then pcall(function() cur.Archivable = was end) end
		return okClone and copy and { copy } or nil
	end
	local ok, objs = pcall(function() return realGame:GetObjects("rbxassetid://" .. tostring(tree.id)) end)
	if ok and type(objs) == "table" and #objs > 0 then return objs end
	local loaded, model = pcall(function() return insertService:LoadAsset(tree.id) end)
	if loaded and model then
		local kids = model:GetChildren()
		for _, c in ipairs(kids) do c.Parent = nil end
		model:Destroy()
		return #kids > 0 and kids or nil
	end
	return nil
end

local function positionOf(node)
	local parent = node.Parent
	if not parent then return 1 end
	local map = positionCache[parent]
	if not map then
		map = {}
		local counts = {}
		for _, s in ipairs(parent:GetChildren()) do
			counts[s.Name] = (counts[s.Name] or 0) + 1
			map[s] = counts[s.Name]
		end
		positionCache[parent] = map
	end
	return map[node] or 1
end

local function keyOf(inst)
	local parts, node = {}, inst
	while node and not rootIndex[node] do
		local pos = positionOf(node)
		table.insert(parts, 1, pos > 1 and (node.Name .. "~" .. pos) or node.Name)
		node = node.Parent
	end
	local tree = node and treeOfRoot[node]
	return (tree and tree.tag or "?") .. "/r" .. tostring(node and rootIndex[node] or 0) .. "/" .. table.concat(parts, "/")
end

-- Replace a real remote with a mock one, children and attributes kept.
local function swapRemote(node)
	local replacement = mockRemote(node.ClassName)
	replacement.Name = node.Name
	pcall(function()
		for name, value in pairs(node:GetAttributes()) do
			replacement:SetAttribute(name, value)
		end
	end)
	for _, child in ipairs(node:GetChildren()) do
		child.Parent = replacement
	end
	replacement.Parent = node.Parent
	node:Destroy()
	return replacement
end

-- Stamp keys, remember which scripts were disabled, switch every script off and swap the remotes.
-- Keys are stamped while the tree is untouched, so they match the keys the bundler computed.
local function prepareRoots(roots, tree)
	for index, root in ipairs(roots) do
		rootIndex[root] = index
		treeOfRoot[root] = tree
	end

	for _, root in ipairs(roots) do
		local nodes = root:GetDescendants()
		table.insert(nodes, 1, root)
		for _, node in ipairs(nodes) do
			if node:IsA("LuaSourceContainer") then
				setAttr(node, KEY_ATTRIBUTE, keyOf(node))
				if node:IsA("BaseScript") then
					local was = getAttr(node, "_sse_wasdisabled")
					if was == nil then
						local ok, value = pcall(function() return node.Disabled end)
						was = ok and value == true
					end
					if was then setAttr(node, OFF_ATTRIBUTE, true) end
					pcall(function() node.Disabled = true end)
				end
			elseif TAGGED_CLASSES[node.ClassName] then
				setAttr(node, TAG_ATTRIBUTE, true)
			end
		end
	end

	if hooksReady then
		for index, root in ipairs(roots) do
			for _, node in ipairs(root:GetDescendants()) do
				if REMOTE_CLASSES[node.ClassName] then
					pcall(swapRemote, node)
				end
			end
			if REMOTE_CLASSES[root.ClassName] then
				local ok, replacement = pcall(swapRemote, root)
				if ok and replacement then
					rootIndex[replacement] = index
					treeOfRoot[replacement] = tree
					roots[index] = replacement
				end
			end
		end
	end
end

local function loadTree(tree)
	while loadingTrees[tree.tag] do task.wait() end
	if loadedTrees[tree.tag] then return loadedTrees[tree.tag] end
	loadingTrees[tree.tag] = true

	local ok, roots = pcall(fetchRoots, tree)
	if not ok or type(roots) ~= "table" or #roots == 0 then
		loadingTrees[tree.tag] = nil
		return nil
	end

	local folder = realInstance.new("Folder")
	folder.Name = tree.tag
	folder.Parent = holder
	local prepared, err = pcall(prepareRoots, roots, tree)
	if not prepared then warn("[Converted] prepare failed: " .. tostring(err)) end
	for _, root in ipairs(roots) do
		pcall(function() root.Parent = folder end)
	end

	local info = { roots = roots, folder = folder }
	loadedTrees[tree.tag] = info
	loadingTrees[tree.tag] = nil
	return info
end

-- The module require(id) returns: a root module, a module named MainModule, or (loose) the first module.
local function findMain(info, loose)
	for _, root in ipairs(info.roots) do
		if root:IsA("ModuleScript") then return root end
	end
	local named = info.folder:FindFirstChild("MainModule", true)
	if named and named:IsA("ModuleScript") then return named end
	if loose then
		for _, root in ipairs(info.roots) do
			if not root:IsA("Tool") then
				for _, node in ipairs(root:GetDescendants()) do
					if node:IsA("ModuleScript") then return node end
				end
			end
		end
	end
	return nil
end

local insertCounter = 0
local function loadLoose(assetId)
	local model = realInstance.new("Model")
	local id = tonumber(assetId)
	if not id then return model end
	insertCounter = insertCounter + 1
	-- An embedded id reuses its tag so the embedded sources still match.
	local known = treeById[id]
	local tree = { tag = known and known.tag or ("a" .. tostring(id)), id = id }
	local ok, roots = pcall(fetchRoots, tree)
	if ok and type(roots) == "table" then
		pcall(prepareRoots, roots, tree)
		for _, root in ipairs(roots) do
			pcall(function() root.Parent = model end)
		end
	end
	return model
end

local insertMock = proxy(insertService, {
	LoadAsset = function(_, assetId) return loadLoose(assetId) end,
	LoadAssetVersion = function(_, versionId) return loadLoose(versionId) end,
	GetLatestAssetVersionAsync = function(_, assetId) return assetId end,
})

local closeCallbacks = {}
local serviceMocks = {
	ServerScriptService = serverScriptService,
	ServerStorage = serverStorage,
	Players = playersMock,
	RunService = runMock,
	HttpService = httpMock,
	DataStoreService = dataStoreMock,
	MessagingService = messagingMock,
	InsertService = insertMock,
	TeleportService = teleportMock,
}

local gameOverrides = {
	GetService = function(_, n) return serviceMocks[n] or realGame:GetService(n) end,
	FindService = function(_, n) return serviceMocks[n] or realGame:FindService(n) end,
	BindToClose = function(_, cb) table.insert(closeCallbacks, cb) end,
}
gameOverrides.getService = gameOverrides.GetService
for n, m in pairs(serviceMocks) do gameOverrides[n] = m end
local mockGame = proxy(realGame, gameOverrides)

local function instanceApi()
	local api = setmetatable({}, { __index = realInstance })
	api.new = function(class, parent)
		local c = (hooksReady and REMOTE_CLASSES[class]) and mockRemote(class) or realInstance.new(class)
		if TAGGED_CLASSES[class] then setAttr(c, TAG_ATTRIBUTE, true) end
		if parent ~= nil then c.Parent = unwrap(parent) end
		return c
	end
	return api
end

local function sandboxTypeof(v)
	if type(v) == "table" and proxyTargets[v] then return "Instance" end
	return realTypeof(v)
end

-- Strong on purpose: Instance wrappers are collected while the Instance lives, a weak table would
-- forget a loaded module or a started script and run it a second time.
local cache = {}
local started = {}
local armed = {}
local runModule, envFor, startScript

-- Compile a node preferring its REAL bytecode (getscriptclosure) so obfuscated scripts run as
-- compiled; fall back to the embedded source only when the closure is unavailable.
local function compileNode(inst, source)
	if getscriptclosure then
		local ok, closure = pcall(getscriptclosure, inst)
		if ok and type(closure) == "function" then
			return closure
		end
	end
	if type(source) == "string" and source ~= "" and realLoadstring then
		local func, err = realLoadstring(source, "=" .. inst:GetFullName())
		if not func then warn("[Converted] compile failed: " .. inst.Name .. " - " .. tostring(err)) end
		return func
	end
	return nil
end

-- Engine require at a low identity, an elevated thread is refused for game modules.
local function nativeRequire(target)
	local previous = getthreadidentity and getthreadidentity()
	if setthreadidentity then pcall(setthreadidentity, 2) end
	local ok, value = pcall(realRequire, target)
	if setthreadidentity and previous then pcall(setthreadidentity, previous) end
	return ok, value
end

local function runProtected(func, node)
	local ok, err = xpcall(func, function(message)
		return debug.traceback(tostring(message), 2)
	end)
	if not ok then
		local named, fullName = pcall(function() return node:GetFullName() end)
		warn("[Converted] " .. (named and fullName or "script") .. ": " .. tostring(err))
	end
end

local function requireModule(inst)
	local key = getAttr(inst, KEY_ATTRIBUTE)
	if type(key) ~= "string" then
		-- Not part of a converted tree: the engine keeps its own cache for game modules.
		local ok, value = nativeRequire(inst)
		if ok then return value end
		return runModule(inst, nil)
	end
	local entry = byKey[key]
	return runModule(inst, entry and entry.source or nil)
end

-- Resolve a string require relative to the caller: @self/X, ./X, ../X, A/B/C.
local function resolveRelative(path, caller)
	if not caller then return nil end
	local base, rest
	if path == "@self" then
		return caller:IsA("ModuleScript") and caller or nil
	elseif path:sub(1, 6) == "@self/" then
		base, rest = caller, path:sub(7)
	elseif path:sub(1, 2) == "./" then
		base, rest = caller.Parent, path:sub(3)
	elseif path:sub(1, 3) == "../" then
		base, rest = caller.Parent and caller.Parent.Parent, path:sub(4)
		while rest:sub(1, 3) == "../" do
			base = base and base.Parent
			rest = rest:sub(4)
		end
	else
		base, rest = caller.Parent, path
	end
	if not base then return nil end
	local current = base
	for segment in rest:gmatch("[^/]+") do
		if segment == ".." then
			current = current and current.Parent
		elseif segment ~= "." then
			current = current and current:FindFirstChild(segment)
		end
		if not current then return nil end
	end
	return current and current:IsA("ModuleScript") and current or nil
end

local function convertedRequire(target, caller)
	target = unwrap(target)
	if realTypeof(target) == "Instance" and target:IsA("ModuleScript") then
		return requireModule(target)
	end
	local id = tonumber(target)
	if id then
		-- Ids the bundler never saw (fast mode, or ids built at run time) are fetched on demand.
		local tree = treeById[id]
		if not tree then
			tree = { tag = "a" .. tostring(id), id = id }
			treeById[id] = tree
		end
		local info = loadTree(tree)
		local main = info and findMain(info, true)
		if main then return requireModule(main) end
		error("Converted: asset " .. tostring(id) .. " could not be loaded or has no MainModule", 2)
	end
	if type(target) == "string" then
		local module = resolveRelative(target, caller)
		if module then return requireModule(module) end
	end
	local ok, value = nativeRequire(target)
	if not ok then error(value, 2) end
	return value
end

-- Run source in a fresh Script or LocalScript object, the NS/NLS helpers script hubs expect.
local function spawnSource(source, parent, isClient)
	local container = realInstance.new(isClient and "LocalScript" or "Script")
	container.Name = isClient and "NLS" or "NS"
	pcall(function() container.Disabled = true end)
	started[container] = true
	container.Parent = unwrap(parent) or serverScriptService
	local func, err = realLoadstring(tostring(source), "=" .. container.Name)
	if not func then
		warn("[Converted] " .. container.Name .. ": " .. tostring(err))
		return container
	end
	setfenv(func, envFor(container, isClient))
	task.spawn(runProtected, func, container)
	return container
end

envFor = function(inst, isClient)
	local env = {
		script = inst,
		owner = localPlayer,
		game = isClient and realGame or mockGame,
		Game = isClient and realGame or mockGame,
		Instance = instanceApi(),
		typeof = sandboxTypeof,
		require = function(target) return convertedRequire(target, inst) end,
		loadstring = function(src, chunk)
			local f, err = realLoadstring(src, chunk)
			if f then setfenv(f, envFor(inst, isClient)) end
			return f, err
		end,
		NS = function(source, parent) return spawnSource(source, parent, false) end,
		NLS = function(source, parent) return spawnSource(source, parent, true) end,
	}
	return setmetatable(env, { __index = function(_, k)
		local v = genv[k]
		if v ~= nil then return v end
		return renv[k]
	end })
end

runModule = function(inst, source)
	local state = cache[inst]
	if state then
		if state.thread == coroutine.running() and not state.done then
			error("Requested module was cyclic: " .. inst.Name, 2)
		end
		local deadline = os.clock() + MODULE_TIMEOUT
		while not state.done do
			if os.clock() >= deadline then
				error("Converted: require timed out: " .. inst.Name, 2)
			end
			task.wait()
		end
		if state.failed then error(state.value, 0) end
		return state.value
	end
	state = { thread = coroutine.running() }
	cache[inst] = state
	local func = compileNode(inst, source)
	if not func then
		-- No bytecode and no source: the engine loader is the last resort.
		local ok, value = nativeRequire(inst)
		state.done = true
		if ok then
			state.value = value
			return value
		end
		state.failed, state.value = true, "no runnable code: " .. inst.Name
		error(state.value, 0)
	end
	setfenv(func, envFor(inst, false))
	local ok, value = pcall(func)
	state.done = true
	if not ok then
		state.failed, state.value = true, inst.Name .. ": " .. tostring(value)
		error(state.value, 0)
	end
	state.value = value
	return value
end

-- A script only runs where the engine would run it: LocalScripts under the player or the character,
-- server Scripts there too and anywhere in Workspace or the emulated ServerScriptService.
local function isLive(node)
	local character = localPlayer.Character
	if node:IsDescendantOf(localPlayer) or (character and node:IsDescendantOf(character)) then
		return true
	end
	if node:IsA("LocalScript") then return false end
	return node:IsDescendantOf(workspaceService) or node:IsDescendantOf(serverScriptService)
end

local function isClientScript(node)
	if node:IsA("LocalScript") then return true end
	local ok, context = pcall(function() return node.RunContext end)
	return ok and context == Enum.RunContext.Client
end

-- Start one converted script once. Clones are recognised by the key attribute they carry.
startScript = function(node, force)
	if not active or started[node] then return end
	local key = getAttr(node, KEY_ATTRIBUTE)
	if type(key) ~= "string" then return end
	if not force and not isLive(node) then return end

	-- A script that shipped disabled waits until the hub enables it.
	if getAttr(node, OFF_ATTRIBUTE) then
		if not armed[node] then
			armed[node] = true
			for _, property in ipairs({ "Disabled", "Enabled" }) do
				pcall(function()
					track(node:GetPropertyChangedSignal(property):Connect(function()
						if not node.Disabled then startScript(node, force) end
					end))
				end)
			end
		end
		local ok, disabled = pcall(function() return node.Disabled end)
		if not ok or disabled then return end
	end

	started[node] = true
	-- Our copy runs instead of the engine's, so the instance itself stays switched off.
	pcall(function() node.Disabled = true end)

	local entry = byKey[key]
	local func = compileNode(node, entry and entry.source or nil)
	if not func then
		return warn("[Converted] no runnable code: " .. node:GetFullName())
	end
	setfenv(func, envFor(node, isClientScript(node)))
	task.spawn(runProtected, func, node)
end

-- Watch the places a server would deliver content to, so cloned GUIs, tools and scripts come alive.
local function watch(container)
	if not container then return end
	track(container.DescendantAdded:Connect(function(node)
		if node:IsA("BaseScript") then
			task.defer(startScript, node)
		end
	end))
end

local function watchPlayerChild(child)
	if child:IsA("PlayerGui") or child:IsA("Backpack") or child:IsA("PlayerScripts") then
		watch(child)
	end
end

watch(workspaceService)
watch(serverScriptService)
for _, child in ipairs(localPlayer:GetChildren()) do
	watchPlayerChild(child)
end
track(localPlayer.ChildAdded:Connect(watchPlayerChild))

-- StarterGui and StarterPack content reaches the player the way a server would deliver it.
pcall(function()
	track(realGame:GetService("StarterGui").ChildAdded:Connect(function(child)
		if not getAttr(child, TAG_ATTRIBUTE) then return end
		task.defer(function()
			local playerGui = localPlayer:FindFirstChildOfClass("PlayerGui")
			if not (active and playerGui) then return end
			pcall(function()
				if child:IsA("ScreenGui") then child.ResetOnSpawn = false end
				child.Parent = playerGui
			end)
		end)
	end))
	track(realGame:GetService("StarterPack").ChildAdded:Connect(function(child)
		if not (child:IsA("Tool") and getAttr(child, TAG_ATTRIBUTE)) then return end
		task.defer(function()
			local backpack = localPlayer:FindFirstChildOfClass("Backpack")
			if not (active and backpack) then return end
			pcall(function() child:Clone().Parent = backpack end)
		end)
	end))
end)

-- Tool drop + ground pickup (same behaviour as the live SSEmu) so converted hubs support dropping.
do
	local userInput = realGame:GetService("UserInputService")
	local dropKey = (type(shared) == "table" and type(shared.SSEmuConfig) == "table" and shared.SSEmuConfig.dropKey) or Enum.KeyCode.Backspace

	local function groundPickup(tool, handle)
		task.delay(1, function()
			if not (tool and tool.Parent and handle and tool:IsDescendantOf(workspaceService)) then return end
			local picked = false
			local connection
			connection = handle.Touched:Connect(function(hit)
				if picked then return end
				local character = localPlayer.Character
				if character and hit:IsDescendantOf(character) and hit:FindFirstAncestorWhichIsA("Tool") == nil then
					picked = true
					if connection then connection:Disconnect() end
					local backpack = localPlayer:FindFirstChildOfClass("Backpack") or localPlayer:WaitForChild("Backpack", 3)
					if backpack then
						pcall(function() handle.Anchored = false end)
						tool.Parent = backpack
					end
				end
			end)
		end)
	end

	local function dropTool(tool, character)
		local handle = tool:FindFirstChild("Handle")
		if not (character and handle and handle:IsA("BasePart")) then return end
		for _, part in ipairs(tool:GetDescendants()) do
			if part:IsA("BasePart") and part ~= handle then
				local welded = false
				for _, j in ipairs(part:GetJoints()) do
					if (j:IsA("WeldConstraint") or j:IsA("Weld") or j:IsA("Motor6D")) and (j.Part0 == handle or j.Part1 == handle) then
						welded = true break
					end
				end
				if not welded then
					pcall(function()
						local w = realInstance.new("WeldConstraint")
						w.Part0, w.Part1 = handle, part
						w.Parent = handle
					end)
				end
				pcall(function() part.Anchored = false end)
			end
		end
		for _, node in ipairs(character:GetDescendants()) do
			if node:IsA("Weld") or node:IsA("Motor6D") or node:IsA("ManualWeld") then
				local other = (node.Part0 == handle and node.Part1) or (node.Part1 == handle and node.Part0) or nil
				if other and not other:IsDescendantOf(tool) then pcall(function() node:Destroy() end) end
			end
		end
		pcall(function() tool.CanBeDropped = true end)
		tool.Parent = workspaceService
		pcall(function() handle.Anchored = false end)
		pcall(function() handle.CanCollide = true end)
		local root = character:FindFirstChild("HumanoidRootPart") or character.PrimaryPart
		if root then pcall(function() tool:PivotTo(root.CFrame * CFrame.new(0, 0.5, -3)) end) end
		groundPickup(tool, handle)
	end

	track(userInput.InputBegan:Connect(function(input, processed)
		if not processed and input.KeyCode == dropKey then
			local character = localPlayer.Character
			local tool = character and character:FindFirstChildOfClass("Tool")
			if tool then dropTool(tool, character) end
		end
	end))
end

-- Entry.
local mainTree
for _, t in ipairs(TREES) do if t.tag == MAIN_TAG then mainTree = t end end
local info = mainTree and loadTree(mainTree)
if not info then
	stop()
	error("Converted: the source tree could not be loaded", 0)
end

local result
local mainModule = findMain(info, false)
if ENTRY then
	-- Loader-line convert: the line runs as a server script, require(id) resolves to the embedded tree.
	local entryScript = realInstance.new("Script")
	entryScript.Name = "Entry"
	pcall(function() entryScript.Disabled = true end)
	started[entryScript] = true
	entryScript.Parent = serverScriptService
	local func = realLoadstring("return " .. ENTRY, "=Entry") or realLoadstring(ENTRY, "=Entry")
	if func then
		setfenv(func, envFor(entryScript, false))
		local ok, value = xpcall(func, function(message)
			return debug.traceback(tostring(message), 2)
		end)
		if ok then
			result = value
		else
			warn("[Converted] entry failed: " .. tostring(value))
		end
	else
		warn("[Converted] the entry line does not compile: " .. ENTRY)
	end
elseif mainModule then
	-- require-style asset: only the MainModule runs, everything it clones out starts through the watchers.
	local ok, value = pcall(requireModule, mainModule)
	if ok then
		result = value
	else
		warn("[Converted] MainModule failed: " .. tostring(value))
	end
else
	-- model-style asset: tools and GUIs are delivered to the player, the rest runs in place.
	for _, root in ipairs(info.roots) do
		if root:IsA("Tool") then
			local backpack = localPlayer:FindFirstChildOfClass("Backpack") or localPlayer:WaitForChild("Backpack", 5)
			if backpack then root.Parent = backpack end
		elseif root:IsA("LayerCollector") then
			local playerGui = localPlayer:FindFirstChildOfClass("PlayerGui") or localPlayer:WaitForChild("PlayerGui", 5)
			if playerGui then
				pcall(function()
					if root:IsA("ScreenGui") then root.ResetOnSpawn = false end
				end)
				root.Parent = playerGui
			end
		end
	end
	for _, root in ipairs(info.roots) do
		local nodes = root:GetDescendants()
		table.insert(nodes, 1, root)
		for _, node in ipairs(nodes) do
			if node:IsA("BaseScript") then
				startScript(node, true)
			end
		end
	end
end

registry[MAIN_TAG] = {
	stop = stop,
	result = result,
	holder = holder,
	createFakePlayer = createFakePlayer,
	removeFakePlayer = removeFake,
}
genv.ConvertedResult = result
return result
]=====]

-- Server-only APIs that cannot behave the same on a client.
local SERVER_ONLY_PATTERNS = {
	{ "BanAsync", "Players:BanAsync" },
	{ "UnbanAsync", "Players:UnbanAsync" },
	{ "DataStoreService", "DataStoreService" },
	{ "MessagingService", "MessagingService" },
	{ "OnServerEvent", "RemoteEvent.OnServerEvent" },
	{ "OnServerInvoke", "RemoteFunction.OnServerInvoke" },
	{ "FireClient", "RemoteEvent:FireClient" },
	{ "FireAllClients", "RemoteEvent:FireAllClients" },
	{ "ServerScriptService", "ServerScriptService" },
	{ "ServerStorage", "ServerStorage" },
	{ "PostAsync", "HttpService:PostAsync" },
	{ "SetPrimaryPartCFrame", "client replication limits" },
	{ "SetNetworkOwner", "BasePart:SetNetworkOwner" },
	{ "LoadCharacter", "Player:LoadCharacter" },
	{ "TeleportAsync", "TeleportService:TeleportAsync" },
}

---Wrap text in a Lua long string whose brackets cannot appear inside it.
---@param text string
---@return string
local function longString(text)
	text = text .. "\n"
	local level = 0
	while text:find("%]" .. string.rep("=", level) .. "%]", 1) or text:find("%[" .. string.rep("=", level) .. "%[", 1) do
		level = level + 1
	end
	local equals = string.rep("=", level)
	return "[" .. equals .. "[\n" .. text .. "]" .. equals .. "]"
end

---Read a source without letting one stuck decompile hang the whole convert.
---@param node Instance
---@return string?
local function safeRead(node)
	local done, result = false, nil
	task.spawn(function()
		local ok, value = pcall(readSource, node)
		result = ok and value or nil
		done = true
	end)
	local deadline = os.clock() + 10
	while not done and os.clock() < deadline do
		task.wait()
	end
	return result
end

---Collect every script of a tree and its key, the key must match the runtime keyOf.
---@param roots table
---@param tag string
---@return table, number
local function indexTree(roots, tag)
	local rootIndex = {}
	for index, root in ipairs(roots) do
		rootIndex[root] = index
	end

	local positionCache = {}
	local function positionOf(node)
		local parent = node.Parent
		if not parent then
			return 1
		end
		local map = positionCache[parent]
		if not map then
			map = {}
			local counts = {}
			for _, sibling in ipairs(parent:GetChildren()) do
				counts[sibling.Name] = (counts[sibling.Name] or 0) + 1
				map[sibling] = counts[sibling.Name]
			end
			positionCache[parent] = map
		end
		return map[node] or 1
	end

	local function keyOf(inst)
		local parts, node = {}, inst
		while node and not rootIndex[node] do
			local position = positionOf(node)
			table.insert(parts, 1, position > 1 and (node.Name .. "~" .. position) or node.Name)
			node = node.Parent
		end
		return tag .. "/r" .. tostring(rootIndex[node] or 0) .. "/" .. table.concat(parts, "/")
	end

	local list, visited = {}, 0
	local function collect(node)
		visited = visited + 1
		if node:IsA("LuaSourceContainer") then
			table.insert(list, { node = node, key = keyOf(node) })
		end
		if visited % 500 == 0 then
			task.wait()
		end
	end
	for _, root in ipairs(roots) do
		collect(root)
		for _, descendant in ipairs(root:GetDescendants()) do
			collect(descendant)
		end
	end
	return list, visited
end

---Build a standalone client-sided script, nested asset requires are embedded too.
---@param roots table
---@param assetId number?
---@param path string?
---@param options table
---@return string, table
function Proxy.bundle(roots, assetId, path, options)
	options = options or {}
	local stats = {
		scripts = 0, modules = 0, missing = 0, total = 0, assets = 1, nested = {},
		serverOnly = {}, obfuscated = 0, requires = {},
	}
	local trees, chunks = {}, {}
	local seenAssets = { [assetId or 0] = true }

	-- Fast mode (default): no decompile. The runtime re-fetches the asset and runs its real bytecode,
	-- so obfuscated trees convert in seconds. --full also embeds source for offline robustness.
	local fast = not options.full

	local function addTree(treeRoots, tag, id, treePath, depth)
		table.insert(trees, string.format(
			"\t{ tag = %q, id = %s, path = %s },",
			tag, id and tostring(id) or "nil", treePath and string.format("%q", treePath) or "nil"
		))

		local list, visited = indexTree(treeRoots, tag)
		stats.total = stats.total + visited
		local pending = {}

		for index, item in ipairs(list) do
			local node = item.node
			local source = (not fast) and safeRead(node) or nil
			local isModule = node:IsA("ModuleScript")
			stats[isModule and "modules" or "scripts"] = stats[isModule and "modules" or "scripts"] + 1

			if not source then
				if not fast then stats.missing = stats.missing + 1 end
			else
				for _, pair in ipairs(SERVER_ONLY_PATTERNS) do
					if source:find(pair[1], 1, true) and not stats.serverOnly[pair[2]] then
						stats.serverOnly[pair[2]] = node.Name
					end
				end
				if source:find("Luraph Obfuscator", 1, true) or source:find("getfenv%(%)%s*%.%s*LPH") or #source > 200000 then
					stats.obfuscated = stats.obfuscated + 1
				end
				for id in source:gmatch("require%s*%(%s*(%d%d%d+)%s*%)") do
					id = tonumber(id)
					if id and not seenAssets[id] then
						seenAssets[id] = true
						table.insert(pending, id)
					end
				end
				for target in source:gmatch("require%s*%(([^%)\n]+)%)") do
					if #stats.requires < 60 then
						table.insert(stats.requires, node.Name .. " -> " .. target:match("^%s*(.-)%s*$"):sub(1, 60))
					end
				end
			end

			local disabled = false
			if node:IsA("BaseScript") then
				local was = node:GetAttribute(WAS_DISABLED_ATTRIBUTE)
				if was ~= nil then
					disabled = was == true
				else
					local okDisabled, value = pcall(function() return node.Disabled end)
					disabled = okDisabled and value == true
				end
			end

			table.insert(chunks, string.format(
				"\t{ key = %q, class = %q, disabled = %s, source = %s },",
				item.key, node.ClassName, tostring(disabled), source and longString(source) or "false"
			))
			if index % 5 == 0 then
				task.wait()
			end
		end

		-- Smart part: nested asset requires are downloaded and embedded as their own trees.
		if depth < (options.depth or 2) then
			for _, nestedId in ipairs(pending) do
				if stats.assets >= (options.maxAssets or 15) then
					break
				end
				local nestedRoots = fetchObjects(nestedId)
				if nestedRoots then
					stats.assets = stats.assets + 1
					table.insert(stats.nested, nestedId)
					addTree(nestedRoots, "a" .. nestedId, nestedId, nil, depth + 1)
					for _, root in ipairs(nestedRoots) do
						pcall(function() root:Destroy() end)
					end
				end
			end
		end
	end

	local mainTag = assetId and ("a" .. assetId) or "main"
	addTree(roots, mainTag, assetId, path, 0)

	local header = string.format(
		"-- Converted by Ezproxy | %d scripts, %d modules, %d assets, %d without source | client sided\n",
		stats.scripts, stats.modules, stats.assets, stats.missing
	)
	local body = BUNDLE_RUNTIME
		:gsub("__TAG__", function() return string.format("%q", mainTag) end)
		:gsub("__ENTRY__", function() return options.entry and string.format("%q", options.entry) or "false" end)
		:gsub("__TREES__", function() return table.concat(trees, "\n") end)
		:gsub("__DATA__", function() return table.concat(chunks, "\n") end)
	return header .. body, stats
end

-- The SSEmu's own source, fetched once so convert can embed the whole runtime into a single file.
local selfSourceCache = config.selfSource
local function getSelfSource()
	if selfSourceCache and #selfSourceCache > 5000 then
		return selfSourceCache
	end
	-- Self-contained build injects its own source here, so convert needs no URL and no refetch.
	local injected = rawget(shared, "SSEmuSource") or (genv and rawget(genv, "SSEmuSource"))
	if type(injected) == "string" and #injected > 5000 then
		selfSourceCache = injected
		return injected
	end
	if config.loaderUrl then
		local body = httpGet(config.loaderUrl)
		if body and #body > 5000 then
			selfSourceCache = body
			return body
		end
	end
	return nil
end

---Produce a standalone convert output that embeds the FULL SSEmu and auto-runs the asset.
---Single file, no proxy, 100% feature parity (drops, every service mock, relative requires).
---@param assetId number
---@param entry string? Original loader line, run instead of the bare asset when given.
---@return string?
function Proxy.bundleFull(assetId, entry, path)
	local header = string.format(
		"-- Converted by Ezproxy (full SSEmu engine inside) | %s | single file, runs without the proxy\n",
		assetId and ("asset " .. string.format("%d", assetId)) or (path and ("path " .. tostring(path)) or "exec line")
	)
	-- A one-shot job instead of SSEmuConfig, so the user's own config survives and nothing sticks in shared.
	local assetText = assetId and string.format("%d", assetId) or "nil"
	local entryText = entry and string.format("%q", entry) or "nil"
	local pathText = path and string.format("%q", path) or "nil"
	local cfg = string.format(
		"shared.SSEmuConverted = { asset = %s, entry = %s, path = %s, previous = shared.SSEmuConfig }\n"
			.. "shared.SSEmuConfig = { noProxy = true, convertedAsset = %s, convertedEntry = %s, convertedPath = %s, replicate = false }\n",
		assetText, entryText, pathText, assetText, entryText, pathText
	)
	-- The engine carries its own source (the loader keeps it in shared.SSEmuSource), so this never
	-- needs a URL. Bytecode is only a fallback for a build that was started some other way.
	local src = getSelfSource()
	if src then
		return header .. cfg .. src .. "\n"
	end
	if selfBytecode then
		return header .. cfg .. "local fn = loadstring(" .. string.format("%q", selfBytecode) .. ")\nif fn then fn() end\n"
	end
	return nil
end

---Run a converted instance of the game: found again by path (the game may still be loading) and
---converted live, exactly like .convert did when the file was made.
---@param path string
---@return Instance
function SSEmu.runConvertedPath(path)
	local inst
	for _ = 1, 20 do
		inst = resolvePath(path)
		if inst then
			break
		end
		task.wait(0.5)
	end
	if not inst then
		error("Converted path not found in this game: " .. path, 2)
	end
	log("Converted path: " .. path, INFO_COLOR)
	return SSEmu.convert(inst)
end

---Pull an asset id out of a bare id, require(id), rbxassetid://id or a roblox.com link.
---@param target string
---@return number?
function Proxy.assetIdOf(target)
	return tonumber(
		target:match("require%s*%(%s*(%d+)%s*%)")
			or target:match("^(%d+)$")
			or target:match("^rbxassetid://(%d+)")
			or target:match("^https?://[%w%.%-]*roblox%.com/.-(%d%d%d%d%d+)")
	)
end

---Download the asset once at convert time and report what is in it, so a dead or module-less asset
---is noticed now instead of when the converted file is run.
---@param assetId number
---@param entry string?
---@return boolean
function Proxy.reportAsset(assetId, entry)
	Proxy.emit("Convert: checking asset " .. assetId .. "...", "info")
	local roots = fetchObjects(assetId, 2)
	if not roots then
		Proxy.emit("Asset " .. assetId .. " could not be downloaded right now (private, deleted or not a model). "
			.. "The converted file will fail the same way until it can be.", "warn")
		return false
	end

	local counts = { total = 0, Script = 0, LocalScript = 0, ModuleScript = 0, Tool = 0, gui = 0, remote = 0 }
	local function visit(node)
		counts.total = counts.total + 1
		local className = node.ClassName
		if counts[className] then
			counts[className] = counts[className] + 1
		elseif REMOTE_CLASSES[className] then
			counts.remote = counts.remote + 1
		elseif GUI_CLASSES[className] then
			counts.gui = counts.gui + 1
		end
	end
	for _, root in ipairs(roots) do
		visit(root)
		for index, node in ipairs(root:GetDescendants()) do
			visit(node)
			if index % 2000 == 0 then
				task.wait()
			end
		end
	end
	local explicitMain = findExplicitMainModule(roots) ~= nil
	local anyModule = findMainModule(roots) ~= nil
	for _, root in ipairs(roots) do
		pcall(function() root:Destroy() end)
	end

	Proxy.emit(string.format(
		"Analysis: %d instances, %d scripts, %d local scripts, %d modules, %d tools, %d GUIs, %d remotes, MainModule: %s",
		counts.total, counts.Script, counts.LocalScript, counts.ModuleScript, counts.Tool, counts.gui, counts.remote,
		explicitMain and "yes" or (anyModule and "nested only" or "no")
	), "info")
	if entry and not anyModule then
		Proxy.emit("The asset has no ModuleScript, require(" .. assetId .. ") in the entry line will fail", "warn")
	elseif not entry and explicitMain then
		Proxy.emit("Tip: if this hub needs a call, convert the whole loader line, e.g. .convert require("
			.. assetId .. ").load(owner.Name)", "info")
	end
	return true
end

---Send a finished script to the proxy in parts so large bundles never choke the request.
---@param label string
---@param text string
function Proxy.sendBundle(label, text)
	local size = 30000
	local total = math.max(1, math.ceil(#text / size))
	for part = 1, total do
		local sent = false
		for _ = 1, 3 do
			if Proxy.send("POST", "/convert", {
				label = label,
				part = part,
				total = total,
				data = text:sub((part - 1) * size + 1, part * size),
			}) then
				sent = true
				break
			end
			task.wait(0.5)
		end
		if not sent then
			return Proxy.emit("Convert upload failed at part " .. part .. "/" .. total, "error")
		end
		if part % 3 == 0 then
			task.wait()
		end
	end
end

---Split ".convert <target> --depth 3 --max 20 --dry" into target and options.
---@param raw string
---@return string, table
local function parseConvertArguments(raw)
	local options = { depth = 2, maxAssets = 15 }
	local target = raw
	for flag, value in raw:gmatch("%-%-(%a+)%s*(%d*)") do
		if flag == "depth" and value ~= "" then
			options.depth = tonumber(value)
		elseif flag == "max" and value ~= "" then
			options.maxAssets = tonumber(value)
		elseif flag == "dry" then
			options.dry = true
		elseif flag == "flat" then
			options.depth = 0
		elseif flag == "full" then
			options.full = true
		elseif flag == "lite" then
			options.lite = true
		end
	end
	-- Only the known flags are cut out, a "--" inside converted code stays where it is.
	for _, flag in ipairs({ "depth", "max", "dry", "flat", "full", "lite" }) do
		target = (" " .. target):gsub("%s%-%-" .. flag .. "%s*%d*", ""):sub(2)
	end
	target = target:match("^%s*(.-)%s*$")
	return target, options
end

Proxy.handlers.convert = function(command)
	if mirroredReplica(command) then
		return
	end
	local target, options = parseConvertArguments(tostring(command.target or ""))
	local assetId = Proxy.assetIdOf(target)

	-- ".convert require(id).load(owner.Name)": the part after require(id) is kept, the converted file
	-- runs the whole line instead of only requiring the asset.
	-- Anything that is not a bare asset id, an asset link or a path of the game is code: the converted
	-- file runs that exact text through SSEmu.execute, the same way exec runs it.
	local bareAsset = target:match("^%d+$") or target:match("^rbxassetid://%d+$") or target:match("^https?://")
	local okPath, livePath = pcall(resolvePath, target)
	local entry = nil
	if target ~= "" and not bareAsset and not (okPath and livePath) then
		entry = target
	end
	options.entry = entry

	-- Default for every target: the whole engine goes into the output, so the converted file runs on
	-- its own, without the proxy, with everything the live emulation has. --lite asks for the small
	-- runtime instead.
	local pathTarget = (not assetId and not entry and target ~= "") and target or nil
	if not options.lite and (assetId or pathTarget or entry) then
		local pathInstance = pathTarget and resolvePath(pathTarget)
		if pathTarget and not pathInstance then
			return Proxy.emit("Not found: " .. pathTarget, "error")
		end
		local fullText = Proxy.bundleFull(assetId, entry, pathTarget)
		if fullText then
			if assetId then
				Proxy.reportAsset(assetId, entry)
			elseif pathTarget then
				-- A game instance is also converted live, as before.
				local okLive, liveError = pcall(SSEmu.convert, pathInstance, command.replica)
				if not okLive then
					Proxy.emit("Live convert note: " .. tostring(liveError), "warn")
				end
				Proxy.emit("The converted file looks the instance up by this path, so it works in this game only", "info")
			end
			if entry then
				Proxy.emit("Convert: entry line kept -> " .. entry, "info")
			end
			if options.dry then
				return Proxy.emit("Dry run (full engine), " .. #fullText .. " bytes not sent", "info")
			end
			Proxy.emit(string.format("Convert: full engine inside (%d KB), runs without the proxy", math.floor(#fullText / 1024)), "info")
			local label = assetId and ("require_" .. assetId .. "_full")
				or (pathTarget and ("convert_" .. (pathTarget:match("([%w_]+)$") or "instance") .. "_full"))
				or "exec_full"
			return Proxy.sendBundle(label, fullText)
		end
		Proxy.emit("The engine has no copy of its own source (it was not started through its loader file), using the lite bundle", "warn")
	end

	local roots, label, path, fetched
	if assetId then
		Proxy.emit("Convert: downloading " .. assetId .. "...", "info")
		roots = fetchObjects(assetId, 2)
		label, fetched = "require_" .. assetId, true
	else
		if entry then
			return Proxy.emit("Code can only be converted with the full engine (no --lite)", "error")
		end
		local inst = resolvePath(target)
		if not inst then
			return Proxy.emit("Path not found: " .. target, "error")
		end
		roots, label, path = { inst }, (inst.Name:gsub("[^%w_%-]", "_")), target
		if not options.dry then
			SSEmu.convert(inst, command.replica)
		end
	end
	if not roots then
		return Proxy.emit("Convert failed: the asset could not be downloaded", "error")
	end

	local ok, text, stats = pcall(Proxy.bundle, roots, assetId, path, options)
	if fetched then
		for _, root in ipairs(roots) do
			pcall(function() root:Destroy() end)
		end
	end
	if not ok then
		return Proxy.emit("Convert failed: " .. tostring(text), "error")
	end

	-- Analysis report.
	Proxy.emit(string.format("Analysis: %d instances, %d scripts, %d modules, %d nested assets, %d unreadable",
		stats.total, stats.scripts, stats.modules, stats.assets - 1, stats.missing), "info")
	if #stats.nested > 0 then
		Proxy.emit("Embedded assets: " .. table.concat(stats.nested, ", "), "info")
	end
	for api, scriptName in pairs(stats.serverOnly) do
		Proxy.emit("Server-only API " .. api .. " in " .. scriptName .. " (runs on the client, may do nothing)", "warn")
	end
	if stats.obfuscated > 0 then
		Proxy.emit(stats.obfuscated .. " script(s) look obfuscated or very large, they are embedded unchanged", "warn")
	end
	if stats.missing > 0 then
		Proxy.emit(stats.missing .. " script(s) had no readable source, they run from their bytecode at runtime", "warn")
	end
	if entry then
		Proxy.emit("Convert: entry line kept -> " .. entry, "info")
	end

	if options.dry then
		return Proxy.emit("Dry run, " .. #text .. " bytes not sent", "info")
	end
	Proxy.sendBundle(label, text)
end

end

Proxy.handlers.load = function(command)
	if mirroredReplica(command) then
		return
	end
	local target = tostring(command.target or "")
	local assetId = Proxy.assetIdOf(target)
	local ok, err
	if assetId then
		ok, err = Proxy.runBroadcast(command, SSEmu.loadModel, assetId)
	elseif target:match("^https?://") then
		ok, err = Proxy.runBroadcast(command, SSEmu.loadUrl, target)
	else
		return Proxy.emit("Usage: .load <assetId|url>", "warn")
	end
	if not ok then
		Proxy.emit("Load failed: " .. tostring(err), "error")
	end
end

Proxy.handlers.execclient = function(command)
	local runner, err = SSEmu.babyboo({
		Contents = command.source,
		RunContext = Enum.RunContext.Client,
	})
	if not runner then
		return Proxy.emit("Client run failed: " .. tostring(err), "error")
	end
	task.spawn(runner)
	Proxy.emit("Client script executed", "info")
end

Proxy.handlers.strict = function(command)
	SSEmu.setStrict(command.on == true)
	Proxy.emit("Strict server mode " .. (command.on and "on" or "off") .. " (Players.LocalPlayer is " .. (command.on and "nil" or "visible") .. ")", "info")
end

Proxy.handlers.fakeplayer = function(command)
	-- A fake player of the origin reaches the replicas as a mirrored character, not as a second fake.
	if mirroredReplica(command) then
		return
	end
	local action = command.action or (command.on and "add" or "clear")
	if action == "add" then
		local fake = SSEmu.createFakePlayer(command.name or "FakePlayer")
		Proxy.emit("Fake player: " .. rawget(fake, "Name"), "info")
	elseif action == "remove" then
		for _, fake in ipairs(table.clone(SSEmu.getFakePlayers())) do
			if rawget(fake, "Name") == command.name then
				SSEmu.removeFakePlayer(fake)
			end
		end
	elseif action == "chat" then
		if not SSEmu.fakeChat(command.name, command.message or "") then
			Proxy.emit("No fake player named " .. tostring(command.name), "warn")
		end
	elseif action == "list" then
		local names = {}
		for _, fake in ipairs(SSEmu.getFakePlayers()) do
			table.insert(names, rawget(fake, "Name"))
		end
		Proxy.emit("Fake players (" .. #names .. "): " .. table.concat(names, ", "), "server")
	else
		for _, fake in ipairs(table.clone(SSEmu.getFakePlayers())) do
			SSEmu.removeFakePlayer(fake)
		end
	end
end

Proxy.handlers.replicaEvent = function(command)
	applyEvent(command.event)
end

Proxy.handlers.kick = function(command)
	local wanted = tostring(command.name):lower()
	local name, display = localPlayer.Name:lower(), localPlayer.DisplayName:lower()
	if name:sub(1, #wanted) == wanted or display:sub(1, #wanted) == wanted then
		Proxy.emit("Kicking " .. localPlayer.Name .. ": " .. tostring(command.reason), "warn")
		task.wait(0.3)
		localPlayer:Kick(tostring(command.reason))
	end
end

Proxy.handlers.players = function()
	local names = {}
	for _, player in ipairs(playersService:GetPlayers()) do
		table.insert(names, player.Name)
	end
	Proxy.emit("Players (" .. #names .. "): " .. table.concat(names, ", "), "server")
end

Proxy.handlers.rescan = function()
	Proxy.emit("Indexing scripts...", "info")
	Proxy.reconstruct()
end

---Report a require performed inside the sandbox.
---@param target any
---@param caller Instance?
function Proxy.onRequire(target, caller)
	local label = tostring(target)
	if realTypeof(target) == "Instance" then
		local ok, name = pcall(target.GetFullName, target)
		label = ok and name or target.Name
	end

	local from = "ExternalScript"
	if caller then
		local ok, name = pcall(caller.GetFullName, caller)
		from = ok and name or caller.Name
	end
	Proxy.emit("require(" .. label .. ") <- " .. from, "require")
end

---Attach to the proxy and start the headless loops.
function Proxy.start()
	SSEmu.onRequire = Proxy.onRequire
	Proxy.hello()

	-- Batch log lines so the proxy console stays smooth.
	task.spawn(function()
		while active do
			task.wait(0.3)
			if #Proxy.queue > 0 then
				local lines = Proxy.queue
				Proxy.queue = {}
				Proxy.send("POST", "/log", { lines = lines })
			end
		end
	end)

	-- Long-poll commands typed into the proxy console.
	task.spawn(function()
		while active do
			local startedAt = os.clock()
			local response = Proxy.send("GET", "/cmd?client=" .. httpService:UrlEncode(Proxy.clientId))

			if not response then
				task.wait(3)
			elseif response.idle then
				Proxy.applyState(response)
			elseif response.cmd or response.cmds then
				-- The proxy sends everything that was waiting at once (older proxies: one command).
				local batch = type(response.cmds) == "table" and response.cmds or { response.cmd }
				for _, command in ipairs(batch) do
					local handler = type(command) == "table" and Proxy.handlers[command.type]
					if handler then
						local ok, err = pcall(handler, command)
						if not ok then
							Proxy.emit("Command failed: " .. tostring(err), "error")
						end
					end
				end
			elseif os.clock() - startedAt < 2 then
				-- The proxy answered instantly, so it forgot this client, register again.
				task.wait(2)
				Proxy.hello()
				task.spawn(Proxy.reconstruct)
			end
		end
	end)

	task.spawn(Proxy.reconstruct)
end

-- ═══════════════════════════════════════════════════════════════════
-- PUBLIC API
-- ═══════════════════════════════════════════════════════════════════

---Run source inside the server emulation.
---@param source string
---@param name string?
---@param replica boolean?
---@return boolean, string?
function SSEmu.execute(source, name, replica, silent, origin)
	local container = create("Script", { Name = name or "Script", Disabled = true }, serverScriptService)
	-- Code a broadcast command runs on every client (.load <url>): what it makes is marked like
	-- broadcast assets, through the origin its Instance.new calls inherit.
	if SSEmu.dispatchThreads[coroutine.running()] then
		pcall(container.SetAttribute, container, ORIGIN_ATTRIBUTE, "dispatch:exec")
	end
	if replica then
		container:SetAttribute(REPLICA_ATTRIBUTE, true)
	elseif not silent then
		SSEmu.replicate("script", { source = source, origin = { userId = localPlayer.UserId, name = localPlayer.Name } })
	end

	-- The text is kept so an error report can show the failing line of what was typed.
	sourceOverrides[container] = source

	-- Replicas see the player that ran the script as owner, like a real server would.
	if origin and origin.userId then
		local ownerPlayer = playersService:GetPlayerByUserId(tonumber(origin.userId) or 0)
		if ownerPlayer then
			contextOwners[container] = ownerPlayer
		end
	end
	local func, err = realLoadstring(source, "=" .. container.Name)
	if not func then
		log("Error: " .. tostring(err), ERROR_COLOR)
		return false, err
	end

	infect(func, container, false)
	started[container] = true
	runSandboxed(func, container)
	return true
end

SSEmu.require = smartRequire
SSEmu.giveTool = giveTool
SSEmu.loadAsset = loadAsset
SSEmu.giveAsset = giveAsset

---Stop the emulation and restore the executor environment.
function SSEmu.detach()
	if SSEmu.stopReplication then
		SSEmu.stopReplication()
	end
	for _, callback in ipairs(closeCallbacks) do
		pcall(callback)
	end
	active = false
	SSEmu.logHandler = nil
	SSEmu.onRequire = nil

	for _, connection in ipairs(connections) do
		pcall(function() connection:Disconnect() end)
	end
	table.clear(connections)

	for key, saved in pairs(savedGlobals) do
		genv[key] = saved.value
	end
	table.clear(savedGlobals)

	SSEmu.running = false
	pcall(function() moduleHolder:Destroy() end)
	pcall(function() serverRoot:Destroy() end)
end

-- ═══════════════════════════════════════════════════════════════════
-- ENTRY POINT
-- ═══════════════════════════════════════════════════════════════════

---Build everything and publish the singleton.
local function initializeScript()
	-- Console lines go to the proxy instead of a GUI.
	SSEmu.logHandler = function(text, color)
		Proxy.emit(text, Proxy.kindOf(color))
	end

	installRemoteHooks(false)
	local testOk, testErr = selfTest()
	if not testOk then
		installRemoteHooks(true)
		testOk, testErr = selfTest()
	end
	startServerEvents()
	setupWatchers()
	setupToolDrops()
	setupSeats()
	setupKillHandler()
	setupDedupe()
	setupLiveConvert()
	if TAKEOVER_GENV then
		takeoverGlobals()
	end
	if testOk then
		log("Remote replication ready", INFO_COLOR)
	else
		log("Remote replication failed: " .. tostring(testErr), ERROR_COLOR)
	end

	shared.SSEmu = SSEmu
	shared.Re2lua = SSEmu
	if REPLICATION_ENABLED then
		SSEmu.startReplication()
	end

	-- Standalone converted build: run the embedded asset, skip the proxy console.
	if config.convertedAsset or config.convertedEntry or config.convertedPath then
		task.spawn(function()
			task.wait(0.25)
			local ok, err = pcall(SSEmu.runConverted, config.convertedAsset, config.convertedEntry, config.convertedPath)
			if not ok then
				log("Converted asset failed: " .. tostring(err), ERROR_COLOR)
			end
		end)
	end

	if config.noProxy then
		log("Server ready (standalone). Player: " .. localPlayer.Name .. " (" .. localPlayer.UserId .. ")", INFO_COLOR)
	else
		Proxy.start()
		log("Server ready. Player: " .. localPlayer.Name .. " (" .. localPlayer.UserId .. ")", INFO_COLOR)
	end
end

---Called when initialization errors.
---@param err string
local function onInitializeError(err)
	warn("Failed to initialize.")
	warn(cleanText(err))
	warn(cleanText(debug.traceback()))
	SSEmu.detach()
end

-- Safely initialize the script as well as handle errors.
xpcall(initializeScript, onInitializeError)
]==============]

if shared then
	shared.SSEmuSource = SOURCE
end
local engine, compileError = loadstring(SOURCE, "=SSEmu")
if not engine then
	return warn("Ezproxy engine failed to compile: " .. tostring(compileError))
end
-- The engine runs in this file's own environment, exactly as if its code stood here directly.
pcall(setfenv, engine, getfenv())
return engine(...)