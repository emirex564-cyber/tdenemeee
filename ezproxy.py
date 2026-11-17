#!/usr/bin/env python3
import difflib
import glob
import json
import os
import platform
import queue
import re
import subprocess
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

# Arrow keys and history for input(). Windows needs: pip install pyreadline3
try:
    import readline
    readline.parse_and_bind("tab: complete")
    readline.set_completer(lambda text, index: completer(text, index))
    readline.set_completer_delims(" \t\n")
except ImportError:
    readline = None

# Optional: pip install prompt_toolkit keeps the typed line intact while logs stream in.
def loadPromptToolkit():
    try:
        import prompt_toolkit
        return prompt_toolkit
    except ImportError:
        return None


pt = loadPromptToolkit()
if pt:
    from prompt_toolkit import PromptSession
    from prompt_toolkit.patch_stdout import patch_stdout
    from prompt_toolkit.history import InMemoryHistory

HOST, PORT = "127.0.0.1", 1337
PROMPT = "> "
STARTED = time.time()

os.system("")
RESET, GRAY, RED, GREEN = "\033[0m", "\033[90m", "\033[91m", "\033[92m"
YELLOW, CYAN, BLUE, WHITE = "\033[93m", "\033[96m", "\033[94m", "\033[97m"
KIND_COLORS = {"info": GREEN, "warn": YELLOW, "error": RED, "require": CYAN, "trace": GRAY, "print": WHITE, "server": BLUE}

lock = threading.Lock()
printLock = threading.Lock()
clients = {}
rooms = {}
scripts = []
requireEvents = []
stats = {"lines": 0, "requires": 0, "converts": [], "errors": 0}
# FilteringEnabled starts OFF: every change on a connected client (its game scripts' effects included)
# travels from the first second. ".fe enable" turns normal filtering back on.
state = {"logs": True, "prompt": False, "reading": False, "replication": True, "fakeplayer": False,
         "feOff": True, "feScope": "all", "feMode": "mirror"}
bundles = {}
lastLine = {"text": "", "count": 0}


def out(text="", color=""):
    with printLock:
        if pt:
            # patch_stdout redraws the prompt itself.
            sys.stdout.write(color + text + RESET + "\n")
        else:
            sys.stdout.write("\r\033[K" + color + text + RESET + "\n")
            if state["reading"]:
                sys.stdout.write(PROMPT)
        sys.stdout.flush()


def stamp():
    now = time.time()
    return time.strftime("%H:%M:%S", time.localtime(now)) + ".%03d" % int((now % 1) * 1000)


hiddenNames = {"opiumware", "potassium"}


def clean(text):
    lines = []
    for line in str(text).split("\n"):
        lower = line.strip().lower()
        skip = False
        for name in hiddenNames:
            escaped = re.escape(name)
            if re.match(escaped + r"[\w.\-]*:\d+\s*$", lower) or re.match(escaped + r"[\w.\-]*:\d+ function", lower) \
                    or re.match(r"script '[^']*" + escaped + r"[^']*', line \d+", lower):
                skip = True
                break
            line = re.sub(r"(?i)" + escaped + r"[\w.\-]*:\d+:?\s*", "", line)
            line = re.sub(r"(?i)script '[^']*" + escaped + r"[^']*', line \d+\s*-*\s*", "", line)
        if not skip and line.strip():
            lines.append(line)
    return "\n".join(lines)


BADGES = {
    "info": ("INFO ", GREEN), "warn": ("WARN ", YELLOW), "error": ("ERROR", RED),
    "require": ("REQ  ", CYAN), "trace": ("TRACE", GRAY), "print": ("PRINT", WHITE), "server": ("SRV  ", BLUE),
}


def serverLog(text, kind="print"):
    if not state["logs"]:
        return
    text = clean(text)
    if not text:
        return
    if text == lastLine["text"] and time.time() - lastLine.get("time", 0) < 2:
        return
    lastLine["text"], lastLine["time"] = text, time.time()
    stats["lines"] += 1
    if kind == "error":
        stats["errors"] += 1
    badge, color = BADGES.get(kind, BADGES["print"])
    first, *rest = text.split("\n")
    out("%s%s%s %s%s%s %s" % (GRAY, stamp(), RESET, color, badge, RESET, first))
    for line in rest:
        out("%s%s%s %s" % (GRAY, " " * 12 + "  " + " " * 5, RESET, line))


def logDirs():
    system = platform.system()
    if system == "Windows":
        return [os.path.join(os.environ.get("LOCALAPPDATA", ""), "Roblox", "logs")]
    if system == "Darwin":
        return [os.path.expanduser("~/Library/Logs/Roblox")]
    return []


def findUdmux():
    files = []
    for directory in logDirs():
        files += glob.glob(os.path.join(directory, "*.log"))
    files.sort(key=os.path.getmtime, reverse=True)
    for path in files[:6]:
        try:
            with open(path, "r", errors="ignore") as handle:
                data = handle.read()
        except OSError:
            continue
        found = re.findall(r"UDMUX server (\d{1,3}(?:\.\d{1,3}){3}):(\d+)", data)
        if found:
            return found[-1]

    # macOS fallback, read the live socket of the player process.
    if platform.system() == "Darwin":
        try:
            result = subprocess.run(["lsof", "-nP", "-iUDP", "-a", "-c", "RobloxPlayer"], capture_output=True, text=True, timeout=5)
            found = re.findall(r"->(\d{1,3}(?:\.\d{1,3}){3}):(\d+)", result.stdout)
            if found:
                return found[-1]
        except Exception:
            pass
    return None


class QuietServer(ThreadingHTTPServer):
    daemon_threads = True

    def handle_error(self, request, client_address):
        pass


def getRoom(name):
    with lock:
        if name not in rooms:
            rooms[name] = {"events": [], "seq": 0, "cv": threading.Condition()}
        return rooms[name]


def liveClients():
    now = time.time()
    with lock:
        for key in [k for k, c in clients.items() if now - c["last"] > 45]:
            del clients[key]
        return list(clients.values())


def dispatch(command):
    # With replication on every client runs the command, the first one is the origin player.
    targets = liveClients()
    if not targets:
        out("No clients connected to the proxy.", YELLOW)
        return 0
    info = targets[0]["info"]
    origin = {"userId": info.get("userId"), "name": info.get("name")}
    targets[0]["cmds"].put(dict(command, origin=origin))
    if state["replication"]:
        for client in targets[1:]:
            client["cmds"].put(dict(command, replica=True, origin=origin))
    return len(targets) if state["replication"] else 1


def feState():
    # What every reply to a client carries, so late joiners pick up FilteringEnabled too.
    return {"replication": state["replication"], "filteringEnabled": not state["feOff"], "feScope": state["feScope"],
            "feMode": state["feMode"]}


def setFilteringEnabled(enabled, scope=None):
    if scope in ("executor", "all"):
        state["feScope"] = scope
    state["feOff"] = not enabled
    if state["feOff"] and not state["replication"]:
        state["replication"] = True
        broadcast({"type": "replication", "on": True})
    sent = broadcast({"type": "fe", "enabled": enabled, "scope": state["feScope"]})
    if enabled:
        out("FilteringEnabled = true (normal filtering)", GREEN)
    else:
        out("FilteringEnabled = false, scope %s: every client's world changes replicate to all %d client(s)" % (state["feScope"], sent), YELLOW)


def broadcast(command):
    with lock:
        targets = list(clients.values())
    if not targets:
        out("No clients connected to the proxy.", YELLOW)
        return 0
    for client in targets:
        client["cmds"].put(command)
    return len(targets)


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *args):
        pass

    def reply(self, obj):
        data = json.dumps(obj).encode()
        try:
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)
            self.wfile.flush()
            return True
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, OSError):
            return False

    def readBody(self):
        length = int(self.headers.get("Content-Length") or 0)
        try:
            return json.loads(self.rfile.read(length) or b"{}")
        except ValueError:
            return {}

    def do_GET(self):
        parsed = urlparse(self.path)
        query = parse_qs(parsed.query)

        if parsed.path == "/poll":
            room = getRoom(query.get("room", ["default"])[0])
            since = int(query.get("since", ["-1"])[0])
            deadline = time.time() + min(int(query.get("wait", ["0"])[0]), 8)
            with room["cv"]:
                while True:
                    events = [e for e in room["events"] if e["seq"] > since]
                    remaining = deadline - time.time()
                    if events or remaining <= 0:
                        break
                    room["cv"].wait(remaining)
            return self.reply({"events": events, "last": room["seq"]})

        if parsed.path == "/cmd":
            client = clients.get(query.get("client", [""])[0])
            if not client:
                return self.reply({})
            client["last"] = time.time()
            client["gen"] = client.get("gen", 0) + 1
            mine = client["gen"]
            deadline = time.time() + 5
            while time.time() < deadline and client["gen"] == mine:
                try:
                    command = client["cmds"].get(timeout=0.4)
                except queue.Empty:
                    continue
                # Everything already waiting goes in the same reply: one command per request made the
                # client fall further behind with every mirror update (the delay kept growing).
                batch = [command]
                while len(batch) < 500:
                    try:
                        batch.append(client["cmds"].get_nowait())
                    except queue.Empty:
                        break
                # Put the commands back when the client already hung up.
                if not self.reply({"cmd": batch[0], "cmds": batch}):
                    for item in batch:
                        client["cmds"].put(item)
                return
            return self.reply(dict(feState(), idle=True))

        self.reply({})

    def do_POST(self):
        path = urlparse(self.path).path
        body = self.readBody()

        if path == "/push":
            if state["replication"]:
                event = {"type": body.get("type"), "payload": body.get("payload"), "client": body.get("client")}
                with lock:
                    others = [c for key, c in clients.items() if key != body.get("client")]
                for client in others:
                    client["cmds"].put({"type": "replicaEvent", "event": event})
            room = getRoom(body.get("room", "default"))
            with room["cv"]:
                room["seq"] += 1
                room["events"].append({"seq": room["seq"], "client": body.get("client"), "type": body.get("type"), "payload": body.get("payload")})
                del room["events"][:-500]
                room["cv"].notify_all()

        elif path == "/hello":
            for name in body.get("hidden", []):
                hiddenNames.add(str(name).lower())
            with lock:
                known = body["client"] in clients
                if known:
                    clients[body["client"]]["info"] = body
                    clients[body["client"]]["last"] = time.time()
                else:
                    clients[body["client"]] = {"info": body, "cmds": queue.Queue(), "last": time.time()}
            if not known:
                serverLog("Player joined: %s (%s) | PlaceId %s | JobId %s" % (body.get("name"), body.get("userId"), body.get("placeId"), body.get("jobId")), "info")
            return self.reply(dict(feState(), ok=True))

        elif path == "/convert":
            label = re.sub(r"[^\w\-]", "_", str(body.get("label", "converted")))
            entry = bundles.setdefault(label, {})
            entry[int(body.get("part", 1))] = body.get("data", "")
            if len(entry) >= int(body.get("total", 1)):
                text = "".join(entry[i] for i in sorted(entry))
                del bundles[label]
                folder = os.path.join(os.path.dirname(os.path.abspath(__file__)), "converted")
                os.makedirs(folder, exist_ok=True)
                target = os.path.join(folder, label + ".lua")
                with open(target, "w", encoding="utf-8", newline="\n") as handle_file:
                    handle_file.write(text)
                copyClipboard(text)
                stats["converts"].append((label, target, len(text)))
                serverLog("Convert saved: %s (%.1f KB, copied to clipboard)" % (target, len(text) / 1024), "info")

        elif path == "/log":
            for entry in body.get("lines", []):
                kind = entry.get("kind", "print")
                serverLog(entry.get("text", ""), kind)
                if kind == "require":
                    requireEvents.append(entry.get("text", ""))
                    stats["requires"] += 1

        elif path == "/scripts":
            if body.get("reset"):
                scripts.clear()
            scripts.extend(body.get("items", []))
            if body.get("last"):
                counts = {}
                for item in scripts:
                    counts[item["class"]] = counts.get(item["class"], 0) + 1
                summary = ", ".join("%d %s" % (n, c) for c, n in counts.items())
                serverLog("Indexed %d scripts (%s)" % (len(scripts), summary), "info")

        self.reply({"ok": True})


def copyClipboard(text):
    try:
        system = platform.system()
        command = ["clip"] if system == "Windows" else ["pbcopy"] if system == "Darwin" else ["xclip", "-selection", "clipboard"]
        subprocess.run(command, input=text.encode("utf-16" if system == "Windows" else "utf-8"), timeout=5)
    except Exception:
        pass


def printTree(filterText=None):
    printed = set()
    shown = 0
    for item in sorted(scripts, key=lambda s: s["path"]):
        if filterText and filterText.lower() not in item["path"].lower():
            continue
        parts = item["path"].split(".")
        for depth in range(len(parts) - 1):
            key = ".".join(parts[: depth + 1])
            if key not in printed:
                printed.add(key)
                out("  " * depth + parts[depth], GRAY)
        out("  " * (len(parts) - 1) + parts[-1] + " <" + item["class"] + ">", WHITE)
        for target in item.get("requires", []):
            out("  " * len(parts) + "-> require(" + target + ")", CYAN)
        shown += 1
    out("%d scripts" % shown, GREEN)


def listPlayers():
    current = liveClients()
    out("Proxy clients (%d):" % len(current), GREEN)
    for client in current:
        info = client["info"]
        out("  %s (%s) | JobId %s" % (info.get("name"), info.get("userId"), info.get("jobId")), WHITE)
    if current:
        broadcast({"type": "players"})


def helpText():
    groups = [
        ("Server", [
            (".exec <lua>", "run on the server (all clients when replication is on)"),
            (".execclient <lua>", "run a script as client (reversed babyboo, real game env)"),
            (".strict on|off", "hide Players.LocalPlayer from server scripts like a real server"),
            (".execfile <path>", "run a lua file"),
            (".require <id|path>", "require an asset id or module path"),
            (".give <id>", "give an asset or tool"),
            (".load <id|url>", "load an admin loader model (Adonis, HD Admin...) or a url script"),
        ]),
        ("Convert", [
            (".convert require(<id>)", "full client sided script, nested requires embedded"),
            (".convert <path>", "same for an instance in the game"),
            ("   flags", "--depth N  --max N  --dry  --flat"),
            (".converts", "list saved conversions"),
            (".open", "open the converted folder"),
        ]),
        ("Network", [
            (".fe disable [all]", "FilteringEnabled off: every client's world changes replicate to all (all = game LocalScripts too)"),
            (".fe enable", "FilteringEnabled on: normal filtering"),
            (".diag", "every client reports its mirror state: connected, sent, received, last error"),
            (".share <path>", "push something you see to everyone by hand, e.g. .share Workspace.LocalMap"),
            (".femode mirror|convert", "mirror (default): you run it, everyone sees the same thing in the same place; convert: every client runs its own copy"),
            (".replication enable|disable", "mirror execution to every client"),
            (".mirror on|off", "FE-disabled style: origin's world state is streamed to the alts (default on)"),
            (".resync", "resend the whole mirrored world to every client"),
            (".fakeplayer add|remove|chat|list|clear", "fake players that react to server scripts"),
            (".kick <name> [reason]", "kick a proxy connected player"),
            (".players", "proxy clients and in-game players"),
        ]),
        ("Console", [
            (".logs on|off", "server console stream"),
            (".status", "dashboard"),
            (".scripts [filter]", "script tree with requires"),
            (".search <text>", "find scripts and require targets"),
            (".requires", "requires seen at runtime"),
            (".rescan", "rebuild the script tree"),
            (".clear  .exit", ""),
        ]),
    ]
    for title, rows in groups:
        out("")
        out("  " + title, BLUE)
        for name, text in rows:
            out("    %s%-30s%s %s%s%s" % (CYAN, name, RESET, GRAY, text, RESET))
    out("")


def statusBoard():
    current = liveClients()
    up = int(time.time() - STARTED)
    on, off = GREEN + "on" + RESET, RED + "off" + RESET
    out("")
    out("  Ezproxy %s127.0.0.1:%d%s  uptime %02d:%02d:%02d" % (GRAY, PORT, RESET, up // 3600, up // 60 % 60, up % 60), WHITE)
    fe = (RED + "false" + RESET + " (" + state["feScope"] + ")") if state["feOff"] else (GREEN + "true" + RESET)
    out("  replication %s   logs %s   fakeplayer %s   FilteringEnabled %s   femode %s" % (on if state["replication"] else off, on if state["logs"] else off, on if state["fakeplayer"] else off, fe, state["feMode"]))
    out("  clients %d   scripts %d   requires %d   log lines %d   errors %d   converts %d" % (
        len(current), len(scripts), stats["requires"], stats["lines"], stats["errors"], len(stats["converts"])), GRAY)
    for client in current:
        info = client["info"]
        out("    %s* %s%s (%s)  last seen %.0fs ago" % (GREEN, RESET, info.get("name"), info.get("userId"), time.time() - client["last"]), WHITE)
    out("")


def searchScripts(text):
    needle = text.lower()
    found = 0
    for item in sorted(scripts, key=lambda s: s["path"]):
        hits = [r for r in item.get("requires", []) if needle in r.lower()]
        if needle in item["path"].lower() or hits:
            found += 1
            out("  %s%s%s <%s>" % (WHITE, item["path"], RESET, item["class"]))
            for hit in hits:
                out("      %s-> require(%s)%s" % (CYAN, hit, RESET))
    out("%d match(es)" % found, GREEN)


COMMANDS = ["help", "players", "scripts", "search", "rescan", "requires", "exec", "execclient", "strict", "execfile", "require", "load", "admin", "give", "convert",
            "converts", "open", "fe", "femode", "diag", "share", "replication", "mirror", "resync", "fakeplayer", "kick", "logs", "status", "clear", "exit"]


def completer(text, index):
    typed = text.lstrip(".")
    options = ["." + c for c in COMMANDS if c.startswith(typed)]
    return options[index] if index < len(options) else None


def toggle(argument):
    return argument.lower() in ("enable", "on", "true", "1")


def handle(line):
    line = line.strip()
    if not line:
        return True
    parts = line.lstrip(".").split(None, 1)
    name, argument = parts[0].lower(), (parts[1] if len(parts) > 1 else "")

    if name == "help":
        helpText()
    elif name == "players":
        listPlayers()
    elif name in ("status", "stats"):
        statusBoard()
    elif name == "search":
        searchScripts(argument) if argument else out("Usage: .search <text>", YELLOW)
    elif name == "converts":
        for label, target, size in stats["converts"]:
            out("  %s  %.1f KB  %s" % (label, size / 1024, target), WHITE)
        out("%d conversion(s)" % len(stats["converts"]), GREEN)
    elif name == "open":
        folder = os.path.join(os.path.dirname(os.path.abspath(__file__)), "converted")
        os.makedirs(folder, exist_ok=True)
        try:
            if platform.system() == "Windows":
                os.startfile(folder)
            else:
                subprocess.run(["open" if platform.system() == "Darwin" else "xdg-open", folder])
        except Exception as error:
            out("Cannot open folder: %s" % error, RED)
    elif name == "scripts":
        printTree(argument or None)
    elif name == "rescan":
        broadcast({"type": "rescan"})
    elif name == "requires":
        for entry in requireEvents[-60:]:
            out(entry, CYAN)
        out("%d require events" % len(requireEvents), GREEN)
    elif name == "exec":
        sent = dispatch({"type": "exec", "source": argument})
        if sent:
            out("exec sent to %d client(s)" % sent, GRAY)
    elif name == "execfile":
        try:
            with open(argument.strip('"'), "r", encoding="utf-8") as handle_file:
                dispatch({"type": "exec", "source": handle_file.read()})
        except OSError as error:
            out("Cannot read file: %s" % error, RED)
    elif name == "require":
        dispatch({"type": "require", "target": argument})
    elif name in ("execclient", "client"):
        dispatch({"type": "execclient", "source": argument}) if argument else out("Usage: .execclient <lua>", YELLOW)
    elif name == "strict":
        broadcast({"type": "strict", "on": toggle(argument)})
        out("Strict server mode %s" % ("on" if toggle(argument) else "off"), GREEN)
    elif name in ("load", "admin"):
        dispatch({"type": "load", "target": argument}) if argument else out("Usage: .load <assetId|url>", YELLOW)
    elif name == "give":
        dispatch({"type": "give", "target": argument})
    elif name == "convert":
        targets = liveClients()
        if targets:
            targets[0]["cmds"].put({"type": "convert", "target": argument})
        else:
            out("No clients connected to the proxy.", YELLOW)
    elif name == "fe":
        words = argument.lower().split()
        action = words[0] if words else ""
        scope = words[1] if len(words) > 1 else None
        if action in ("disable", "disabled", "off", "false"):
            setFilteringEnabled(False, scope)
        elif action in ("enable", "enabled", "on", "true"):
            setFilteringEnabled(True)
        elif action in ("", "status"):
            out("FilteringEnabled = %s%s" % ("false" if state["feOff"] else "true", " (scope %s)" % state["feScope"] if state["feOff"] else ""), GREEN)
        else:
            out("Usage: .fe disable [all] | .fe enable | .fe status", YELLOW)
    elif name == "share":
        if not argument:
            out("Usage: .share <path>   e.g. .share Workspace.LocalMap", YELLOW)
        else:
            dispatch({"type": "share", "target": argument})
    elif name == "diag":
        sent = broadcast({"type": "diag"})
        if sent:
            out("diag asked from %d client(s)" % sent, GRAY)
    elif name == "femode":
        mode = argument.strip().lower()
        if mode not in ("convert", "mirror"):
            out("FE mode = %s. Usage: .femode convert|mirror" % state["feMode"], YELLOW)
        else:
            state["feMode"] = mode
            broadcast({"type": "femode", "mode": mode})
            out("FE mode = %s" % mode, GREEN)
    elif name == "replication":
        state["replication"] = toggle(argument)
        if not state["replication"] and state["feOff"]:
            setFilteringEnabled(True)
        broadcast({"type": "replication", "on": toggle(argument)})
        out("Replication %s" % ("enabled" if toggle(argument) else "disabled"), GREEN)
    elif name == "mirror":
        if not toggle(argument) and state["feOff"]:
            out("FilteringEnabled is off, the mirror carries it. Run .fe enable first.", YELLOW)
            return True
        broadcast({"type": "mirror", "on": toggle(argument)})
        out("Mirror %s" % ("on" if toggle(argument) else "off"), GREEN)
    elif name == "resync":
        broadcast({"type": "resync"})
    elif name == "fakeplayer":
        sub, _, rest = argument.partition(" ")
        sub = sub.lower()
        if sub in ("enable", "on", "add"):
            dispatch({"type": "fakeplayer", "action": "add", "name": rest or "FakePlayer"})
        elif sub in ("disable", "off", "clear"):
            dispatch({"type": "fakeplayer", "action": "clear"})
        elif sub == "remove":
            dispatch({"type": "fakeplayer", "action": "remove", "name": rest})
        elif sub == "chat":
            who, _, message = rest.partition(" ")
            dispatch({"type": "fakeplayer", "action": "chat", "name": who, "message": message})
        elif sub == "list":
            dispatch({"type": "fakeplayer", "action": "list"})
        else:
            out("Usage: .fakeplayer add [name] | remove <name> | chat <name> <msg> | list | clear", YELLOW)
    elif name == "kick":
        target, _, reason = argument.partition(" ")
        if not target:
            out("Usage: .kick <name> [reason]", YELLOW)
        else:
            broadcast({"type": "kick", "name": target, "reason": reason or "Kicked by server"})
    elif name == "logs":
        state["logs"] = argument.lower() != "off"
        out("Logs %s" % ("on" if state["logs"] else "off"), GREEN)
    elif name == "clear":
        os.system("cls" if platform.system() == "Windows" else "clear")
    elif name in ("exit", "quit"):
        return False
    else:
        close = difflib.get_close_matches(name, COMMANDS, n=1)
        out("Unknown command.%s Type .help" % (" Did you mean .%s?" % close[0] if close else ""), YELLOW)
    return True


def main():
    started = time.perf_counter()
    try:
        server = QuietServer((HOST, PORT), Handler)
    except OSError:
        out("Ezproxy is already running on %s:%d" % (HOST, PORT), RED)
        return
    found = findUdmux()
    address = "%s:%s" % found if found else "waiting for RobloxPlayer"
    out("Ezproxy Starting For Roblox server udmux " + address, GREEN)
    out("Virtualise Sandbox Plugins Loading...", GRAY)
    out("Virtualise Sandbox Plugins: (2) RaknetDecoder RequireMmio", GRAY)
    out("(RaknetDecoder) Loaded 7 Raknet Files", CYAN)

    server.daemon_threads = True
    threading.Thread(target=server.serve_forever, daemon=True).start()

    elapsed = (time.perf_counter() - started) * 1000
    out("(Ezproxy) Native Replication Bridge on Roblox", CYAN)
    out("(Ezproxy) Loaded in %.3fms" % elapsed, CYAN)
    out("(Ezproxy) Located at %s:%d" % (HOST, PORT), CYAN)
    out("(Ezproxy) Type .help for cmds", CYAN)

    state["prompt"] = True
    try:
        if pt:
            from prompt_toolkit.completion import WordCompleter
            session = PromptSession(history=InMemoryHistory(), completer=WordCompleter(["." + c for c in COMMANDS], ignore_case=True))
            with patch_stdout(raw=True):
                while True:
                    try:
                        line = session.prompt(PROMPT)
                    except EOFError:
                        break
                    try:
                        if not handle(line):
                            break
                    except Exception as error:
                        out("Error: %r" % error, RED)
        else:
            while True:
                try:
                    if not handle_line():
                        break
                except Exception as error:
                    out("Error: %r" % error, RED)
    except (KeyboardInterrupt, EOFError):
        pass
    server.shutdown()


def handle_line():
    state["reading"] = True
    try:
        line = input(PROMPT)
    except EOFError:
        return False
    finally:
        state["reading"] = False
    return handle(line)


if __name__ == "__main__":
    main()