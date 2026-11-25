from collections import Counter, defaultdict
import re


def cost_profile(path):
    groups, counts, scopes, phases, sessions = Counter(), Counter(), {}, [], []
    with path.open(encoding="utf-8", errors="replace") as file:
        for line in file:
            line = line.rstrip("\n")
            if match := re.fullmatch(r"cost_group=(\S+) exclusive_us=(\d+)", line):
                groups[match[1]] += int(match[2])
            elif match := re.fullmatch(r"cost_count=(\S+) value=(\d+)", line):
                counts[match[1]] += int(match[2])
            elif match := re.fullmatch(r"cost=(\S+) calls=(\d+) inclusive_us=(\d+) exclusive_us=(\d+) max_us=(\d+)", line):
                values = scopes.setdefault(match[1], dict(calls=0, inclusive_us=0, exclusive_us=0, max_us=0))
                for key, value in zip(values, map(int, match.groups()[1:])):
                    values[key] = max(values[key], value) if key == "max_us" else values[key] + value
            elif line.startswith("phase="):
                if not line.startswith("phase=lowering.definition:"):
                    phases.append(line)
            elif line.startswith("cost_total "):
                sessions.append(line)
    return dict(exclusive_group_us=dict(groups), counts=dict(counts), scopes=scopes,
                phases=phases, sessions=sessions)



FINISHED = re.compile(r"\s*([\d.]+)(ns|µs|ms|s)\s+(.+) \(excluding diagnostics\)$")
SCALE = {"ns": 1e-9, "µs": 1e-6, "ms": 1e-3, "s": 1}


def analyze(path, top):
    declarations = []
    modules = {}
    stack = []
    unmatched = []
    phase_seconds = Counter()
    by_kind = defaultdict(lambda: {"calls": 0, "exclusive_seconds": 0.0})
    phase = None
    phase_start = 0.0
    last_progress = None
    last_declaration = None
    milestones = []
    lines = 0
    with path.open() as source:
        for lines, raw in enumerate(source, 1):
            line = raw.rstrip("\n")
            if line.startswith("checking "):
                stack.append({"label": line[9:], "start_line": lines, "children_seconds": 0.0})
            elif match := FINISHED.fullmatch(line):
                seconds = float(match[1]) * SCALE[match[2]]
                label = match[3]
                entry = {"label": label, "seconds": seconds, "end_line": lines}
                if stack and stack[-1]["label"] == label:
                    frame = stack.pop()
                    entry["start_line"] = frame["start_line"]
                    entry["exclusive_seconds"] = max(0.0, seconds - frame["children_seconds"])
                    if stack:
                        stack[-1]["children_seconds"] += seconds
                    kind = label.rsplit(": ", 1)[-1].split(" ", 1)[0]
                    by_kind[kind]["calls"] += 1
                    by_kind[kind]["exclusive_seconds"] += entry["exclusive_seconds"]
                else:
                    unmatched.append({"line": lines, "label": label})
                declarations.append(entry)
                last_declaration = entry
            elif line.startswith("progress "):
                event = dict(re.findall(r"(\w+)=(\S+)", line))
                event["line"] = lines
                elapsed = float(event["elapsed_seconds"])
                if "phase" in event:
                    if phase is not None:
                        phase_seconds[phase] += elapsed - phase_start
                    phase = event["phase"]
                    phase_start = elapsed
                if event.get("event") == "complete" and "module_seconds" in event:
                    modules[event["module"]] = {
                        "module": event["module"], "seconds_at_completion": float(event["module_seconds"]),
                        "elapsed_seconds": elapsed, "line": lines,
                    }
                    package_completed = event.get("package_completed", "0/0")
                    done = int(package_completed.split("/")[0])
                    if done and done % 50 == 0:
                        milestones.append({"package": event["module"].split(".")[0],
                                           "completed": package_completed, "elapsed_seconds": elapsed})
                last_progress = event
    if last_progress and phase is not None:
        phase_seconds[phase] += float(last_progress["elapsed_seconds"]) - phase_start
    return {
        "log": str(path), "lines": lines,
        "completed_declarations": len(declarations), "completed_modules": len(modules),
        "last_progress": last_progress, "last_completed_declaration": last_declaration,
        "unfinished_declarations": stack, "unmatched_completions": unmatched,
        "phase_seconds_through_last_progress": dict(phase_seconds),
        "declaration_kinds": dict(by_kind),
        "slowest_declarations": sorted(declarations, key=lambda x: x["seconds"], reverse=True)[:top],
        "slowest_completed_modules": sorted(modules.values(), key=lambda x: x["seconds_at_completion"], reverse=True)[:top],
        "package_milestones": milestones,
        "notes": ["Declaration durations exclude diagnostic time; nested calls are subtracted in exclusive_seconds.",
                  "Module durations are provisional at completion; later analysis and cache writes may add time.",
                  "The final phase is measured only through the last progress timestamp, not process exit.",
                  "This log alone cannot attribute an interruption to OOM, terminal closure, or a signal."],
    }
