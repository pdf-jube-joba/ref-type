#!/usr/bin/env python3
"""Count progress events in complete or interrupted bench.py measurements."""
from collections import Counter, defaultdict
import json
from pathlib import Path
import re
import sys


def summarize(log):
    phases = Counter()
    checked = Counter()
    skipped = Counter()
    check_times = defaultdict(list)
    phase = None
    previous = 0.0
    last = None
    loading_events = 0
    for line in Path(log).read_text(errors="replace").splitlines():
        if not line.startswith("progress "):
            continue
        event = dict(re.findall(r"(\w+)=(\S+)", line))
        now = float(event["elapsed_seconds"])
        if phase:
            phases[phase] += now - previous
        if "phase" in event:
            phase = event["phase"]
            loading_events += phase == "Loading"
        if event.get("event") == "complete":
            module = event["module"]
            if event["action"] == "Check":
                checked[module] += 1
                check_times[module].append(now)
            elif event["action"] == "Skip":
                skipped[module] += 1
        previous = now
        last = event
    return {
        "last_progress": last,
        "phase_seconds_through_last_progress": {
            key: round(value, 3) for key, value in phases.items()
        },
        "loading_phase_events": loading_events,
        "check_events": checked.total(),
        "unique_checked_modules": len(checked),
        "repeated_check_events": checked.total() - len(checked),
        "skip_events": skipped.total(),
        "unique_checked_by_package": dict(Counter(name.split(".")[0] for name in checked)),
        "most_repeated_modules": [
            {"module": name, "check_events": count, "elapsed_seconds": check_times[name]}
            for name, count in checked.most_common(10)
        ],
        "notes": [
            "Check events include work from workers later aborted by a resource limit.",
            "Counts measure progress events, not CPU time or a final verification verdict.",
            "Phases are disjoint intervals through the final progress timestamp; the remaining tail is unassigned.",
        ],
    }


if __name__ == "__main__":
    report = json.loads(Path(sys.argv[1]).read_text())
    print(json.dumps([
        {"log": row["log"], **summarize(row["log"])}
        for row in report["measurements"]
    ], ensure_ascii=False, indent=2))
