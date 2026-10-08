#!/usr/bin/env python3
"""Measure uncached library checks in fresh CLI processes (Linux, Python stdlib)."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import time

LIBRARIES = (
    "std", "algebra", "real", "complex", "linear_algebra", "topology", "calculus",
    "integration", "category", "topological_algebra", "algebraic_topology",
)


def parse_costs(log):
    costs = {}
    groups = {}
    counters = {}
    total = None
    for line in log.splitlines():
        if match := re.fullmatch(r"cost=(\S+) calls=(\d+) inclusive_us=(\d+) exclusive_us=(\d+) max_us=(\d+)", line):
            costs[match[1]] = dict(zip(
                ("calls", "inclusive_us", "exclusive_us", "max_us"),
                map(int, match.groups()[1:]),
            ))
        elif match := re.fullmatch(r"cost_group=(\S+) exclusive_us=(\d+)", line):
            groups[match[1]] = int(match[2])
        elif match := re.fullmatch(r"cost_count=(\S+) value=(\d+)", line):
            counters[match[1]] = int(match[2])
        elif match := re.fullmatch(r"cost_total elapsed_us=(\d+) accounted_us=(\d+) unaccounted_us=(\d+)", line):
            total = dict(zip(
                ("elapsed_us", "accounted_us", "unaccounted_us"), map(int, match.groups()),
            ))
    if not costs or total is None:
        raise ValueError("Missing cost profile in CLI log")
    return {"costs": costs, "cost_groups_us": groups, "cost_counts": counters, "cost_total": total}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=Path("target/debug/cli"))
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--libraries", nargs="+", choices=LIBRARIES, default=LIBRARIES)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--profile-costs", nargs="?", const="1", help="Collect nested phase costs, optionally selecting label prefixes")
    parser.add_argument("--profile-phases", action="store_true", help="Collect query phase timings")
    parser.add_argument("--no-progress", action="store_true", help="Disable module progress clocks and logs")
    args = parser.parse_args()
    if platform.system() != "Linux" or args.runs < 1:
        parser.error("Linux and a positive --runs value are required")
    root = args.root.resolve()
    binary = args.binary.resolve()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    logs = args.output.parent / (args.output.stem + "-logs")
    logs.mkdir(exist_ok=True)
    inputs = hashlib.sha256()
    for path in sorted((root / "libs").rglob("*")):
        if path.suffix == ".ref" or path.name == "ref.toml":
            inputs.update(str(path.relative_to(root)).encode() + b"\0")
            inputs.update(path.read_bytes() + b"\0")
    environment = {k: v for k, v in os.environ.items() if not k.startswith("REF_TYPE_PROFILE")}
    if args.profile_costs:
        environment["REF_TYPE_PROFILE_COSTS"] = args.profile_costs
    if args.profile_phases:
        environment["REF_TYPE_PROFILE_PHASES"] = "1"
    result = {
        "platform": platform.platform(),
        "binary": str(binary),
        "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "library_sources_sha256": inputs.hexdigest(),
        "flags": ["--no-cache", "--diagnostics", "compact"],
        "runs": args.runs,
        "profile_costs": args.profile_costs,
        "profile_phases": args.profile_phases,
        "measurements": [],
    }
    if args.no_progress:
        result["flags"].append("--no-progress")
    for run in range(1, args.runs + 1):
        for library in args.libraries:
            log = logs / f"{run}-{library}.log"
            command = [str(binary), f"libs/{library}", *result["flags"]]
            start = time.perf_counter()
            with log.open("w") as output:
                child = subprocess.Popen(command, cwd=root, env=environment,
                                         stdout=output, stderr=subprocess.STDOUT)
                try:
                    _, status, usage = os.wait4(child.pid, 0)
                    child.returncode = os.waitstatus_to_exitcode(status)
                except BaseException:
                    child.terminate()
                    child.wait()
                    raise
            row = {
                "run": run, "library": library,
                "seconds": round(time.perf_counter() - start, 4),
                "user_seconds": usage.ru_utime, "system_seconds": usage.ru_stime,
                "maxrss_kib": usage.ru_maxrss, "exit": child.returncode,
            }
            if args.profile_costs and child.returncode == 0:
                row.update(parse_costs(log.read_text()))
            if args.profile_phases and child.returncode == 0:
                phases = {}
                lines = []
                for line in log.read_text().splitlines():
                    if match := re.fullmatch(r"phase=(query\.\S+) elapsed_us=(\d+) .*", line):
                        phases[match[1]] = phases.get(match[1], 0) + int(match[2])
                        lines.append(line)
                if "query.resolve" not in phases:
                    raise ValueError(f"Missing resolver phase in {log}")
                row["query_phases_us"] = phases
                if not args.profile_costs:
                    log.write_text("\n".join(lines) + "\n")
            result["measurements"].append(row)
            args.output.write_text(json.dumps(result, indent=2) + "\n")
            print(json.dumps({k: v for k, v in row.items() if not k.startswith("cost") and k != "query_phases_us"}), flush=True)
            if child.returncode:
                raise SystemExit(f"Check failed; see {log}")
    for library in args.libraries:
        rows = [row for row in result["measurements"] if row["library"] == library]
        seconds = [row["seconds"] for row in rows]
        print(f"{library}: median {statistics.median(seconds):.3f}s "
              f"({min(seconds):.3f}–{max(seconds):.3f}s), "
              f"peak {max(row['maxrss_kib'] for row in rows) / 1024:.1f} MiB")


if __name__ == "__main__":
    main()
