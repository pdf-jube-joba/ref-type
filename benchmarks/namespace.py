#!/usr/bin/env python3
"""Measure the current CLI and resolver sequentially, then summarize cost logs.

Build first with cargo build -p cli --locked and
cargo build -p resolve --example resolve-bench --locked.
"""
import argparse
from collections import Counter
from datetime import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import statistics
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
RUNS = Path("benchmarks/namespace-runs")
TENSOR = "tests/projects/homological-algebra"
MODULE = "homological_algebra_tests.Field.Tensor"
FORMS = "libs/geometry/differential_forms"
CASES = [
    ("tensor-plain-1", TENSOR, MODULE, "target/debug/cli", False),
    ("tensor-costs", TENSOR, MODULE, "target/debug/cli", True),
    ("tensor-plain-2", TENSOR, MODULE, "target/debug/cli", False),
    ("tensor-plain-3", TENSOR, MODULE, "target/debug/cli", False),
    ("forms-resolve", FORMS, None, "target/debug/examples/resolve-bench", True),
]


def costs(path):
    groups, counts = Counter(), Counter()
    scopes = {}
    phases = []
    sessions = []
    for line in path.read_text().splitlines():
        if match := re.fullmatch(r"cost_group=(\S+) exclusive_us=(\d+)", line):
            groups[match[1]] += int(match[2])
        elif match := re.fullmatch(r"cost_count=(\S+) value=(\d+)", line):
            counts[match[1]] += int(match[2])
        elif match := re.fullmatch(
            r"cost=(\S+) calls=(\d+) inclusive_us=(\d+) exclusive_us=(\d+) max_us=(\d+)", line
        ):
            values = scopes.setdefault(match[1], dict(calls=0, inclusive_us=0, exclusive_us=0, max_us=0))
            for key, value in zip(values, map(int, match.groups()[1:])):
                values[key] = max(values[key], value) if key == "max_us" else values[key] + value
        elif line.startswith(("phase=query.", "phase=environment.", "phase=package.", "phase=lowering.all ")):
            # Preserve phase order: nested phases overlap and RSS is process-wide.
            phases.append(line)
        elif line.startswith("cost_total "):
            sessions.append(line)
    return dict(exclusive_group_us=dict(groups), counts=dict(counts), scopes=scopes,
                phases=phases, sessions=sessions)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--summarize-only", action="store_true")
    args = parser.parse_args()
    os.chdir(ROOT)
    RUNS.mkdir(exist_ok=True)
    measurements = {}
    for name, path, module, binary, profile in CASES:
        log = RUNS / f"{name}.log"
        result = RUNS / f"{name}.json"
        environment = {k: v for k, v in os.environ.items() if not k.startswith("REF_TYPE_PROFILE_")}
        if profile:
            environment.update(REF_TYPE_PROFILE_COSTS="1", REF_TYPE_PROFILE_PHASES="1")
        command = [sys.executable, "benchmarks/check.py", path, "--binary", binary,
                   "--seconds", "600", "--memory-mib", "3584", "--log", str(log), "--result", str(result)]
        if module:
            command.extend(["--module", module])
        if not args.summarize_only:
            with tempfile.TemporaryDirectory(prefix=f"{name}-", dir=RUNS) as cache:
                if module:
                    command.extend(["--cache-dir", cache, "--cache-stats", "--batch-seconds", "600"])
                subprocess.run(command, env=environment, check=True)
        measurement = json.loads(result.read_text())
        if measurement["status"] != 0 or measurement["timeout"]:
            raise RuntimeError(f"incomplete measurement: {name}")
        if any(line.startswith("splitting ") for line in log.read_text().splitlines()):
            raise RuntimeError(f"batch splitting changed the workload: {name}")
        if module:
            measurement["cache_stats"] = [
                {key: int(value) for key, value in re.findall(r"(\w+): (\d+)", line)}
                for line in log.read_text().splitlines() if line.startswith("queries: QueryStats")
            ]
            if len(measurement["cache_stats"]) != 1 or any(
                measurement["cache_stats"][0][key] for key in ("disk_hits", "environment_hits", "package_hits", "checkpoint_hits")
            ):
                raise RuntimeError(f"expected one cold worker: {name}")
        measurement["profile_environment"] = {k: v for k, v in environment.items()
                                                if k.startswith("REF_TYPE_PROFILE_")}
        if profile:
            # Individual lowering RSS samples are large and do not attribute
            # allocation ownership. Keep aggregate timings and coarse phases.
            log.write_text("\n".join(line for line in log.read_text().splitlines()
                                     if not line.startswith("phase=lowering.definition:")) + "\n")
            measurement["profile"] = costs(log)
            if not measurement["profile"]["exclusive_group_us"]:
                raise RuntimeError(f"missing cost measurements: {name}")
        measurements[name] = measurement
    plain = [measurements[f"tensor-plain-{n}"] for n in range(1, 4)]
    profile = measurements["tensor-costs"]["profile"]
    groups = profile["exclusive_group_us"]
    accounted = sum(groups.values())
    report = {
        "date": datetime.now().astimezone().isoformat(timespec="seconds"),
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "profile": "dev, opt-level=2, debug assertions enabled",
        "rustc": subprocess.check_output(["rustc", "--version"], text=True).strip(),
        "kernel": subprocess.check_output(["uname", "-sr"], text=True).strip(),
        "cpu_model": next(line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                          if line.startswith("model name")),
        "binary_sha256": {binary: hashlib.sha256(Path(binary).read_bytes()).hexdigest()
                          for binary in sorted({case[3] for case in CASES})},
        "reproduce": "python3 benchmarks/namespace.py",
        "conditions": [
            "Sequential runs; no concurrent builds or other benchmark jobs.",
            "Each CLI run uses an empty dedicated temporary cache, including checkpoint writes; neither disk results nor batch layouts are reused.",
            "The CLI batch timeout equals the outer 600-second limit; successful runs must not split.",
            "The CLI supervisor loads sources and a worker checks them; cost groups sum completed sessions from both processes.",
            "peak_rss_kib is wait4 ru_maxrss: maximum individual-process RSS including waited descendants, not simultaneous process-tree RSS.",
            "Detailed profiling adds overhead; exclusive groups avoid nested timing double counting.",
            "Phase RSS is process-wide, not heap allocation ownership by subsystem.",
            "query.packages exclusive time also contains uninstrumented checking, analysis, checkpoint and teardown work; it is not solely disk I/O.",
            "Profiling overhead and time-based checkpoint scheduling can change the work done; group shares are not uninstrumented runtime fractions.",
            "The forms resolver run covers the whole package dependency graph, not the Tensor selection; it is not a subtraction baseline.",
            "Library partitioning, sources and CLI checkpoint behavior differ from the October 10 reports; these are not controlled before/after measurements.",
        ],
        "summary": {
            "tensor_plain_median_seconds": statistics.median(run["seconds"] for run in plain),
            "tensor_plain_seconds_range": [min(run["seconds"] for run in plain), max(run["seconds"] for run in plain)],
            "tensor_plain_cpu_seconds_range": [round(min(run["user_seconds"] + run["system_seconds"] for run in plain), 3),
                                               round(max(run["user_seconds"] + run["system_seconds"] for run in plain), 3)],
            "tensor_plain_peak_rss_kib_range": [min(run["peak_rss_kib"] for run in plain), max(run["peak_rss_kib"] for run in plain)],
            "tensor_profile_accounted_seconds": accounted / 1e6,
            "tensor_profile_exclusive_group_seconds": {key: value / 1e6 for key, value in groups.items()},
            "tensor_profile_exclusive_group_percent": {key: round(value / accounted * 100, 2) for key, value in groups.items()},
            "forms_resolve_seconds": int(re.search(r"resolve_ms=(\d+)", (RUNS / "forms-resolve.log").read_text())[1]) / 1000,
        },
        "measurements": measurements,
    }
    destination = Path("benchmarks/namespace-results.json")
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report["summary"], indent=2))


if __name__ == "__main__":
    main()
