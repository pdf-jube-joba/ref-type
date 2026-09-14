#!/usr/bin/env python3
"""Repeat a saved comparison using its exact binaries, inputs and CPU."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import runpy
import statistics
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("experiment", type=Path)
parser.add_argument("output", type=Path)
parser.add_argument("--filter", required=True)
parser.add_argument("--samples", type=int, default=15)
parser.add_argument("--sample-ms", type=int, default=200)
parser.add_argument("--rounds", type=int, default=4)
args = parser.parse_args()
source = args.experiment.resolve()
destination = args.output.resolve()
destination.mkdir(parents=True, exist_ok=False)
metadata = json.loads((source / "experiment.json").read_text())
runner = runpy.run_path(str(source / "runner.py"))
for name in ["before", "after"]:
    assert hashlib.sha256((source / "bin" / name).read_bytes()).hexdigest() == metadata["binary_sha256"][name]
    assert runner["fingerprint"](source / name / "src") == metadata["source_sha256"][name]
    for relative, digest in metadata["inputs_sha256"].items():
        assert runner["fingerprint"](source / name / relative) == digest
os.sched_setaffinity(0, {metadata["measurement_cpu"]})
env = os.environ.copy()
env.update(LC_ALL="C", GIT_CEILING_DIRECTORIES=str(source))
metadata["replay_of"] = str(source)
metadata["settings"] = dict(filter=args.filter, samples=args.samples,
                            sample_ms=args.sample_ms, warmup_ms=1000, rounds=args.rounds)
metadata["runs"] = []
metadata["replay_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
results = {"before": {}, "after": {}}
for index in range(args.rounds):
    order = ["before", "after"] if index % 2 == 0 else ["after", "before"]
    for name in order:
        label = f"{name}-{index + 1}"
        invocation = [str(source / "bin" / name), "--filter", args.filter,
                      "--samples", str(args.samples), "--sample-ms", str(args.sample_ms),
                      "--warmup-ms", "1000", "--output-dir", str(destination),
                      "--save-baseline", label]
        print(f"Measuring {label} ...", flush=True)
        subprocess.run(invocation, cwd=source / name, env=env, check=True)
        path = destination / f"{label}.tsv"
        assert path.read_text().rstrip().endswith("# complete")
        metadata["runs"].append(dict(label=label, command=invocation))
        (destination / "experiment.json").write_text(json.dumps(metadata, indent=2) + "\n")
        for case, samples in runner["read_samples"](path).items():
            results[name].setdefault(case, []).extend(samples)
assert results["before"].keys() == results["after"].keys()
lines = ["case\tbefore_ms\tafter_ms\tchange_percent\tbefore_cv_percent\tafter_cv_percent"]
for case, old in results["before"].items():
    new = results["after"][case]
    left, right = statistics.median(old), statistics.median(new)
    old_cv = 100 * statistics.stdev(old) / statistics.mean(old)
    new_cv = 100 * statistics.stdev(new) / statistics.mean(new)
    lines.append(f"{case}\t{left / 1e6:.6f}\t{right / 1e6:.6f}\t{100 * (right / left - 1):+.2f}\t{old_cv:.2f}\t{new_cv:.2f}")
summary = "\n".join(lines) + "\n"
(destination / "summary.tsv").write_text(summary)
print(summary, end="")
