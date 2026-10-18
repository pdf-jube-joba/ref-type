#!/usr/bin/env python3
"""Measure fixed-size packages along dependency chains of increasing depth."""
import argparse
from pathlib import Path
import tempfile

from bench import BENCHMARKS, Measurements, package


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=Path("target/debug/cli"))
    parser.add_argument("--depths", type=int, nargs="+", default=[8, 16, 32, 64])
    parser.add_argument("--width", type=int, default=16)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--seconds", type=float, default=180)
    parser.add_argument("--memory-mib", type=int, default=3072)
    parser.add_argument("--output", type=Path, default=BENCHMARKS / "runs/scaling/report.json")
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    if min(*args.depths, args.width, args.runs) < 1:
        parser.error("depths, width and runs must be positive")
    args.action = "scaling"
    args.command = None
    args.profile_costs = None
    args.profile_phases = False
    args.work_dir = BENCHMARKS / "runs/scratch"
    args.cache_mib = 8192
    args.output_mib = 8
    args.progress_seconds = 30
    args.batch_seconds = None
    args.module = None
    args.extra = ["--full-check"] if args.force else []
    measurements = Measurements(args)
    measurements.report.update(depths=args.depths, width=args.width, forced=args.force)
    args.work_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="scaling-", dir=args.work_dir) as directory:
        root = Path(directory)
        for depth in args.depths:
            previous = None
            for index in range(depth):
                name = f"p{index}"
                lines = [r"\module Core {"]
                if previous is not None:
                    lines.append(rf"\import {previous}.Core[] \as D;")
                for item in range(args.width):
                    body = rf"D.p{item}" if previous else r"\forall (P: \Prop) -> P -> P"
                    lines.append(rf"\definition p{item}: \Prop := {body};")
                lines.append("}")
                entry = package(root / f"depth-{depth}", name,
                                [previous] if previous else [], "\n".join(lines) + "\n")
                previous = name
            for run in range(args.runs):
                with tempfile.TemporaryDirectory(prefix="cache-", dir=root) as cache:
                    measurements.run(f"depth-{depth}", entry, Path(cache))
    return measurements.finish()


if __name__ == "__main__":
    raise SystemExit(main())
