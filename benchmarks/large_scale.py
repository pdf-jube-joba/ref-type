#!/usr/bin/env python3
"""Generate and measure independent declaration-sharing and resident-store axes."""
import argparse
from pathlib import Path
import tempfile

from measurements import BENCHMARKS, MeasurementOptions, Measurements, target_directory
from workloads import chain, consumers, independent, namespace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=target_directory() / "debug/cli")
    parser.add_argument("--axes", nargs="+", choices=["chain", "consumers", "width", "imports", "locals", "resident"],
                        default=["chain", "consumers", "width", "imports", "locals", "resident"])
    parser.add_argument("--sizes", type=int, nargs="+", default=[16, 32, 64])
    parser.add_argument("--width", type=int, default=32)
    parser.add_argument("--imports", type=int, default=32)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--resident-mib", type=int, default=1)
    parser.add_argument("--seconds", type=float, default=300)
    parser.add_argument("--output", type=Path, default=BENCHMARKS / "runs/large-scale-checking/scaling.json")
    args = parser.parse_args()
    if min(*args.sizes, args.width, args.imports, args.runs, args.resident_mib) < 1:
        parser.error("sizes, widths, budgets and runs must be positive")
    work_dir = BENCHMARKS / "runs/scratch"
    measurements = Measurements(MeasurementOptions(
        output=args.output, binary=args.binary, action="large-scale",
        seconds=args.seconds, extra=("--full-check",),
    ))
    measurements.environment["REF_TYPE_GRAPH_RESIDENT_MIB"] = str(args.resident_mib)
    measurements.report.update(axes=args.axes, sizes=args.sizes, width=args.width, imports=args.imports,
                               resident_mib=args.resident_mib)
    work_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="axes-", dir=work_dir) as temporary:
        root = Path(temporary)
        for axis in args.axes:
            for size in args.sizes:
                directory = root / f"{axis}-{size}"
                if axis == "chain":
                    entry = chain(directory, size, args.width)
                elif axis == "consumers":
                    entry = consumers(directory, size, args.width)
                elif axis == "resident":
                    entry = independent(directory, size, args.width)
                else:
                    entry = namespace(directory, size if axis == "width" else args.width,
                                      args.imports if axis == "width" else size, axis == "locals")
                for run in range(args.runs):
                    with tempfile.TemporaryDirectory(prefix="cache-", dir=root) as cache:
                        measurements.run(f"{axis}-{size}", entry, Path(cache))
    return measurements.finish()


if __name__ == "__main__":
    raise SystemExit(main())
