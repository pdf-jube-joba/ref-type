"""Generate and measure independent declaration-sharing and resident-store axes."""
from pathlib import Path
import tempfile

from common.measurements import MeasurementOptions, Measurements
from .generators import chain, consumers, independent, namespace


def configure(parser):
    parser.add_argument("--axes", nargs="+", choices=["chain", "consumers", "width", "imports", "locals", "resident"],
                        default=["chain", "consumers", "width", "imports", "locals", "resident"])
    parser.add_argument("--sizes", type=int, nargs="+", default=[16, 32, 64])
    parser.add_argument("--width", type=int, default=32)
    parser.add_argument("--imports", type=int, default=32)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--resident-mib", type=int, default=1)


def run(args):
    options = MeasurementOptions.from_namespace(args)
    options.extra = ("--full-check", *options.extra)
    measurements = Measurements(options)
    measurements.environment["REF_TYPE_GRAPH_RESIDENT_MIB"] = str(args.resident_mib)
    measurements.report.update(axes=args.axes, sizes=args.sizes, width=args.width, imports=args.imports,
                               resident_mib=args.resident_mib)
    args.work_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="scaling-", dir=args.work_dir) as temporary:
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
