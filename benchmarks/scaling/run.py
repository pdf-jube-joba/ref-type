"""Generate and measure independent declaration-sharing and resident-store axes."""
from pathlib import Path
import tempfile

from common.measurements import MeasurementOptions, Measurements
from . import recovery
from .generators import chain, checkpoint_disk, consumers, independent, layered, namespace


DEFAULT_AXES = ["chain", "consumers", "width", "imports", "locals", "resident"]
WORKSPACE_AXES = ["checkpoint-disk", "layered"]


def configure(parser):
    parser.add_argument("--axes", nargs="+", choices=DEFAULT_AXES + WORKSPACE_AXES + ["recovery"], default=DEFAULT_AXES)
    parser.add_argument("--sizes", type=int, nargs="+", default=[16, 32, 64])
    parser.add_argument("--width", type=int, default=32)
    parser.add_argument("--imports", type=int, default=32)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--resident-mib", type=int, default=1)


def run(args):
    options = MeasurementOptions.from_namespace(args)
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
                if axis == "recovery":
                    recovery.run(measurements, directory, size, args.width, args.runs)
                    continue
                if axis == "chain":
                    entry = chain(directory, size, args.width)
                elif axis == "consumers":
                    entry = consumers(directory, size, args.width)
                elif axis == "resident":
                    entry = independent(directory, size, args.width)
                elif axis == "checkpoint-disk":
                    entry = checkpoint_disk(directory, size, args.width)
                elif axis == "layered":
                    entry = layered(directory, size, args.width)
                else:
                    entry = namespace(directory, size if axis == "width" else args.width,
                                      args.imports if axis == "width" else size, axis == "locals")
                workspace = axis in WORKSPACE_AXES
                for run in range(args.runs):
                    with tempfile.TemporaryDirectory(prefix="cache-", dir=root) as cache:
                        measurements.run(f"{axis}-{size}", entry, Path(cache),
                                         extra=() if workspace else ("--full-check",),
                                         sample_cache=workspace)
    return measurements.finish()
