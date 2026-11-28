from functools import partial
from pathlib import Path
import tempfile

from common.measurements import MeasurementOptions, Measurements
from common.sources import package
from . import generators


TERMS = {
    "transport": generators.transport,
    "constructor-equations": generators.constructor_equations,
    "program-binds": generators.program_binds,
    "refinement": generators.refinement,
    "witnesses": generators.witnesses,
    "recursive-notation": generators.recursive_notation,
    "step-motive": generators.step_motive,
}
FAMILIES = [*TERMS, "focused-files"]
STRESS = {
    "transport": (96, 160),
    "constructor-equations": (128, 256),
    "program-binds": (96, 160),
    "refinement": (48, 96),
    "witnesses": (48, 96),
    "recursive-notation": (48, 96),
    "step-motive": (128, 256),
    "focused-files": (128, 256),
}


def configure(parser):
    parser.add_argument("--families", nargs="+", choices=FAMILIES, default=FAMILIES)
    parser.add_argument("--preset", choices=("quick", "stress"), default="quick")
    parser.add_argument("--sizes", type=int, nargs="+", help="override sizes for every selected family")
    parser.add_argument("--runs", type=int, default=1)


def coverage(report, module, phase):
    expected = [["sample"], ["sample", module]]
    verified = report.get("verified_modules")
    if not isinstance(verified, list) or len(verified) != len(expected) or any(
            path not in verified for path in expected):
        return f"expected verified_modules {expected}, got {verified}"
    checked = report.get("checked_modules")
    if phase == "warm":
        if checked != [] or report.get("cache", {}).get("verification_reused") is not True:
            return "expected verified cache reuse with no newly checked modules"
    else:
        required = [["sample", module]] if phase == "edit" else expected
        if any(path not in (checked or []) for path in required):
            return f"expected newly checked modules {required}, got {checked}"
        if report.get("execution", {}).get("source_steps", 0) <= 0:
            return "expected source checking"
    return None


def focused_sequence(measurements, root, size):
    entry = generators.focused_files(root, size)
    for phase in ("cold", "warm", "edit"):
        if phase == "edit":
            (entry / "src/Focus.ref").write_text(
                r"\definition choose[P: \Prop]: \Prop := P -> P;", encoding="utf-8")
        row = measurements.run(
            f"focused-files-{size}-{phase}", entry, root / "cache",
            extra=("--module", "sample.Focus", "--module-only"),
            check_coverage=partial(coverage, module="Focus", phase=phase))
        if not row["completed"]:
            break


def run(args):
    measurements = Measurements(MeasurementOptions.from_namespace(args))
    sizes = {}
    for name in args.families:
        sizes[name] = args.sizes or (STRESS[name] if args.preset == "stress" else (8, 32))
    measurements.report.update(preset=args.preset, family_sizes=sizes, runs=args.runs)
    args.work_dir.mkdir(parents=True, exist_ok=True)
    for name, values in sizes.items():
        for size in values:
            for _ in range(args.runs):
                with tempfile.TemporaryDirectory(prefix=f"{name}-", dir=args.work_dir) as temporary:
                    root = Path(temporary).resolve()
                    if name == "focused-files":
                        focused_sequence(measurements, root, size)
                    else:
                        body = TERMS[name](size)
                        entry = package(root, "sample", [], "\\module Work {\n" + body + "\n}\n")
                        measurements.run(f"{name}-{size}-off", entry,
                                         check_coverage=partial(coverage, module="Work", phase="off"))
    return measurements.finish()
