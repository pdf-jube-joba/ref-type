from pathlib import Path
import tempfile

from common.measurements import MeasurementOptions, Measurements
from common.sources import package


def run(args):
    measurements = Measurements(MeasurementOptions.from_namespace(args))
    measurements.report["depth"] = args.depth
    args.work_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="cache-", dir=args.work_dir) as directory:
        root = Path(directory)
        cache = root / "cache"
        leaf = package(root, "base", [], r"\module Core { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }")
        previous = "base"
        for index in range(args.depth):
            name = f"layer{index}"
            package(root, name, [previous], rf"\module Core {{ \import {previous}.Core[] \as D; \definition P: \Prop := D.P; }}")
            previous = name
        body = rf"\module Main {{ \import {previous}.Core[] \as D; \definition P: \Prop := D.P; \infer P; }}"
        entry = package(root, "app", [previous], body)
        other = package(root, "other", [previous], body)
        for label, path in [("cold", entry), ("warm", entry), ("other-consumer", other)]:
            measurements.run(label, path, cache)
        (entry / "src/root.ref").write_text(body + "\n\\module Added { \\definition Q: \\Prop := \\forall (P: \\Prop) -> P -> P; }\n")
        measurements.run("entry-edit", entry, cache)
        (leaf / "src/root.ref").write_text(r"\module Core { \definition P: \Prop := \forall (Q: \Prop) -> Q -> Q; }")
        measurements.run("dependency-edit", entry, cache)
        for branch in ("left", "right"):
            package(root, branch, ["base"], r"\module Core { \import base.Core[] \as D; \definition P: \Prop := D.P; }")
        body = r"\module Main { \import left.Core[] \as L; \import right.Core[] \as R; \definition P: \Prop := L.P; \definition Q: \Prop := R.P; }"
        entry = package(root, "diamond", ["left", "right"], body)
        measurements.run("diamond-cold", entry, cache)
        measurements.run("diamond-warm", entry, cache)
        package(root, "diamond", ["right", "left"], body)
        measurements.run("dependency-order", entry, cache)
        package(root, "independent", [], r"\module Core { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }")
        package(root, "diamond", ["independent", "right", "left"], body)
        measurements.run("unrelated-dependency", entry, cache)
    return measurements.finish()

