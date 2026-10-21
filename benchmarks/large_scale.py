#!/usr/bin/env python3
"""Generate and measure independent declaration-sharing and resident-store axes."""
import argparse
from pathlib import Path
import tempfile

from bench import BENCHMARKS, Measurements, package


def definitions(width, carrier="A"):
    return "\n".join(rf"\definition id{i}[x: {carrier}]: {carrier} := x;" for i in range(width))


def namespace(root, width, imports, local=False):
    lines = [rf"\module Source(A: \Set) {{ {definitions(width)} }}",
             r"\inductive Unit: \Set := | unit: Unit;"]
    for i in range(imports):
        if local:
            lines.append(rf"\definition use{i}[A: \Set][x: A]: A := Source[A := A].id0 x;")
        elif i % 2:
            lines.extend([rf"\import Source[A := Unit -> Unit] \as S{i};",
                          rf"\definition use{i}[x: Unit]: Unit := S{i}.id0 (\fun (y: Unit) => y) x;"])
        else:
            lines.extend([rf"\import Source[A := Unit] \as S{i};",
                          rf"\definition use{i}: Unit := S{i}.id0 Unit::unit;"])
    return package(root, "namespaces", [], "\\module Main {\n" + "\n".join(lines) + "\n}")


def chain(root, size, width):
    previous = None
    for i in range(size):
        name = f"p{i}"
        lines = [r"\module Core {"]
        if previous:
            lines.append(rf"\import {previous}.Core[] \as D;")
        for j in range(width):
            body = rf"D.p{j}" if previous else r"\forall (P: \Prop) -> P -> P"
            lines.append(rf"\definition p{j}: \Prop := {body};")
        lines.append("}")
        entry = package(root, name, [previous] if previous else [], "\n".join(lines))
        previous = name
    return entry


def consumers(root, size, width):
    package(root, "base", [], rf"\module Core(A: \Set) {{ {definitions(width)} }}")
    names = []
    for i in range(size):
        name = f"user{i}"
        names.append(name)
        package(root, name, ["base"], r"\module Use(A: \Set) { \import base.Core[A := A] \as B; \definition id[x: A]: A := B.id0 x; }")
    (root / "ref.toml").write_text("[workspace]\npackages = [" + ", ".join(f'"{name}"' for name in names) + "]\n", encoding="utf-8")
    return root


def independent(root, size, width):
    groups = []
    for i in range(size):
        declarations = []
        for j in range(width):
            declarations.extend([
                rf"\inductive T{j}: \Set := | zero: T{j};",
                rf"\definition Carrier{j}: \Set := T{j};",
                rf"\definition id{j}[x: T{j}]: T{j} := x;",
                rf"\definition value{j}: T{j} := id{j} T{j}::zero;",
            ])
        groups.append(rf"\module G{i} {{ " + "\n".join(declarations) + " }")
    # Revisit old type aliases after the independent groups exceed the page
    # budget. Conversion must read verified bodies without checking them again.
    reads = []
    for i in range(size):
        reads.extend([
            rf"\import \root.G{i}[] \as G{i};",
            rf"\definition value{i}: G{i}.Carrier0 := G{i}.value0;",
        ])
    groups.append(r"\module ReadBack { " + "\n".join(reads) + " }")
    return package(root, "groups", [], "\n".join(groups))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=Path("target/debug/cli"))
    parser.add_argument("--axes", nargs="+", choices=["chain", "consumers", "width", "imports", "locals", "resident"],
                        default=["chain", "consumers", "width", "imports", "locals", "resident"])
    parser.add_argument("--sizes", type=int, nargs="+", default=[16, 32, 64])
    parser.add_argument("--width", type=int, default=32)
    parser.add_argument("--imports", type=int, default=32)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--memory-mib", type=int, default=3072)
    parser.add_argument("--resident-mib", type=int, default=1)
    parser.add_argument("--seconds", type=float, default=300)
    parser.add_argument("--output", type=Path, default=BENCHMARKS / "runs/large-scale-checking/scaling.json")
    args = parser.parse_args()
    if min(*args.sizes, args.width, args.imports, args.runs, args.resident_mib) < 1:
        parser.error("sizes, widths, budgets and runs must be positive")
    args.action, args.command = "large-scale", None
    args.profile_costs, args.profile_phases = None, False
    args.work_dir = BENCHMARKS / "runs/large-scale-checking/generated"
    args.cache_mib, args.batch_seconds, args.module = None, None, None
    args.output_mib, args.progress_seconds = 8, 30
    args.extra = ["--full-check"]
    measurements = Measurements(args)
    measurements.environment["REF_TYPE_GRAPH_RESIDENT_MIB"] = str(args.resident_mib)
    measurements.report.update(axes=args.axes, sizes=args.sizes, width=args.width, imports=args.imports,
                               resident_mib=args.resident_mib)
    args.work_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="axes-", dir=args.work_dir) as temporary:
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
