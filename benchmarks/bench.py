#!/usr/bin/env python3
"""Measure checker workloads and analyze their logs (Linux, Python 3.11+)."""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import shlex
import signal
import sys
import tempfile
import tomllib

from log_analysis import analyze, cost_profile
from measurements import BENCHMARKS, MeasurementOptions, Measurements, save_json, target_directory
from workloads import package, packages


def cases():
    """Read the named workloads; paths are relative to benchmarks/."""
    catalog = tomllib.loads((BENCHMARKS / "cases.toml").read_text(encoding="utf-8"))
    for name, definition in catalog.items():
        if (not isinstance(definition, dict)
                or set(definition) != {"input", "target", "description", "seconds"}
                or not isinstance(definition["target"], str)
                or definition["target"] not in {"checker", "resolver"}
                or not isinstance(definition["input"], str)
                or not isinstance(definition["description"], str)
                or type(definition["seconds"]) not in (int, float)
                or not math.isfinite(definition["seconds"]) or definition["seconds"] <= 0):
            raise ValueError(f"invalid benchmark case: {name}")
        if not (BENCHMARKS / definition["input"]).exists():
            raise ValueError(f"missing benchmark input: {name}")
    return catalog


def run_paths(args):
    paths = packages(args.paths) if args.action == "libraries" else args.paths
    if not paths:
        raise ValueError("no input paths")
    mode = args.cache_mode or ("shared" if args.cache_dir or args.action == "libraries" else "off")
    if args.command and (mode != "off" or args.module is not None):
        raise ValueError("pass raw command options after --extra instead of CLI-specific options")
    measurements = Measurements(MeasurementOptions.from_namespace(args))
    args.work_dir.mkdir(parents=True, exist_ok=True)
    cache = (args.cache_dir or measurements.output.parent / "cache").resolve()
    for run in range(args.runs):
        for path in paths:
            if mode == "cold":
                with tempfile.TemporaryDirectory(prefix="cold-", dir=args.work_dir) as directory:
                    measurements.run(getattr(args, "name", str(path)), path, Path(directory))
            else:
                measurements.run(getattr(args, "name", str(path)), path, cache if mode == "shared" else None)
    return measurements.finish()


def run_cache(args):
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


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="action", required=True)
    commands.add_parser("list", help="list the named benchmark cases")
    for action, description in [("run", "repeat a selected workload"),
                                ("case", "measure a named case from cases.toml"),
                                ("libraries", "measure packages in dependency order"),
                                ("cache", "measure generated chain, diamond, and editing workloads")]:
        command = commands.add_parser(action, help=description)
        if action != "cache":
            if action == "case":
                command.add_argument("name", help="case name shown by the list command")
            else:
                command.add_argument("paths", type=Path, nargs="+")
            command.add_argument("--runs", type=int, default=1)
            command.add_argument("--cache-mode", choices=["off", "cold", "shared"])
            command.add_argument("--cache-dir", type=Path)
            command.add_argument("--command", help="raw command accepting the input path; shell-quoted arguments")
        else:
            command.set_defaults(command=None)
            command.add_argument("--depth", type=int, default=8)
        command.add_argument("--binary", type=Path, default=target_directory() / "debug/cli")
        command.add_argument("--module")
        command.add_argument("--seconds", type=float, default=None if action == "case" else 300)
        command.add_argument("--cache-mib", type=int)
        command.add_argument("--output-mib", type=int, default=8)
        command.add_argument("--progress-seconds", type=float, default=30)
        command.add_argument("--profile-costs", nargs="?", const="1")
        command.add_argument("--profile-phases", action="store_true")
        command.add_argument("--work-dir", type=Path, default=BENCHMARKS / "runs/scratch")
        command.add_argument("--output", type=Path)
        command.add_argument("--extra", nargs=argparse.REMAINDER, default=[], help="remaining checker arguments")
        command.set_defaults(function=run_cache if action == "cache" else run_paths)
    analysis = commands.add_parser("analyze", help="summarize completed or interrupted logs")
    analysis.add_argument("log", type=Path)
    analysis.add_argument("--top", type=int, default=10)
    analysis.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    if args.action == "list":
        for name, definition in cases().items():
            print(f"{name} ({definition['target']}): {definition['description']}")
        return 0
    if args.action == "analyze":
        if args.top < 1:
            parser.error("--top must be positive")
        report = analyze(args.log, args.top)
        report["profile"] = cost_profile(args.log)
        if args.output:
            save_json(args.output, report)
        else:
            print(json.dumps(report, indent=2, ensure_ascii=False))
        return 0
    if args.action == "case":
        catalog = cases()
        if args.name not in catalog:
            parser.error(f"unknown case: {args.name}; choose from {', '.join(catalog)}")
        args.case_definition = catalog[args.name]
        args.paths = [BENCHMARKS / args.case_definition["input"]]
        if args.seconds is None:
            args.seconds = args.case_definition["seconds"]
        if args.case_definition["target"] == "resolver" and args.command is None:
            args.command = shlex.join([str(target_directory() / "debug/resolve-bench")])
    if args.output is None:
        args.output = BENCHMARKS / "runs" / getattr(args, "name", args.action) / "report.json"
    if (not math.isfinite(args.seconds) or args.seconds <= 0
            or (args.cache_mib is not None and args.cache_mib < 1)
            or args.output_mib < 1 or args.progress_seconds < 0
            or not math.isfinite(args.progress_seconds)
            or getattr(args, "runs", 1) < 1 or getattr(args, "depth", 0) < 0):
        parser.error("resource limits and runs must be positive; depth and progress interval must be nonnegative")
    return args.function(args)


if __name__ == "__main__":
    def interrupt(signum, frame):
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            signal.signal(sig, signal.SIG_IGN)
        raise KeyboardInterrupt

    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, interrupt)
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
    except (OSError, ValueError) as error:
        print(f"benchmark error: {error}", file=sys.stderr)
        raise SystemExit(2)
