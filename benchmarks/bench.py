#!/usr/bin/env python3
"""Measure checker workloads and analyze their logs (Linux, Python 3.11+)."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
import math
import os
from pathlib import Path
import re
import resource
import shlex
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
BENCHMARKS = Path(__file__).resolve().parent


def cases():
    """Read the named workloads; paths are relative to benchmarks/."""
    catalog = tomllib.loads((BENCHMARKS / "cases.toml").read_text(encoding="utf-8"))
    for name, definition in catalog.items():
        if (not isinstance(definition, dict)
                or set(definition) != {"input", "target", "description", "seconds", "memory_mib"}
                or not isinstance(definition["target"], str)
                or definition["target"] not in {"checker", "resolver"}
                or not isinstance(definition["input"], str)
                or not isinstance(definition["description"], str)
                or type(definition["seconds"]) not in (int, float)
                or not math.isfinite(definition["seconds"]) or definition["seconds"] <= 0
                or type(definition["memory_mib"]) is not int or definition["memory_mib"] < 1):
            raise ValueError(f"invalid benchmark case: {name}")
        if not (BENCHMARKS / definition["input"]).exists():
            raise ValueError(f"missing benchmark input: {name}")
    return catalog


def save_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                     prefix=path.name + ".", suffix=".tmp", delete=False) as file:
        temporary = Path(file.name)
        try:
            json.dump(value, file, indent=2, ensure_ascii=False)
            file.write("\n")
            file.close()
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)


def file_digest(path):
    with path.open("rb") as file:
        return hashlib.file_digest(file, "sha256").hexdigest()


def packages(paths):
    """List explicit packages or workspace members in dependency order."""
    ordered, visited, visiting = [], set(), set()

    def visit(path):
        path = path.resolve()
        if path in visiting:
            raise ValueError(f"cyclic package dependency: {path}")
        if path in visited:
            return
        visiting.add(path)
        manifest = tomllib.loads((path / "ref.toml").read_text(encoding="utf-8"))
        if "package" in manifest:
            for dependency in manifest.get("dependencies", {}).values():
                visit(path / dependency["path"])
            ordered.append(path)
        for member in manifest.get("workspace", {}).get("packages", []):
            member = (path / member).resolve()
            if member != path:
                visit(member)
        visiting.remove(path)
        visited.add(path)

    for path in paths:
        visit(path)
    return ordered


def source_digest(path):
    roots = packages([path]) if path.is_dir() and (path / "ref.toml").exists() else [path.parent]
    files = set()
    for root in roots:
        for directory, children, names in os.walk(root):
            children[:] = [name for name in children if name != "refcache"]
            files.update(Path(directory) / name for name in names
                         if name.endswith(".ref") or name == "ref.toml")
    digest = hashlib.sha256()
    for file in sorted(files):
        digest.update(str(file).encode() + b"\0" + file.read_bytes() + b"\0")
    return digest.hexdigest()


def directory_bytes(directory):
    total = 0
    if directory is not None:
        for path in directory.rglob("*"):
            try:
                if path.is_file():
                    total += path.stat().st_size
            except FileNotFoundError:
                pass  # Atomic publication or collection can remove a scanned file.
    return total


def tail(path, size=65536):
    with path.open("rb") as file:
        file.seek(max(0, path.stat().st_size - size))
        return file.read(size).decode("utf-8", errors="replace")


def cost_profile(path):
    groups, counts, scopes, phases, sessions = Counter(), Counter(), {}, [], []
    with path.open(encoding="utf-8", errors="replace") as file:
        for line in file:
            line = line.rstrip("\n")
            if match := re.fullmatch(r"cost_group=(\S+) exclusive_us=(\d+)", line):
                groups[match[1]] += int(match[2])
            elif match := re.fullmatch(r"cost_count=(\S+) value=(\d+)", line):
                counts[match[1]] += int(match[2])
            elif match := re.fullmatch(r"cost=(\S+) calls=(\d+) inclusive_us=(\d+) exclusive_us=(\d+) max_us=(\d+)", line):
                values = scopes.setdefault(match[1], dict(calls=0, inclusive_us=0, exclusive_us=0, max_us=0))
                for key, value in zip(values, map(int, match.groups()[1:])):
                    values[key] = max(values[key], value) if key == "max_us" else values[key] + value
            elif line.startswith("phase="):
                if not line.startswith("phase=lowering.definition:"):
                    phases.append(line)
            elif line.startswith("cost_total "):
                sessions.append(line)
    return dict(exclusive_group_us=dict(groups), counts=dict(counts), scopes=scopes,
                phases=phases, sessions=sessions)


def measure(command, log, *, seconds, memory_mib, environment=None,
            progress_seconds=0, checkpoint=False, output_mib=8):
    """Run directly, retain wait4 resource usage, and stop through the supervisor."""
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (memory_mib * 2**20,) * 2)
        cpu = math.ceil(seconds)
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 1))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    def reap(block=False):
        waited, status, usage = os.wait4(child.pid, 0 if block else os.WNOHANG)
        if waited:
            child.returncode = os.waitstatus_to_exitcode(status)
            return usage
        return None

    def send(sig):
        try:
            os.killpg(child.pid, sig)
        except ProcessLookupError:
            pass

    def stop():
        send(signal.SIGTERM)
        deadline = time.monotonic() + 2
        while time.monotonic() < deadline:
            if usage := reap():
                return usage
            time.sleep(.02)
        send(signal.SIGKILL)
        return reap(True)

    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    next_progress = started + progress_seconds
    reason = None
    with log.open("wb") as output:
        child = subprocess.Popen(command, cwd=ROOT, env=environment, stdout=output, stderr=output,
                                 stdin=subprocess.DEVNULL, start_new_session=True, preexec_fn=limits)
        try:
            while (usage := reap()) is None:
                now = time.monotonic()
                if now - started >= seconds:
                    reason = "time_limit"
                elif log.stat().st_size > output_mib * 2**20:
                    reason = "output_limit"
                elif checkpoint and "event=checkpoint-saved" in tail(log):
                    reason = "checkpoint"
                if reason:
                    usage = stop()
                    break
                if progress_seconds > 0 and now >= next_progress:
                    print(f"  running {now - started:.0f}s: {log}", file=sys.stderr, flush=True)
                    next_progress = now + progress_seconds
                time.sleep(.02)
        except KeyboardInterrupt:
            reason = "interrupted"
            usage = stop()
        except BaseException:
            stop()
            raise
    if reason is None and (child.returncode in (-signal.SIGKILL, -signal.SIGXCPU)
                           or child.returncode != 0 and "memory allocation of" in tail(log)):
        reason = "resource_limit"
    return dict(command=command, exit=child.returncode, seconds=round(time.monotonic() - started, 3),
                user_seconds=round(usage.ru_utime, 3), system_seconds=round(usage.ru_stime, 3),
                peak_rss_kib=usage.ru_maxrss, stopped_by=reason, log=str(log),
                profile=cost_profile(log))


class Measurements:
    def __init__(self, args):
        self.args = args
        self.output = args.output.resolve()
        self.logs = self.output.parent / (self.output.stem + "-logs")
        self.command = shlex.split(args.command) if args.command else [str(args.binary.resolve())]
        if not self.command or not (executable := shutil.which(self.command[0])):
            raise ValueError("checker command does not exist; build or specify --binary/--command")
        self.command[0] = str(Path(executable).resolve())
        self.binary_digest = file_digest(Path(self.command[0]))
        self.command_digests = {str(Path(token).resolve()): file_digest(Path(token))
                                for token in self.command if Path(token).is_file()}
        self.environment = os.environ.copy()
        if args.profile_costs is not None:
            self.environment["REF_TYPE_PROFILE_COSTS"] = args.profile_costs
        if args.profile_phases:
            self.environment["REF_TYPE_PROFILE_PHASES"] = "1"
        self.report = dict(version=1, action=args.action,
                           case_definition=getattr(args, "case_definition", None),
                           binary_sha256=self.binary_digest,
                           command_sha256=self.command_digests,
                           memory_mib=args.memory_mib, seconds_per_run=args.seconds,
                           profile_environment={k: v for k, v in self.environment.items()
                                                if k.startswith("REF_TYPE_PROFILE_")},
                           measurements=[], complete=False)
        self.save()

    def save(self):
        rows = self.report["measurements"]
        summary = {}
        for label in dict.fromkeys(row["case"] for row in rows):
            successful = [row for row in rows if row["case"] == label and row["completed"]]
            if successful:
                summary[label] = dict(runs=len(successful),
                                      median_seconds=statistics.median(row["seconds"] for row in successful),
                                      peak_rss_kib=max(row["peak_rss_kib"] for row in successful))
        self.report["summary"] = summary
        save_json(self.output, self.report)

    def run(self, label, path, cache=None, extra=(), checkpoint=False):
        path = path.resolve()
        index = len(self.report["measurements"])
        basename = f"{index:03}-" + re.sub(r"[^\w.-]+", "-", label)
        log = self.logs / (basename + ".log")
        checker_report = self.logs / (basename + ".checker.json")
        command = [*self.command, str(path)]
        if not self.args.command:
            command += ["--diagnostics", "compact", "--no-progress", "--memory-mib", str(self.args.memory_mib),
                        "--cache-budget-mib", str(self.args.cache_mib), "--report-json", str(checker_report)]
            command += ["--cache-dir", str(cache)] if cache is not None else ["--no-cache"]
            if self.args.module:
                command += ["--module", self.args.module]
            if self.args.batch_seconds is not None:
                command += ["--batch-seconds", str(self.args.batch_seconds)]
        command += [*extra, *self.args.extra]
        environment = self.environment.copy()
        if checkpoint:
            environment["REF_TYPE_PROFILE_PROGRESS"] = "1"
        before = source_digest(path)
        row = measure(command, log, seconds=self.args.seconds, memory_mib=self.args.memory_mib,
                      environment=environment, progress_seconds=self.args.progress_seconds,
                      checkpoint=checkpoint, output_mib=self.args.output_mib)
        try:
            unchanged = source_digest(path) == before
        except (OSError, ValueError):
            unchanged = False
        row.update(case=label, path=str(path), sources_sha256=before,
                   sources_unchanged=unchanged, cache_bytes=directory_bytes(cache))
        if not self.args.command:
            try:
                row["checker"] = json.loads(checker_report.read_text(encoding="utf-8"))
            except (OSError, ValueError):
                row["checker"] = None
        row["completed"] = (row["exit"] == 0 and row["stopped_by"] is None and row["sources_unchanged"]
                            and (self.args.command is not None or isinstance(row["checker"], dict)
                                 and row["checker"].get("version") == 1
                                 and row["checker"].get("outcome") == "accepted"))
        self.report["measurements"].append(row)
        self.save()
        print(f"{label}: {row['seconds']:.3f}s, {row['peak_rss_kib']} KiB, exit {row['exit']}", flush=True)
        if row["stopped_by"] == "interrupted":
            raise KeyboardInterrupt
        return row

    def finish(self):
        rows = self.report["measurements"]
        self.report["binary_unchanged"] = all(Path(path).is_file() and file_digest(Path(path)) == digest
                                              for path, digest in self.command_digests.items())
        self.report["complete"] = (bool(rows) and self.report["binary_unchanged"]
                                   and all(row["completed"] or row["stopped_by"] == "checkpoint" for row in rows))
        self.save()
        print(f"complete={self.report['complete']}; report: {self.output}")
        return 0 if self.report["complete"] else 1


def run_paths(args):
    paths = packages(args.paths or [ROOT / "libs"]) if args.action == "libraries" else args.paths
    if not paths:
        raise ValueError("no input paths")
    mode = args.cache_mode or ("shared" if args.cache_dir or args.action == "libraries" else "off")
    if args.command and (mode != "off" or args.module is not None or args.batch_seconds is not None):
        raise ValueError("pass raw command options after --extra instead of CLI-specific options")
    measurements = Measurements(args)
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


def package(root, name, dependencies, body):
    path = root / name
    (path / "src").mkdir(parents=True, exist_ok=True)
    manifest = f'[package]\nname = "{name}"\n[dependencies]\n'
    manifest += "".join(f'{dep} = {{path = "../{dep}"}}\n' for dep in dependencies)
    (path / "ref.toml").write_text(manifest, encoding="utf-8")
    (path / "src/root.ref").write_text(body, encoding="utf-8")
    return path


def run_cache(args):
    measurements = Measurements(args)
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
        if args.checkpoint:
            interrupted = package(root, "interrupted", [previous], "\n".join(
                rf"\module M{index} {{ \import {previous}.Core[] \as D; \definition P: \Prop := D.P; }}"
                for index in range(160)))
            cache = root / "resume-cache"
            row = measurements.run("interruption", interrupted, cache, ["--checkpoint-seconds", "0"], checkpoint=True)
            if row["stopped_by"] != "checkpoint":
                raise ValueError("checker did not report a checkpoint before completion or its resource limit")
            measurements.run("resume", interrupted, cache, ["--checkpoint-seconds", "0"])
            measurements.run("resume-warm", interrupted, cache)
    return measurements.finish()



FINISHED = re.compile(r"\s*([\d.]+)(ns|µs|ms|s)\s+(.+) \(excluding diagnostics\)$")
SCALE = {"ns": 1e-9, "µs": 1e-6, "ms": 1e-3, "s": 1}


def analyze(path, top):
    declarations = []
    modules = {}
    stack = []
    unmatched = []
    phase_seconds = Counter()
    by_kind = defaultdict(lambda: {"calls": 0, "exclusive_seconds": 0.0})
    phase = None
    phase_start = 0.0
    last_progress = None
    last_declaration = None
    milestones = []
    lines = 0
    with path.open() as source:
        for lines, raw in enumerate(source, 1):
            line = raw.rstrip("\n")
            if line.startswith("checking "):
                stack.append({"label": line[9:], "start_line": lines, "children_seconds": 0.0})
            elif match := FINISHED.fullmatch(line):
                seconds = float(match[1]) * SCALE[match[2]]
                label = match[3]
                entry = {"label": label, "seconds": seconds, "end_line": lines}
                if stack and stack[-1]["label"] == label:
                    frame = stack.pop()
                    entry["start_line"] = frame["start_line"]
                    entry["exclusive_seconds"] = max(0.0, seconds - frame["children_seconds"])
                    if stack:
                        stack[-1]["children_seconds"] += seconds
                    # Generated module names may themselves contain colons.
                    kind = label.rsplit(": ", 1)[-1].split(" ", 1)[0]
                    by_kind[kind]["calls"] += 1
                    by_kind[kind]["exclusive_seconds"] += entry["exclusive_seconds"]
                else:
                    unmatched.append({"line": lines, "label": label})
                declarations.append(entry)
                last_declaration = entry
            elif line.startswith("progress "):
                event = dict(re.findall(r"(\w+)=(\S+)", line))
                event["line"] = lines
                elapsed = float(event["elapsed_seconds"])
                if "phase" in event:
                    if phase is not None:
                        phase_seconds[phase] += elapsed - phase_start
                    phase = event["phase"]
                    phase_start = elapsed
                if event.get("event") == "complete" and "module_seconds" in event:
                    modules[event["module"]] = {
                        "module": event["module"], "seconds_at_completion": float(event["module_seconds"]),
                        "elapsed_seconds": elapsed, "line": lines,
                    }
                    package_completed = event.get("package_completed", "0/0")
                    done = int(package_completed.split("/")[0])
                    if done and done % 50 == 0:
                        milestones.append({"package": event["module"].split(".")[0],
                                           "completed": package_completed, "elapsed_seconds": elapsed})
                last_progress = event
    if last_progress and phase is not None:
        phase_seconds[phase] += float(last_progress["elapsed_seconds"]) - phase_start
    return {
        "log": str(path), "lines": lines,
        "completed_declarations": len(declarations), "completed_modules": len(modules),
        "last_progress": last_progress, "last_completed_declaration": last_declaration,
        "unfinished_declarations": stack, "unmatched_completions": unmatched,
        "phase_seconds_through_last_progress": dict(phase_seconds),
        "declaration_kinds": dict(by_kind),
        "slowest_declarations": sorted(declarations, key=lambda x: x["seconds"], reverse=True)[:top],
        "slowest_completed_modules": sorted(modules.values(), key=lambda x: x["seconds_at_completion"], reverse=True)[:top],
        "package_milestones": milestones,
        "notes": ["Declaration durations exclude diagnostic time; nested calls are subtracted in exclusive_seconds.",
                  "Module durations are provisional at completion; later analysis and cache writes may add time.",
                  "The final phase is measured only through the last progress timestamp, not process exit.",
                  "This log alone cannot attribute an interruption to OOM, terminal closure, or a signal."],
    }



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
                command.add_argument("paths", type=Path, nargs="+" if action == "run" else "*")
            command.add_argument("--runs", type=int, default=1)
            command.add_argument("--cache-mode", choices=["off", "cold", "shared"])
            command.add_argument("--cache-dir", type=Path)
            command.add_argument("--command", help="raw command accepting the input path; shell-quoted arguments")
        else:
            command.set_defaults(command=None)
            command.add_argument("--depth", type=int, default=8)
            command.add_argument("--checkpoint", action="store_true", help="interrupt at a reported checkpoint and measure resumption")
        command.add_argument("--binary", type=Path, default=ROOT / "target/debug/cli")
        command.add_argument("--module")
        command.add_argument("--seconds", type=float, default=None if action == "case" else 300)
        command.add_argument("--memory-mib", type=int, default=None if action == "case" else 3072)
        command.add_argument("--cache-mib", type=int, default=8192)
        command.add_argument("--output-mib", type=int, default=8)
        command.add_argument("--batch-seconds", type=int)
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
        if args.memory_mib is None:
            args.memory_mib = args.case_definition["memory_mib"]
        if args.case_definition["target"] == "resolver" and args.command is None:
            args.command = shlex.join([str(BENCHMARKS / "target/debug/resolve-bench")])
    if args.output is None:
        args.output = BENCHMARKS / "runs" / getattr(args, "name", args.action) / "report.json"
    if (not math.isfinite(args.seconds) or args.seconds <= 0 or args.memory_mib < 1
            or args.cache_mib < 1 or args.output_mib < 1 or args.progress_seconds < 0
            or not math.isfinite(args.progress_seconds) or args.batch_seconds is not None and args.batch_seconds < 1
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
