#!/usr/bin/env python3
"""Repeatable artifact-cache workloads; all generated sources and caches are temporary."""
import argparse
import hashlib
import json
import math
import os
import resource
import signal
from pathlib import Path
import subprocess
import sys
import tempfile
import time


def package(root, name, dependencies, body):
    directory = root / name
    (directory / "src").mkdir(parents=True, exist_ok=True)
    manifest = f'[package]\nname = "{name}"\n[dependencies]\n'
    manifest += ''.join(f'{dep} = {{path = "../{dep}"}}\n' for dep in dependencies)
    (directory / "ref.toml").write_text(manifest)
    (directory / "src/root.ref").write_text(body)
    return directory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--depth", type=int, default=8)
    parser.add_argument("--skip-interruption", action="store_true")
    parser.add_argument("--project", type=Path, action="append", default=[],
                        help="Also measure a real project cold and warm in a dedicated cache")
    parser.add_argument("--resume-project-cache", type=Path,
                        help="Continue one real project using a retained cache; preserve it afterward")
    parser.add_argument("--retain-project-caches", type=Path,
                        help="Keep real-project caches under a new directory for later validation")
    parser.add_argument("--work-dir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "refcache/artifact-benchmark-scratch",
                        help="Disk-backed scratch directory; generated caches are removed afterward")
    parser.add_argument("--memory-mib", type=int, default=1536,
                        help="Address-space limit for each checker process")
    parser.add_argument("--timeout", type=float, default=120,
                        help="Maximum seconds for each case, including supervisor workers")
    parser.add_argument("--cache-mib", type=int, default=2048,
                        help="Stop a case when its cache exceeds this disk budget")
    args = parser.parse_args()
    if args.depth < 0 or args.memory_mib <= 0 or args.cache_mib <= 0:
        parser.error("depth must be nonnegative and memory/cache limits must be positive")
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("timeout must be finite and positive")
    if args.resume_project_cache is not None:
        if len(args.project) != 1 or not args.resume_project_cache.is_dir():
            parser.error("--resume-project-cache requires one --project and an existing cache directory")
        args.resume_project_cache = args.resume_project_cache.resolve()
    if args.retain_project_caches is not None:
        if not args.project or args.resume_project_cache or args.retain_project_caches.exists():
            parser.error("--retain-project-caches requires --project, a new directory, and no resume cache")
        args.retain_project_caches = args.retain_project_caches.resolve()
        args.retain_project_caches.mkdir(parents=True)
    args.work_dir.mkdir(parents=True, exist_ok=True)

    def handle_interruption(signum, frame):
        # Let finally blocks reap the complete child group before scratch cleanup.
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            signal.signal(sig, signal.SIG_IGN)
        raise KeyboardInterrupt

    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, handle_interruption)

    def limit_child():
        limit = args.memory_mib * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
        os.nice(10)

    def signal_group(child, sig):
        try:
            os.killpg(child.pid, sig)
        except ProcessLookupError:
            pass

    def stop(child):
        # GNU time can exit before its checker: leader exit does not imply group exit.
        signal_group(child, signal.SIGTERM)
        try:
            child.wait(timeout=5)
        except subprocess.TimeoutExpired:
            pass
        finally:
            signal_group(child, signal.SIGKILL)
            child.wait()

    def cache_bytes(directory):
        total = 0
        for path in directory.rglob("*"):
            try:
                if path.is_file():
                    total += path.stat().st_size
            except FileNotFoundError:
                # Collection and atomic publication can remove a scanned path.
                pass
        return total

    def log_tail(path):
        with path.open("rb") as stream:
            stream.seek(max(0, path.stat().st_size - 65536))
            return stream.read(65536).decode(errors="replace").strip()

    def object_sizes(directory):
        kinds = {1: "result", 2: "resolver", 3: "environment", 4: "checkpoint"}
        totals = {}
        for path in (directory / "v2/objects").rglob("*"):
            if not path.is_file():
                continue
            try:
                with path.open("rb") as stream:
                    header = stream.read(28)
                stored_bytes = path.stat().st_size
            except FileNotFoundError:
                continue
            if len(header) != 28 or header[:8] != b"REFOBJ02" or header[8] not in kinds:
                continue
            total = totals.setdefault(kinds[header[8]], {"objects": 0, "stored_bytes": 0, "decoded_bytes": 0})
            total["objects"] += 1
            total["stored_bytes"] += stored_bytes
            total["decoded_bytes"] += int.from_bytes(header[20:28], "little")
        return totals

    binary = args.binary.resolve()
    binary_digest = hashlib.sha256()
    with binary.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            binary_digest.update(chunk)
    rows = []

    def save_report():
        output = json.dumps({
            "depth": args.depth,
            "binary_sha256": binary_digest.hexdigest(),
            "measurement_conditions": {
                "per_process_virtual_memory_mib": args.memory_mib,
                "case_timeout_seconds": args.timeout,
                "cache_limit_mib": args.cache_mib,
                "scratch": str(args.work_dir),
                "resumed_project_cache": str(args.resume_project_cache) if args.resume_project_cache else None,
                "retained_project_caches": str(args.retain_project_caches) if args.retain_project_caches else None,
            },
            "runs": rows,
        }, indent=2) + "\n"
        if args.output:
            # Preserve completed measurements even if writing a later report is interrupted.
            with tempfile.NamedTemporaryFile(mode="w", dir=args.output.parent,
                                             prefix=f".{args.output.name}.", delete=False) as stream:
                temporary = Path(stream.name)
                try:
                    stream.write(output)
                    stream.flush()
                    os.fsync(stream.fileno())
                    os.replace(temporary, args.output)
                finally:
                    temporary.unlink(missing_ok=True)
        return output

    with tempfile.TemporaryDirectory(prefix="ref-artifacts-", dir=args.work_dir) as directory:
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

        def command(path, extra=()):
            return [str(binary), str(path), "--cache-dir", str(cache),
                    "--cache-stats", "--no-progress", "--memory-mib", str(args.memory_mib), *extra]

        def run(case, path, extra=()):
            started = time.monotonic()
            rss = root / "rss.txt"
            rss.unlink(missing_ok=True)
            reason = None
            out = root / "case.stdout"
            err = root / "case.stderr"
            with out.open("w") as stdout, err.open("w") as stderr:
                child = subprocess.Popen(
                    ["/usr/bin/time", "-f", "%M\n%U\n%S", "-o", str(rss), *command(path, extra)],
                    stdout=stdout, stderr=stderr, start_new_session=True, preexec_fn=limit_child,
                )
                try:
                    while child.poll() is None:
                        if time.monotonic() - started > args.timeout:
                            reason = "time_limit"
                            break
                        if cache_bytes(cache) > args.cache_mib * 1024 * 1024:
                            reason = "cache_limit"
                            break
                        if out.stat().st_size + err.stat().st_size > 8 * 1024 * 1024:
                            reason = "output_limit"
                            break
                        try:
                            child.wait(timeout=0.25)
                        except subprocess.TimeoutExpired:
                            pass
                except KeyboardInterrupt:
                    reason = "interrupted"
                finally:
                    stop(child)
            rss_lines = rss.read_text().strip().splitlines() if rss.exists() else []
            measured = len(rss_lines) >= 3 and rss_lines[-3].isdigit()
            rows.append({
                "case": case, "seconds": time.monotonic() - started,
                "peak_rss_kib": int(rss_lines[-3]) if measured else None,
                "user_seconds": float(rss_lines[-2]) if measured else None,
                "system_seconds": float(rss_lines[-1]) if measured else None,
                "stopped_by": reason,
                "completed": reason is None and child.returncode == 0,
                "returncode": child.returncode,
                "cache_bytes": cache_bytes(cache),
                "stats": log_tail(err), "output": log_tail(out),
                "objects": object_sizes(cache),
            })
            save_report()
            print(f"{case}: {rows[-1]['seconds']:.3f}s, {rows[-1]['peak_rss_kib']} KiB, status {child.returncode}", file=sys.stderr, flush=True)
            if reason == "interrupted":
                raise KeyboardInterrupt

        run("cold", entry)
        run("warm", entry)
        run("other_consumer", other)
        (entry / "src/root.ref").write_text(body + "\n\\module Added { \\definition Q: \\Prop := \\forall (P: \\Prop) -> P -> P; }\n")
        run("entry_edit", entry)
        (leaf / "src/root.ref").write_text(r"\module Core { \definition P: \Prop := \forall (Q: \Prop) -> Q -> Q; }")
        run("dependency_edit", entry)

        # Two independent branches share the exact same nominal base instance.
        for branch in ["left", "right"]:
            package(root, branch, ["base"], r"\module Core { \import base.Core[] \as D; \definition P: \Prop := D.P; }")
        diamond_body = r"\module Main { \import left.Core[] \as L; \import right.Core[] \as R; \definition P: \Prop := L.P; \definition Q: \Prop := R.P; }"
        diamond = package(root, "diamond", ["left", "right"], diamond_body)
        run("diamond_cold", diamond)
        run("diamond_warm", diamond)
        diamond = package(root, "diamond", ["right", "left"], diamond_body)
        run("dependency_order", diamond)
        package(root, "independent", [], r"\module Core { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }")
        diamond = package(root, "diamond", ["independent", "right", "left"], diamond_body)
        run("unrelated_dependency", diamond)

        if not args.skip_interruption:
            cache = root / "resume-cache"
            interrupted = package(root, "interrupted", [previous], "\n".join(
                rf"\module M{i} {{ \import {previous}.Core[] \as D; \definition P: \Prop := D.P; }}"
                for i in range(160)))
            started = time.monotonic()
            out = root / "interrupted.stdout"
            err = root / "interrupted.stderr"
            with out.open("w") as stdout, err.open("w") as stderr:
                child = subprocess.Popen(command(interrupted, ["--checkpoint-seconds", "0"]),
                                         stdout=stdout, stderr=stderr, start_new_session=True, preexec_fn=limit_child)
                checkpoint_seen = False
                reason = None
                try:
                    while child.poll() is None:
                        if time.monotonic() - started > args.timeout:
                            reason = "time_limit"
                            break
                        if cache_bytes(cache) > args.cache_mib * 1024 * 1024:
                            reason = "cache_limit"
                            break
                        if out.stat().st_size + err.stat().st_size > 8 * 1024 * 1024:
                            reason = "output_limit"
                            break
                        checkpoint_seen = (any(cache.rglob("*.checkpoint")) or
                                           any(cache.rglob("*.partial")))
                        if checkpoint_seen:
                            signal_group(child, signal.SIGKILL)
                            break
                        time.sleep(0.02)
                except KeyboardInterrupt:
                    reason = "interrupted"
                finally:
                    stop(child)
            rows.append({"case": "interruption", "seconds": time.monotonic() - started,
                         "checkpoint_observed": checkpoint_seen, "returncode": child.returncode,
                         "stopped_by": reason, "cache_bytes": cache_bytes(cache)})
            save_report()
            if reason == "interrupted":
                raise KeyboardInterrupt
            if not checkpoint_seen:
                raise RuntimeError("No checkpoint observed before completion or timeout")
            run("resume", interrupted, ["--checkpoint-seconds", "0"])
            run("resume_warm", interrupted)

        for index, project in enumerate(args.project):
            project_root = args.retain_project_caches or root
            cache = args.resume_project_cache or project_root / f"project-cache-{index}"
            initial_case = "resume" if args.resume_project_cache else "cold"
            run(f"project:{project}:{initial_case}", project.resolve())
            if rows[-1]["returncode"] == 0:
                run(f"project:{project}:warm", project.resolve())
    output = save_report()
    if not args.output:
        print(output, end="")


if __name__ == "__main__":
    main()
