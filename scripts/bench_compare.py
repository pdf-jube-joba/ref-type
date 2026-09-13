#!/usr/bin/env python3
"""Build isolated snapshots, then compare them on the same CPU and fixtures."""

import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import sys
import tarfile
import time


ROOT = Path(__file__).resolve().parents[1]


def command(args, cwd=ROOT, **kwargs):
    return subprocess.check_output(args, cwd=cwd, **kwargs)


def fingerprint(directory):
    digest = hashlib.sha256()
    for path in sorted(directory.rglob("*")):
        if path.is_file():
            digest.update(path.relative_to(directory).as_posix().encode() + b"\0")
            digest.update(hashlib.sha256(path.read_bytes()).digest())
    return digest.hexdigest()


def snapshot_worktree(destination):
    files = command(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"])
    for name in set(files.decode().split("\0")) - {""}:
        path = Path(name)
        # Only build sources and fixtures; exclude reports, docs and VCS state.
        if path.parts[0] not in {"src", "lib", "tests", ".cargo"} and name not in {
            "Cargo.toml", "Cargo.lock", "rust-toolchain", "rust-toolchain.toml"
        }:
            continue
        source = ROOT / path
        if source.is_file():
            target = destination / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)


def build(snapshot, target, binary, cargo, env, offline):
    args = cargo + [
        "bench", "--locked", "-p", "cli", "--bench", "performance", "--no-run",
        "--message-format=json", "--target-dir", str(target),
    ]
    if offline:
        args.append("--offline")
    completed = subprocess.run(args, cwd=snapshot, env=env, text=True, stdout=subprocess.PIPE)
    executables = []
    for line in completed.stdout.splitlines():
        message = json.loads(line)
        if message.get("reason") == "compiler-message":
            print(message["message"]["rendered"], end="", file=sys.stderr)
        if (message.get("reason") == "compiler-artifact"
                and message["target"]["name"] == "performance"
                and message.get("executable")):
            executables.append(message["executable"])
    completed.check_returncode()
    if len(executables) != 1:
        raise ValueError("Cargo did not report exactly one performance executable")
    shutil.copy2(executables[0], binary)


def read_samples(path):
    cases = {}
    for line in path.read_text().splitlines():
        if line.startswith(("#", "case\t")):
            continue
        case, _, _, _, duration = line.split("\t")
        cases.setdefault(case, []).append(float(duration))
    return cases


def positive(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", help="Git revision to compare with the current working tree")
    parser.add_argument("--output-dir", type=Path, help="new directory; existing results are never overwritten")
    parser.add_argument("--filter", default="")
    parser.add_argument("--rounds", type=positive, default=2, help="alternating before/after pairs (default: 2)")
    parser.add_argument("--samples", type=positive, default=20)
    parser.add_argument("--warmup-ms", type=int, default=200)
    parser.add_argument("--sample-ms", type=positive, default=50)
    parser.add_argument("--cpu", type=int, help="Linux CPU; defaults to the first allowed CPU")
    parser.add_argument("--toolchain", help="rustup toolchain; defaults to the currently active toolchain")
    parser.add_argument("--offline", action="store_true", help="use only locally cached dependencies")
    args = parser.parse_args()
    if args.samples < 2 or args.warmup_ms < 0:
        parser.error("samples must be >= 2 and warmup-ms must be >= 0")
    available = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else []
    cpu = args.cpu if args.cpu is not None else (available[0] if available else None)
    if cpu is not None and cpu not in available:
        parser.error(f"CPU {cpu} is not available: {available}")
    revision = command(["git", "rev-parse", "--verify", args.base + "^{commit}"], text=True).strip()
    toolchain = args.toolchain
    if toolchain is None and shutil.which("rustup"):
        toolchain = command(["rustup", "show", "active-toolchain"], text=True).split()[0]
    cargo = ["cargo"] + (["+" + toolchain] if toolchain else [])
    rustc = ["rustc"] + (["+" + toolchain] if toolchain else [])
    destination = (args.output_dir or ROOT / "target/benchmarks" / f"compare-{time.time_ns()}").resolve()
    if any(destination.is_relative_to(ROOT / name) for name in ["src", "lib", "tests", ".cargo"]):
        parser.error("output-dir must be outside source and fixture directories")
    destination.mkdir(parents=True, exist_ok=False)
    print(f"Results: {destination}", flush=True)
    runner = Path(__file__).resolve()
    shutil.copy2(runner, destination / "runner.py")
    before, after = destination / "before", destination / "after"
    before.mkdir()
    after.mkdir()
    archive = command(["git", "archive", "--format=tar", revision])
    with tarfile.open(fileobj=io.BytesIO(archive)) as contents:
        contents.extractall(before, filter="data")
    snapshot_worktree(after)

    # Both implementations run today's fixtures and benchmark harness. Keep
    # those exact files in the report so future edits cannot change a replay.
    for relative in ["lib", "tests", "src/cli/benches"]:
        target = before / relative
        if target.exists():
            shutil.rmtree(target)
        shutil.copytree(after / relative, target)
    if (before / "Cargo.lock").read_bytes() != (after / "Cargo.lock").read_bytes():
        raise ValueError("Cargo.lock differs: compare revisions using the same dependencies")
    manifests = {"Cargo.toml"} | {
        path.relative_to(snapshot).as_posix()
        for snapshot in [before, after]
        for path in (snapshot / "src").rglob("Cargo.toml")
    }
    for name in manifests:
        if not (before / name).is_file() or not (after / name).is_file():
            raise ValueError(f"build configuration differs: {name}")
        if (before / name).read_bytes() != (after / name).read_bytes():
            raise ValueError(f"build configuration differs: {name}")
    if fingerprint(before / ".cargo") != fingerprint(after / ".cargo"):
        raise ValueError("build configuration differs: .cargo")

    metadata = {
        "base_commit": revision,
        "worktree_commit": command(["git", "rev-parse", "HEAD"], text=True).strip(),
        "worktree_status": command(["git", "status", "--short"], text=True),
        "rustc": command(rustc + ["-Vv"], text=True),
        "cargo": command(cargo + ["-V"], text=True).strip(),
        "toolchain": toolchain,
        "runner_sha256": hashlib.sha256(runner.read_bytes()).hexdigest(),
        "platform": command(["uname", "-a"], text=True).strip(),
        "cpuinfo": Path("/proc/cpuinfo").read_text() if Path("/proc/cpuinfo").exists() else None,
        "allowed_cpus": available,
        "measurement_cpu": cpu,
        "settings": vars(args) | {"output_dir": str(destination)},
        "build_environment": {k: v for k, v in os.environ.items() if k in {
            "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC", "RUSTC_WRAPPER",
            "RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_TARGET"
        } or k.startswith("CARGO_PROFILE_")},
        "source_sha256": {name: fingerprint(destination / name / "src") for name in ["before", "after"]},
        "inputs_sha256": {name: fingerprint(after / name) for name in ["lib", "tests", "src/cli/benches"]},
        "lock_sha256": hashlib.sha256((after / "Cargo.lock").read_bytes()).hexdigest(),
        "manifests_sha256": {
            name: hashlib.sha256((after / name).read_bytes()).hexdigest()
            for name in sorted(manifests)
        },
        "runs": [],
    }
    (destination / "worktree.patch").write_bytes(command(["git", "diff", "HEAD", "--", "src", "Cargo.toml", "Cargo.lock"]))
    metadata_path = destination / "experiment.json"

    def save_metadata():
        metadata_path.write_text(json.dumps(metadata, indent=2, ensure_ascii=False) + "\n")

    save_metadata()
    env = os.environ.copy()
    env["LC_ALL"] = "C"
    if toolchain:
        env["RUSTUP_TOOLCHAIN"] = toolchain
    # Archived snapshots have no .git; do not report the enclosing worktree as
    # their source revision. experiment.json identifies each snapshot instead.
    env["GIT_CEILING_DIRECTORIES"] = str(destination)
    binaries = destination / "bin"
    binaries.mkdir()
    for name in ["before", "after"]:
        print(f"Building {name} ...", flush=True)
        # Local workspace package identities can collide in a shared Cargo
        # target directory. Separate outputs prevent reusing the other build.
        build(destination / name, destination / "build" / name, binaries / name, cargo, env, args.offline)
    metadata["binary_sha256"] = {
        name: hashlib.sha256((binaries / name).read_bytes()).hexdigest() for name in ["before", "after"]
    }
    save_metadata()
    # Finish both builds before timing. Every child inherits this CPU affinity.
    if cpu is not None:
        os.sched_setaffinity(0, {cpu})
    else:
        print("CPU affinity unavailable; measurement will use the OS scheduler.", flush=True)
    results = {"before": {}, "after": {}}
    for round_index in range(args.rounds):
        order = ["before", "after"] if round_index % 2 == 0 else ["after", "before"]
        for name in order:
            label = f"{name}-{round_index + 1}"
            invocation = [
                str(binaries / name), "--filter", args.filter,
                "--samples", str(args.samples), "--warmup-ms", str(args.warmup_ms),
                "--sample-ms", str(args.sample_ms), "--output-dir", str(destination),
                "--save-baseline", label,
            ]
            print(f"Measuring {label} ...", flush=True)
            subprocess.run(invocation, cwd=destination / name, env=env, check=True)
            metadata["runs"].append({"label": label, "command": invocation})
            save_metadata()
            for case, samples in read_samples(destination / f"{label}.tsv").items():
                results[name].setdefault(case, []).extend(samples)
    if results["before"].keys() != results["after"].keys():
        raise ValueError("benchmark cases differ")
    lines = ["case\tbefore_ms\tafter_ms\tchange_percent\tbefore_cv_percent\tafter_cv_percent"]
    for case, old in results["before"].items():
        new = results["after"][case]
        left, right = statistics.median(old), statistics.median(new)
        old_cv = 100 * statistics.stdev(old) / statistics.mean(old)
        new_cv = 100 * statistics.stdev(new) / statistics.mean(new)
        lines.append(f"{case}\t{left / 1e6:.6f}\t{right / 1e6:.6f}\t{100 * (right / left - 1):+.2f}\t{old_cv:.2f}\t{new_cv:.2f}")
    summary = "\n".join(lines) + "\n"
    (destination / "summary.tsv").write_text(summary)
    print(summary, end="")


if __name__ == "__main__":
    main()
