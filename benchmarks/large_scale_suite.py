#!/usr/bin/env python3
"""Run the large-scale checking comparisons sequentially, without building binaries."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from bench import BENCHMARKS, ROOT, file_digest, save_json

PACKAGES = {
    "finite-models": "libs/topology/examples/finite_models",
    "singular-cohomology": "libs/topology/singular/cohomology",
    "manifolds": "libs/geometry/manifolds",
}
SELECTED = {
    "graph": "cohomology_examples.Graph.On.With",
    "chains": "singular_excision.MayerVietoris.Over.On.Chains",
    "torus": "cohomology_examples.Torus.Geometry.Ring.Primitive",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / "target/debug/cli")
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--output", type=Path, default=BENCHMARKS / "runs/large-scale-checking/final")
    parser.add_argument("--packages", nargs="+", choices=list(PACKAGES), default=list(PACKAGES))
    parser.add_argument("--stages", nargs="+", choices=["selected", "profiles", "full", "reuse", "scaling", "recovery", "baseline-full"],
                        default=["selected", "profiles", "full", "reuse", "scaling", "recovery", "baseline-full"])
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    manifest = {"binary_sha256": file_digest(args.binary), "runs": []}
    if args.baseline:
        manifest["baseline_sha256"] = file_digest(args.baseline)
    manifest_path = args.output / "suite.json"
    if manifest_path.exists():
        previous = json.loads(manifest_path.read_text(encoding="utf-8"))
        if previous["binary_sha256"] != manifest["binary_sha256"]:
            parser.error("output directory belongs to a different binary")
        manifest = previous | manifest | {"runs": previous["runs"]}

    def run(label, arguments, script="bench.py"):
        arguments = list(map(str, arguments))
        position = arguments.index("--extra") if "--extra" in arguments else len(arguments)
        arguments[position:position] = ["--output", str(args.output / f"{label}.json")]
        command = [sys.executable, str(BENCHMARKS / script), *arguments]
        print(label, flush=True)
        status = subprocess.run(command, cwd=ROOT, check=False).returncode
        manifest["runs"].append({"label": label, "command": command, "exit": status})
        save_json(manifest_path, manifest)
        return status

    for stage in ["selected", "profiles"]:
        if stage not in args.stages:
            continue
        for version, binary in [("baseline", args.baseline), ("current", args.binary)]:
            if binary is None:
                continue
            for name, module in SELECTED.items():
                profile = stage == "profiles"
                run(f"{stage}-{version}-{name}", ["run", PACKAGES["finite-models"], "--binary", binary,
                    "--module", module, "--runs", 1 if profile else 3, "--cache-mode", "off", "--memory-mib", 8192,
                    "--seconds", 600, *(["--profile-costs"] if profile else []), "--extra", "--module-only"])
    if "full" in args.stages:
        for memory in [8192, 3072]:
            for name in args.packages:
                path = PACKAGES[name]
                run(f"full-{name}-{memory}", ["run", path, "--binary", args.binary,
                    "--cache-mode", "shared", "--cache-dir", args.output / f"cache-{name}-{memory}",
                    "--memory-mib", memory, "--seconds", 3600, "--extra", "--full-check"])
    if "reuse" in args.stages:
        for name in args.packages:
            path = PACKAGES[name]
            for mode, extra in [("warm", []), ("full-local", ["--full-check-local"])]:
                run(f"{mode}-{name}", ["run", path, "--binary", args.binary, "--runs", 3,
                    "--cache-mode", "shared", "--cache-dir", args.output / f"cache-{name}-8192",
                    "--memory-mib", 8192, "--seconds", 3600, "--extra", *extra])
    if "scaling" in args.stages:
        run("scaling", ["--binary", args.binary, "--sizes", 16, 32, 64, "--runs", 3], "large_scale.py")
    if "recovery" in args.stages:
        run("cache-recovery", ["cache", "--binary", args.binary, "--depth", 16,
                              "--checkpoint", "--memory-mib", 3072, "--seconds", 300])
    if "baseline-full" in args.stages and args.baseline:
        run("baseline-full", ["run", PACKAGES["finite-models"], "--binary", args.baseline,
            "--cache-mode", "shared", "--cache-dir", args.output / "cache-baseline-full",
            "--memory-mib", 8192, "--seconds", 600, "--extra", "--full-check"])
    # Resource cutoffs are retained in individual reports, including expected
    # cutoffs of the baseline and the smaller memory budget.
    return 0 if all(row["exit"] == 0 for row in manifest["runs"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
