#!/usr/bin/env python3
"""Build the current kernel and run the independent API probe without editing Rust crates."""
import json
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
result = subprocess.run(
    ["cargo", "build", "--locked", "-p", "kernel", "--message-format=json"],
    cwd=root, text=True, stdout=subprocess.PIPE, check=True,
)
artifacts = [json.loads(line) for line in result.stdout.splitlines() if line.startswith("{")]
rlib = next(Path(name) for artifact in artifacts
            if artifact.get("reason") == "compiler-artifact" and artifact["target"]["name"] == "kernel"
            for name in artifact["filenames"] if name.endswith(".rlib"))
with tempfile.TemporaryDirectory(prefix="ref-kernel-probe-") as temporary:
    executable = Path(temporary) / "probe"
    subprocess.run([
        os.environ.get("RUSTC", "rustc"), "--edition=2024", str(Path(__file__).with_suffix(".rs")),
        "--extern", f"kernel={rlib}", "-L", f"dependency={rlib.parent / 'deps'}", "-o", str(executable),
    ], cwd=root, check=True)
    subprocess.run([str(executable)], check=True)
