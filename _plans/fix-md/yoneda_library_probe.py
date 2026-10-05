#!/usr/bin/env python3
"""Check the original Transformations import shape in disposable copies of the real library."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--cli", type=Path, default=ROOT / "target/debug/cli")
args = parser.parse_args()
env = {k: v for k, v in os.environ.items()
       if k != "RUST_LOG" and not k.startswith(("REF_TYPE_", "REF_INVESTIGATION_"))}
with tempfile.TemporaryDirectory(prefix="ref-yoneda-") as temporary:
    copy = Path(temporary)
    for source, destination in [("libs/category", "category"), ("tests/projects/category", "example")]:
        shutil.copytree(ROOT / source, copy / destination, ignore=shutil.ignore_patterns("refcache"))
    manifest = copy / "category/ref.toml"
    manifest.write_text(manifest.read_text().replace("../std", (ROOT / "libs/std").as_posix()))
    manifest = copy / "example/ref.toml"
    manifest.write_text(manifest.read_text().replace("../../../libs/category", "../category"))
    source = copy / "category/src/SetValued.ref"
    text = source.read_text()
    start = text.index("    \\definition Family:", text.index("  \\module Yoneda"))
    end = text.index("    \\import std.Data[]", start)
    text = text[:start] + r"""    \import category.SetValued[].On[C := C].Transformations[P := hom u, Q := P] \as Maps;
    \definition Family: \Set := Maps.Family;
    \definition Naturality(a: Family): \Prop := Maps.Naturality a;
    \definition Transformation: \Set := Maps.Transformation;
""" + text[end:]
    text = text.replace(r"\definition evaluate(a: Transformation)", r"\definition evaluate(a: Maps.Transformation)")
    text = text.replace(r"\definition fromElement(p: P.Carrier u): Transformation", r"\definition fromElement(p: P.Carrier u): Maps.Transformation")
    source.write_text(text)
    result = subprocess.run([str(args.cli.resolve()), str(copy / "example"), "--no-cache"],
                            cwd=copy, env=env, capture_output=True, text=True, timeout=180)
    print("category examples with restored Transformations import:", result.returncode)
    print(result.stdout.replace(temporary, "<temporary>"), end="")
    print(result.stderr.replace(temporary, "<temporary>"), end="")
    raise SystemExit(result.returncode)
