#!/usr/bin/env python3
"""Check all pointwise quotient representations without a cache."""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
CASES = (
    ("01-direct-type", None),
    ("02-function-alias", None),
    ("03-explicit-lambda", None),
    ("04-scoped-lambda", None),
    ("05-alias-equality", None),
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cli", type=Path, default=ROOT / "target/debug/cli")
    args = parser.parse_args()
    executable = args.cli.resolve()
    for name, _ in CASES:
        project = Path(__file__).resolve().parent / name
        try:
            result = subprocess.run(
                [str(executable), str(project), "--no-cache", "--diagnostics", "compact"],
                cwd=ROOT, capture_output=True, text=True, timeout=120,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            print(f"{name}: {error}", file=sys.stderr)
            return 1
        if result.returncode != 0:
            print(f"{name}: unexpected exit {result.returncode}\n{result.stdout}{result.stderr}", file=sys.stderr)
            return 1
        print(f"{name}: success", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
