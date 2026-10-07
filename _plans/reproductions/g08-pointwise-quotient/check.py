#!/usr/bin/env python3
"""Check the known failures and working comparisons; success means reproduced."""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
CASES = (
    ("01-direct-type", "uncaptured parameter"),
    ("02-function-alias", None),
    ("03-explicit-lambda", "uncaptured parameter"),
    ("04-scoped-lambda", None),
    ("05-alias-equality", "expected Program value-type syntax"),
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cli", type=Path, default=ROOT / "target/debug/cli")
    args = parser.parse_args()
    executable = args.cli.resolve()
    for name, diagnostic in CASES:
        project = Path(__file__).resolve().parent / name
        try:
            result = subprocess.run(
                [str(executable), str(project), "--no-cache", "--diagnostics", "compact"],
                cwd=ROOT, capture_output=True, text=True, timeout=120,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            print(f"{name}: {error}", file=sys.stderr)
            return 1
        valid = result.returncode == (1 if diagnostic else 0)
        if diagnostic:
            valid = valid and diagnostic in result.stderr and "Forms.ref:" in result.stderr
        if not valid:
            print(f"{name}: unexpected exit {result.returncode}\n{result.stdout}{result.stderr}", file=sys.stderr)
            return 1
        outcome = "success" if diagnostic is None else f"known failure ({diagnostic})"
        print(f"{name}: {outcome}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
