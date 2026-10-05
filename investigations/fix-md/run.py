#!/usr/bin/env python3
"""Check every standalone case in a fresh directory and record both diagnostic streams."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cli", type=Path, default=ROOT / "target/debug/cli")
    parser.add_argument("--output", type=Path, help="write all measured results as JSON")
    args = parser.parse_args()
    executable = args.cli.resolve()
    if not executable.is_file():
        parser.error(f"CLI not found: {executable}; run cargo build --locked -p cli")
    env = {k: v for k, v in os.environ.items()
           if k != "RUST_LOG" and not k.startswith(("REF_TYPE_", "REF_INVESTIGATION_"))}
    results = []
    for source in sorted((HERE / "cases").glob("*.ref")):
        expected = re.findall(r"^/\* expect-error: (.+) \*/$", source.read_text(), re.MULTILINE)
        expected_exit = 1 if expected else 0
        result = {"case": source.name, "expected_exit": expected_exit, "expected_errors": expected}
        with tempfile.TemporaryDirectory(prefix="ref-standalone-") as temporary:
            isolated = Path(temporary) / source.name
            isolated.write_bytes(source.read_bytes())
            for mode, flags in [("parse", ["--parse-only"]), ("check", [])]:
                command = [str(executable), str(isolated), "--no-cache", "--diagnostics", "compact", *flags]
                try:
                    process = subprocess.run(command, cwd=temporary, env=env, capture_output=True,
                                             text=True, timeout=30)
                    measured = {"exit": process.returncode, "stdout": process.stdout,
                                "stderr": process.stderr}
                except subprocess.TimeoutExpired as error:
                    measured = {"exit": "timeout", "stdout": str(error.stdout or ""),
                                "stderr": str(error.stderr or "")}
                for stream in ["stdout", "stderr"]:
                    measured[stream] = measured[stream].replace(temporary, "<isolated>")
                result[mode] = measured
        check = result["check"]
        result["matched"] = (
            result["parse"]["exit"] == 0
            and not result["parse"]["stdout"]
            and not result["parse"]["stderr"]
            and check["exit"] == expected_exit
            and not check["stdout"]
            and all(message in check["stderr"] for message in expected)
            and (expected_exit != 0 or not check["stderr"])
            and "panicked at" not in check["stderr"]
        )
        results.append(result)
        print(f"{'PASS' if result['matched'] else 'FAIL'} {source.name}: parse={result['parse']['exit']} check={check['exit']}")
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({"base": "d56d19914e9cc9c3fa5fe1e54415ec042bd20e62",
                                          "results": results}, ensure_ascii=False, indent=2) + "\n")
    print(f"{sum(r['matched'] for r in results)}/{len(results)} cases matched")
    return 0 if results and all(r["matched"] for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
