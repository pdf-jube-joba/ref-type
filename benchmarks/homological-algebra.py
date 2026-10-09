"""Measure the checked examples, including their dependency checks."""
import csv
import os
from pathlib import Path
import subprocess
import sys
import time

repo_root = Path(__file__).resolve().parent.parent
logs_root = Path(sys.argv[1]) if len(sys.argv) > 1 else repo_root / "work/homological-algebra-benchmark"
logs_root.mkdir(parents=True, exist_ok=True)
with (logs_root / "results.csv").open("w", newline="") as metrics:
    writer = csv.writer(metrics, lineterminator="\n")
    writer.writerow(["example", "wall_seconds", "max_rss_kib"])
    for example in ["IntegerArithmetic", "IntegerMatrices", "Finite"]:
        with (logs_root / f"{example}.log").open("w") as log:
            started = time.monotonic()
            process = subprocess.Popen(
                [str(repo_root / "target/debug/cli"),
                 str(repo_root / "tests/projects/homological-algebra"),
                 "--module", f"homological_algebra_tests.{example}",
                 "--no-cache", "--diagnostics", "compact"],
                cwd=repo_root, stdout=log, stderr=subprocess.STDOUT,
            )
            _, status, usage = os.wait4(process.pid, 0)
            process.returncode = os.waitstatus_to_exitcode(status)
            writer.writerow([example, f"{time.monotonic() - started:.3f}", usage.ru_maxrss])
            metrics.flush()
            if process.returncode:
                sys.exit(f"{example} failed; see {log.name}")
print((logs_root / "results.csv").read_text(), end="")
