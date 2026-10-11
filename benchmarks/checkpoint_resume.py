#!/usr/bin/env python3
"""Bounded SIGKILL/resume measurement for module-boundary checkpoints (Linux)."""
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
MODULE = "resolutions.NonnegativeChain.Over.ShortExact.Morphism.Straighten.With"


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (2560 * 1024 ** 2, 2560 * 1024 ** 2))
    resource.setrlimit(resource.RLIMIT_CPU, (90, 91))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def run(cache, name, interrupt=False):
    log = ROOT / "benchmarks" / f"checkpoint-{name}.log"
    command = [str(ROOT / "target/debug/cli"), "libs/algebra/homological/computations", "--module", MODULE,
               "--cache-dir", str(cache), "--checkpoint-seconds", "1", "--cache-stats",
               "--diagnostics", "compact"]
    environment = {k: v for k, v in os.environ.items() if not k.startswith("REF_TYPE_PROFILE_")}
    environment["REF_TYPE_PROFILE_PROGRESS"] = "1"
    started = time.monotonic()
    interrupted = False
    current_module = ""
    with log.open("w") as writer, log.open() as reader:
        process = subprocess.Popen(command, cwd=ROOT, env=environment, stdout=writer,
                                   stderr=writer, preexec_fn=limits, start_new_session=True)
        try:
            while True:
                waited, status, usage = os.wait4(process.pid, os.WNOHANG)
                if waited:
                    process.returncode = os.waitstatus_to_exitcode(status)
                    break
                for line in reader:
                    if "event=complete" in line:
                        current_module = re.search(r"module=(\S+)", line)[1]
                    if (interrupt and not interrupted and "event=checkpoint-saved" in line
                            and current_module.startswith("homological_algebra.")):
                        os.killpg(process.pid, signal.SIGKILL)
                        interrupted = True
                if time.monotonic() - started > 90:
                    raise TimeoutError(name)
                time.sleep(0.01)
        finally:
            if process.returncode is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
    text = log.read_text()
    stats = re.search(r"queries: QueryStats \{(.*)\}", text)
    stats = dict((key, int(value)) for key, value in re.findall(r"(\w+): (\d+)", stats[1])) if stats else None
    result = {"seconds": round(time.monotonic() - started, 3), "peak_rss_kib": usage.ru_maxrss,
              "status": process.returncode, "interrupted_after_checkpoint": interrupted,
              "last_completed_module": current_module, "stats": stats,
              "partial_bytes": sum(p.stat().st_size for p in cache.glob("*.partial")),
              "log": str(log.relative_to(ROOT))}
    print(json.dumps({name: result}), flush=True)
    return result


def main():
    with tempfile.TemporaryDirectory(prefix="ref-type-checkpoint-") as directory:
        cache = Path(directory)
        interrupted = run(cache, "interrupted", interrupt=True)
        assert interrupted["interrupted_after_checkpoint"] and interrupted["status"] == -signal.SIGKILL
        resumed = run(cache, "resumed")
        assert resumed["status"] == 0 and resumed["stats"]["checkpoint_hits"] == 1
        warm = run(cache, "warm")
        assert warm["status"] == 0 and warm["stats"]["checked_modules"] == 0
        result = {"module": MODULE, "memory_limit_mib": 2560, "checkpoint_seconds": 1,
                  "interrupted": interrupted, "resumed": resumed, "warm": warm}
        (ROOT / "benchmarks/module-checkpoint-results.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
