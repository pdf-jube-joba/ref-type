#!/usr/bin/env python3
"""Run one checker measurement with process-group and memory limits (Linux).

Example: python3 benchmarks/check.py libs/std --binary target/debug/cli
"""
import argparse
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path")
    parser.add_argument("--binary", default="target/debug/cli")
    parser.add_argument("--module")
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--memory-mib", type=int, default=2560)
    parser.add_argument("--log", type=Path, default=Path("benchmarks/check.log"))
    parser.add_argument("--result", type=Path, help="Write the final measurement as JSON")
    parser.add_argument("--cache-dir", help="Enable the persistent cache in this directory")
    parser.add_argument("--progress-seconds", type=float, default=0,
                        help="Print elapsed time and current RSS at this interval")
    args = parser.parse_args()
    if args.seconds <= 0 or args.memory_mib <= 0:
        parser.error("limits must be positive")

    command = [args.binary, args.path, "--diagnostics", "compact"]
    if args.module:
        command.extend(["--module", args.module])
    if args.cache_dir:
        command.extend(["--cache-dir", args.cache_dir])
    else:
        command.append("--no-cache")

    def limits():
        memory = args.memory_mib * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
        resource.setrlimit(resource.RLIMIT_CPU, (args.seconds, args.seconds + 1))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    started = time.monotonic()
    last_progress = started
    timed_out = False
    with args.log.open("w") as log:
        process = subprocess.Popen(command, stdout=log, stderr=log,
                                   start_new_session=True, preexec_fn=limits)
        try:
            while True:
                waited, status, usage = os.wait4(process.pid, os.WNOHANG)
                if waited:
                    break
                if time.monotonic() - started >= args.seconds:
                    timed_out = True
                    os.killpg(process.pid, signal.SIGKILL)
                    _, status, usage = os.wait4(process.pid, 0)
                    break
                now = time.monotonic()
                if args.progress_seconds > 0 and now - last_progress >= args.progress_seconds:
                    try:
                        status_text = Path(f"/proc/{process.pid}/status").read_text()
                        rss = next(int(line.split()[1]) for line in status_text.splitlines()
                                   if line.startswith("VmRSS:"))
                        print(json.dumps({"elapsed_seconds": round(now - started, 1),
                                          "current_rss_kib": rss}), flush=True)
                    except (FileNotFoundError, StopIteration):
                        pass
                    last_progress = now
                time.sleep(0.01)
            process.returncode = os.waitstatus_to_exitcode(status)
        except BaseException:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            raise
    result = {
        "command": command,
        "seconds": round(time.monotonic() - started, 3),
        "peak_rss_kib": usage.ru_maxrss,
        "address_space_mib": args.memory_mib,
        "status": process.returncode,
        "timeout": timed_out,
        "log": str(args.log),
    }
    if args.result:
        args.result.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))
    return 124 if timed_out else (0 if process.returncode == 0 else 1)


if __name__ == "__main__":
    raise SystemExit(main())
