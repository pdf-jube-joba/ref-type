from dataclasses import dataclass, fields
import hashlib
import json
import math
import os
from pathlib import Path
import re
import resource
import shlex
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time

from log_analysis import cost_profile
from workloads import source_digest

ROOT = Path(__file__).resolve().parents[1]
BENCHMARKS = Path(__file__).resolve().parent


def target_directory():
    return Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target")).resolve()


@dataclass
class MeasurementOptions:
    output: Path
    binary: Path | None = None
    command: str | None = None
    action: str = "run"
    case_definition: dict | None = None
    profile_costs: str | None = None
    profile_phases: bool = False
    seconds: float = 300
    cache_mib: int | None = None
    module: str | None = None
    extra: tuple[str, ...] = ()
    progress_seconds: float = 30
    output_mib: int = 8

    @classmethod
    def from_namespace(cls, namespace):
        return cls(**{field.name: getattr(namespace, field.name)
                      for field in fields(cls) if hasattr(namespace, field.name)})


def save_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                     prefix=path.name + ".", suffix=".tmp", delete=False) as file:
        temporary = Path(file.name)
        try:
            json.dump(value, file, indent=2, ensure_ascii=False)
            file.write("\n")
            file.close()
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)


def file_digest(path):
    with path.open("rb") as file:
        return hashlib.file_digest(file, "sha256").hexdigest()


def directory_bytes(directory):
    total = 0
    if directory is not None:
        for path in directory.rglob("*"):
            try:
                if path.is_file():
                    total += path.stat().st_size
            except FileNotFoundError:
                pass
    return total


def tail(path, size=65536):
    with path.open("rb") as file:
        file.seek(max(0, path.stat().st_size - size))
        return file.read(size).decode("utf-8", errors="replace")


def measure(command, log, *, seconds, environment=None,
            progress_seconds=0, output_mib=8):
    def limits():
        cpu = math.ceil(seconds)
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 1))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    def reap(block=False):
        waited, status, usage = os.wait4(child.pid, 0 if block else os.WNOHANG)
        if waited:
            child.returncode = os.waitstatus_to_exitcode(status)
            return usage
        return None

    def send(sig):
        try:
            os.killpg(child.pid, sig)
        except ProcessLookupError:
            pass

    def stop():
        send(signal.SIGTERM)
        deadline = time.monotonic() + 2
        while time.monotonic() < deadline:
            if usage := reap():
                return usage
            time.sleep(.02)
        send(signal.SIGKILL)
        return reap(True)

    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    next_progress = started + progress_seconds
    reason = None
    with log.open("wb") as output:
        child = subprocess.Popen(command, cwd=ROOT, env=environment, stdout=output, stderr=output,
                                 stdin=subprocess.DEVNULL, start_new_session=True, preexec_fn=limits)
        try:
            while (usage := reap()) is None:
                now = time.monotonic()
                if now - started >= seconds:
                    reason = "time_limit"
                elif log.stat().st_size > output_mib * 2**20:
                    reason = "output_limit"
                if reason:
                    usage = stop()
                    break
                if progress_seconds > 0 and now >= next_progress:
                    print(f"  running {now - started:.0f}s: {log}", file=sys.stderr, flush=True)
                    next_progress = now + progress_seconds
                time.sleep(.02)
        except KeyboardInterrupt:
            reason = "interrupted"
            usage = stop()
        except BaseException:
            stop()
            raise
    if reason is None and (child.returncode in (-signal.SIGKILL, -signal.SIGXCPU)
                           or child.returncode != 0 and "memory allocation of" in tail(log)):
        reason = "resource_limit"
    return dict(command=command, exit=child.returncode, seconds=round(time.monotonic() - started, 3),
                user_seconds=round(usage.ru_utime, 3), system_seconds=round(usage.ru_stime, 3),
                peak_rss_kib=usage.ru_maxrss, stopped_by=reason, log=str(log),
                profile=cost_profile(log))


class Measurements:
    def __init__(self, args):
        self.options = args
        self.output = args.output.resolve()
        self.logs = self.output.parent / (self.output.stem + "-logs")
        self.command = shlex.split(args.command) if args.command else [str((args.binary or target_directory() / "debug/cli").resolve())]
        if not self.command or not (executable := shutil.which(self.command[0])):
            raise ValueError("checker command does not exist; build or specify --binary/--command")
        self.command[0] = str(Path(executable).resolve())
        self.binary_digest = file_digest(Path(self.command[0]))
        self.command_digests = {str(Path(token).resolve()): file_digest(Path(token))
                                for token in self.command if Path(token).is_file()}
        self.environment = os.environ.copy()
        if args.profile_costs is not None:
            self.environment["REF_TYPE_PROFILE_COSTS"] = args.profile_costs
        if args.profile_phases:
            self.environment["REF_TYPE_PROFILE_PHASES"] = "1"
        self.report = dict(version=1, action=args.action,
                           case_definition=getattr(args, "case_definition", None),
                           binary_sha256=self.binary_digest,
                           command_sha256=self.command_digests,
                           seconds_per_run=args.seconds,
                           profile_environment={k: v for k, v in self.environment.items()
                                                if k.startswith("REF_TYPE_PROFILE_")},
                           measurements=[], complete=False)
        self.save()

    def save(self):
        rows = self.report["measurements"]
        summary = {}
        for label in dict.fromkeys(row["case"] for row in rows):
            successful = [row for row in rows if row["case"] == label and row["completed"]]
            if successful:
                summary[label] = dict(runs=len(successful),
                                      median_seconds=statistics.median(row["seconds"] for row in successful),
                                      peak_rss_kib=max(row["peak_rss_kib"] for row in successful))
        self.report["summary"] = summary
        save_json(self.output, self.report)

    def run(self, label, path, cache=None):
        path = path.resolve()
        index = len(self.report["measurements"])
        basename = f"{index:03}-" + re.sub(r"[^\w.-]+", "-", label)
        log = self.logs / (basename + ".log")
        checker_report = self.logs / (basename + ".checker.json")
        command = [*self.command, str(path)]
        if not self.options.command:
            command += ["--diagnostics", "compact", "--no-progress", "--report-json", str(checker_report)]
            if self.options.cache_mib is not None:
                command += ["--cache-budget-mib", str(self.options.cache_mib)]
            command += ["--cache-dir", str(cache)] if cache is not None else ["--no-cache"]
            if self.options.module:
                command += ["--module", self.options.module]
        command += self.options.extra
        before = source_digest(path)
        row = measure(command, log, seconds=self.options.seconds,
                      environment=self.environment, progress_seconds=self.options.progress_seconds,
                      output_mib=self.options.output_mib)
        try:
            unchanged = source_digest(path) == before
        except (OSError, ValueError):
            unchanged = False
        row.update(case=label, path=str(path), sources_sha256=before,
                   sources_unchanged=unchanged, cache_bytes=directory_bytes(cache))
        if not self.options.command:
            try:
                row["checker"] = json.loads(checker_report.read_text(encoding="utf-8"))
            except (OSError, ValueError):
                row["checker"] = None
        row["completed"] = (row["exit"] == 0 and row["stopped_by"] is None and row["sources_unchanged"]
                            and (self.options.command is not None or isinstance(row["checker"], dict)
                                 and row["checker"].get("version") == 2
                                 and row["checker"].get("outcome") == "accepted"))
        self.report["measurements"].append(row)
        self.save()
        print(f"{label}: {row['seconds']:.3f}s, {row['peak_rss_kib']} KiB, exit {row['exit']}", flush=True)
        if row["stopped_by"] == "interrupted":
            raise KeyboardInterrupt
        return row

    def finish(self):
        rows = self.report["measurements"]
        self.report["binary_unchanged"] = all(Path(path).is_file() and file_digest(Path(path)) == digest
                                              for path, digest in self.command_digests.items())
        self.report["complete"] = (bool(rows) and self.report["binary_unchanged"]
                                   and all(row["completed"] for row in rows))
        self.save()
        print(f"complete={self.report['complete']}; report: {self.output}")
        return 0 if self.report["complete"] else 1
