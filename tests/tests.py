#!/usr/bin/env python3
"""Execute documented CLI acceptance tests using Python 3.11+ and its standard library."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import dataclass, field
import errno
import fnmatch
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import select
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
SCOPES = {"module", "package", "workspace"}
EXPECTATIONS = {"accept": ("accepted", 0), "reject": ("rejected", 1)}
COMMON = {"id", "expect", "args", "env", "entry", "cwd", "timeout",
          "stdout", "stdout_same_as", "stdout_lines", "stdout_bytes_min", "stderr_empty",
          "remove", "checks", "terminal", "interrupt"}
CONFIG = COMMON | {"scope", "name", "parameters"}


class DefinitionError(ValueError):
    """The document does not describe an executable test."""


@dataclass
class Source:
    path: str | None
    text: str
    line: int


@dataclass
class Step:
    config: dict
    line: int
    sources: list[Source] = field(default_factory=list)


@dataclass
class Case:
    document: Path
    config: dict
    line: int
    scenario: bool
    sources: list[Source] = field(default_factory=list)
    steps: list[Step] = field(default_factory=list)

    @property
    def label(self):
        try:
            path = self.document.relative_to(ROOT)
        except ValueError:
            path = self.document
        return f"{path}::{self.config['id']}"


def relative_path(value, context):
    if not isinstance(value, str) or not value or "\\" in value:
        raise DefinitionError(f"{context}: expected a relative POSIX path")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts:
        raise DefinitionError(f"{context}: path must stay inside the test directory")
    return path


def validate_config(config, allowed, context, *, expectation=False):
    unknown = config.keys() - allowed
    if unknown:
        raise DefinitionError(f"{context}: unknown fields: {', '.join(sorted(unknown))}")
    if not isinstance(config.get("id"), str) or not re.fullmatch(r"[\w.-]+", config["id"]):
        raise DefinitionError(f"{context}: id must be a nonempty identifier")
    outcomes = {*EXPECTATIONS, "interrupted"}
    if expectation and (not isinstance(config.get("expect"), str) or config["expect"] not in outcomes):
        raise DefinitionError(f"{context}: expect must be accept, reject or interrupted")
    if "expect" in config and (not isinstance(config["expect"], str) or config["expect"] not in outcomes):
        raise DefinitionError(f"{context}: expect must be accept, reject or interrupted")
    for key in ("args", "remove"):
        if key in config and (not isinstance(config[key], list)
                              or not all(isinstance(item, str) for item in config[key])):
            raise DefinitionError(f"{context}: {key} must be an array of strings")
    for key in ("entry", "cwd"):
        if key in config:
            relative_path(config[key], context)
    for path in config.get("remove", []):
        if str(relative_path(path, context)) == ".":
            raise DefinitionError(f"{context}: remove must name a file or subdirectory")
    for key in ("stdout", "stdout_same_as", "name", "parameters"):
        if key in config and not isinstance(config[key], str):
            raise DefinitionError(f"{context}: {key} must be a string")
    if "name" in config and not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", config["name"]):
        raise DefinitionError(f"{context}: invalid module name")
    for key in ("stdout_lines", "stdout_bytes_min"):
        if key in config and (type(config[key]) is not int or config[key] < 0):
            raise DefinitionError(f"{context}: {key} must be a nonnegative integer")
    if "timeout" in config and (type(config["timeout"]) not in (int, float)
                                or not 0 < config["timeout"] < float("inf")):
        raise DefinitionError(f"{context}: timeout must be a positive finite number")
    for key in ("stderr_empty", "terminal"):
        if key in config and type(config[key]) is not bool:
            raise DefinitionError(f"{context}: {key} must be a boolean")
    if "interrupt" in config:
        interrupt = config["interrupt"]
        if (not isinstance(interrupt, dict) or not interrupt
                or interrupt.keys() - {"terminal", "stderr"}
                or not all(isinstance(value, str) and value for value in interrupt.values())):
            raise DefinitionError(f"{context}: interrupt must map terminal/stderr to nonempty strings")
    validate_checks(config.get("checks", []), context)
    environment = config.get("env", {})
    if not isinstance(environment, dict) or not all(
        isinstance(key, str) and key and "=" not in key and "\0" not in key
        and isinstance(value, str) and "\0" not in value
        for key, value in environment.items()
    ):
        raise DefinitionError(f"{context}: env must map environment names to strings")
    for arg in config.get("args", []):
        if arg.split("=", 1)[0] in {"--report-json", "--worker"}:
            raise DefinitionError(f"{context}: {arg} is managed by the runner")


def validate_checks(checks, context):
    if not isinstance(checks, list):
        raise DefinitionError(f"{context}: checks must be an array of tables")
    for check in checks:
        if not isinstance(check, dict) or check.keys() - {
            "stream", "contains", "absent", "ordered", "pattern", "count", "sum_equals",
            "relative_tolerance", "positive",
        }:
            raise DefinitionError(f"{context}: invalid output check")
        if not isinstance(check.get("stream"), str) or check["stream"] not in {"stdout", "stderr", "terminal"}:
            raise DefinitionError(f"{context}: check stream must be stdout, stderr or terminal")
        if not ({"contains", "absent", "ordered", "pattern"} & check.keys()):
            raise DefinitionError(f"{context}: empty output check")
        for key in ("contains", "absent", "ordered"):
            if key in check and (not isinstance(check[key], list)
                                 or not all(isinstance(value, str) and value for value in check[key])):
                raise DefinitionError(f"{context}: {key} must be an array of nonempty strings")
        for key in ("pattern", "sum_equals"):
            if key in check:
                if not isinstance(check[key], str):
                    raise DefinitionError(f"{context}: {key} must be a regular expression")
                try:
                    pattern = re.compile(check[key], re.MULTILINE)
                except re.error as error:
                    raise DefinitionError(f"{context}: {error}") from error
                if "sum_equals" in check and pattern.groups != 1:
                    raise DefinitionError(f"{context}: numeric patterns require one capture group")
        if "count" in check and ("pattern" not in check or type(check["count"]) is not int or check["count"] < 0):
            raise DefinitionError(f"{context}: count requires a pattern and a nonnegative integer")
        if "sum_equals" in check and "pattern" not in check:
            raise DefinitionError(f"{context}: sum_equals requires a pattern")
        if "relative_tolerance" in check and (
            "sum_equals" not in check or type(check["relative_tolerance"]) not in (int, float)
            or not 0 <= check["relative_tolerance"] < float("inf")
        ):
            raise DefinitionError(f"{context}: relative_tolerance requires sum_equals and a finite nonnegative number")
        if "positive" in check and ("sum_equals" not in check or type(check["positive"]) is not bool):
            raise DefinitionError(f"{context}: positive requires sum_equals and a boolean")


def fences(document):
    lines = document.read_text(encoding="utf-8").splitlines(keepends=True)
    index = 0
    while index < len(lines):
        opening = re.fullmatch(r" {0,3}(`{3,}|~{3,})([^\r\n]*)\r?\n?", lines[index])
        if not opening:
            index += 1
            continue
        marker, info = opening.groups()
        start = index + 1
        index += 1
        body = []
        closing = re.compile(r" {0,3}" + re.escape(marker[0]) + "{" + str(len(marker)) + r",}\s*")
        while index < len(lines) and not closing.fullmatch(lines[index]):
            body.append(lines[index])
            index += 1
        if index == len(lines):
            raise DefinitionError(f"{document}:{start}: unclosed code fence")
        yield info.strip(), "".join(body), start
        index += 1


def parse_document(document):
    cases = []
    current = None
    step = None
    for info, body, line in fences(document):
        context = f"{document}:{line}"
        tokens = shlex.split(info)
        if tokens in (["toml", "case"], ["toml", "scenario"], ["toml", "step"]):
            try:
                config = tomllib.loads(body)
            except tomllib.TOMLDecodeError as error:
                raise DefinitionError(f"{context}: {error}") from error
            if tokens[1] == "step":
                if current is None or not current.scenario:
                    raise DefinitionError(f"{context}: step requires a scenario")
                validate_config(config, COMMON, context, expectation=True)
                step = Step(config, line)
                current.steps.append(step)
            else:
                scenario = tokens[1] == "scenario"
                validate_config(config, CONFIG, context, expectation=not scenario)
                if not isinstance(config.get("scope"), str) or config["scope"] not in SCOPES:
                    raise DefinitionError(f"{context}: scope must be module, package or workspace")
                if scenario and "expect" in config:
                    raise DefinitionError(f"{context}: put expectations on scenario steps")
                if scenario and "stdout_same_as" in config:
                    raise DefinitionError(f"{context}: stdout_same_as belongs on a step")
                current = Case(document, config, line, scenario)
                cases.append(current)
                step = None
        elif tokens and tokens[0] in {"ref", "toml", "text"} and (
            current is not None or any(token.startswith("file=") for token in tokens[1:])
        ):
            if current is None:
                raise DefinitionError(f"{context}: source requires a case or scenario")
            attributes = {}
            for token in tokens[1:]:
                if "=" not in token:
                    raise DefinitionError(f"{context}: invalid source attribute {token}")
                key, value = token.split("=", 1)
                if key not in {"file", "repeat"} or key in attributes:
                    raise DefinitionError(f"{context}: invalid source attribute {key}")
                attributes[key] = value
            path = attributes.get("file")
            if path is None and (tokens[0] != "ref" or current.config["scope"] != "module"):
                raise DefinitionError(f"{context}: this source block requires file=")
            if path is not None:
                if str(relative_path(path, context)) == ".":
                    raise DefinitionError(f"{context}: file must name a file")
            try:
                repeat = int(attributes.get("repeat", "1"))
            except ValueError as error:
                raise DefinitionError(f"{context}: repeat must be a positive integer") from error
            if not 1 <= repeat <= 100_000 or len(body.encode("utf-8")) * repeat > 16 * 1024 * 1024:
                raise DefinitionError(f"{context}: invalid or excessive source repetition")
            (step.sources if step else current.sources).append(Source(path, body * repeat, line))
        elif tokens and tokens[0] == "toml" and len(tokens) > 1:
            raise DefinitionError(f"{context}: unknown test fence {info}")
        elif any(token.startswith("file=") for token in tokens[1:]):
            raise DefinitionError(f"{context}: unsupported source fence {info}")
    ids = set()
    for case in cases:
        context = f"{document}:{case.line}"
        if case.config["id"] in ids:
            raise DefinitionError(f"{context}: duplicate case id {case.config['id']}")
        ids.add(case.config["id"])
        if case.scenario and not case.steps:
            raise DefinitionError(f"{context}: scenario has no steps")
        if not case.sources and not (
            case.scenario and case.steps[0].sources
        ):
            raise DefinitionError(f"{context}: test has no initial sources")
        if case.config["scope"] != "module" and ({"name", "parameters"} & case.config.keys()):
            raise DefinitionError(f"{context}: name and parameters require module scope")
        previous = set()
        for item in case.steps if case.scenario else [Step(case.config, case.line, case.sources)]:
            if item.config["id"] in previous:
                raise DefinitionError(f"{document}:{item.line}: duplicate step id")
            if "stdout_same_as" in item.config and item.config["stdout_same_as"] not in previous:
                raise DefinitionError(f"{document}:{item.line}: stdout_same_as requires an earlier step")
            settings = {**case.config, **item.config}
            if settings.get("interrupt") and not settings.get("terminal"):
                raise DefinitionError(f"{document}:{item.line}: interrupt requires terminal = true")
            if (settings.get("expect") == "interrupted") != bool(settings.get("interrupt")):
                raise DefinitionError(f"{document}:{item.line}: interrupted expectation requires interrupt conditions")
            paths = [source.path for source in item.sources]
            if len(paths) != len(set(paths)):
                raise DefinitionError(f"{document}:{item.line}: source file written twice in one step")
            previous.add(item.config["id"])
        paths = [source.path for source in case.sources]
        if len(paths) != len(set(paths)):
            raise DefinitionError(f"{context}: initial source file written twice")
    return cases


def contained(root, path):
    target = root / str(relative_path(path, "runtime path"))
    if not target.resolve().is_relative_to(root.resolve()):
        raise DefinitionError(f"path escapes test directory through a symlink: {path}")
    return target


def write_sources(case, directory, sources):
    for source in sources:
        path = source.path
        if path is None:
            path = case.config.get("name", "Test") + ".ref"
        target = contained(directory, path)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source.text, encoding="utf-8")


@contextmanager
def work_directory(keep_failed):
    if not keep_failed:
        with tempfile.TemporaryDirectory(prefix="ref-type-test-") as directory:
            yield Path(directory)
        return
    directory = Path(tempfile.mkdtemp(prefix="ref-type-test-"))
    try:
        yield directory
    except BaseException:
        print(f"  preserved: {directory}", file=sys.stderr)
        raise
    else:
        shutil.rmtree(directory)


def terminate(child):
    if child.poll() is not None:
        return
    if os.name == "posix":
        try:
            os.killpg(child.pid, signal.SIGTERM)
        except ProcessLookupError:
            child.wait()
            return
    else:
        child.terminate()
    try:
        child.communicate(timeout=2)
    except subprocess.TimeoutExpired:
        if os.name == "posix":
            os.killpg(child.pid, signal.SIGKILL)
        else:
            child.kill()
        child.communicate()


def invoke(command, cwd, environment, timeout, logs):
    logs.mkdir(parents=True, exist_ok=True)
    (logs / "command.json").write_text(json.dumps(
        {"command": command, "cwd": str(cwd)}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    # File redirection drains both outputs without a pipe-buffer deadlock.
    with (logs / "stdout").open("wb") as stdout, (logs / "stderr").open("wb") as stderr:
        child = subprocess.Popen(command, cwd=cwd, env=environment, stdin=subprocess.DEVNULL,
                                 stdout=stdout, stderr=stderr, start_new_session=os.name == "posix")
        try:
            child.wait(timeout=timeout)
        except subprocess.TimeoutExpired as error:
            raise AssertionError(f"CLI exceeded {timeout} seconds") from error
        finally:
            terminate(child)
    return (child.returncode, (logs / "stdout").read_bytes(), (logs / "stderr").read_bytes())


def invoke_terminal(command, cwd, environment, timeout, logs, interrupt=None):
    import pty
    import resource

    logs.mkdir(parents=True, exist_ok=True)
    (logs / "command.json").write_text(json.dumps(
        {"command": command, "cwd": str(cwd)}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    child, terminal = pty.fork()
    if child == 0:
        try:
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            os.chdir(cwd)
            for descriptor, stream in ((1, "stdout"), (2, "stderr")):
                with (logs / stream).open("wb", buffering=0) as output:
                    os.dup2(output.fileno(), descriptor)
            os.execvpe(command[0], command, environment)
        finally:
            os._exit(127)
    captured = bytearray()
    sent_interrupt = False
    reaped = False
    deadline = time.monotonic() + timeout
    try:
        while time.monotonic() < deadline:
            if select.select([terminal], [], [], 0.01)[0]:
                try:
                    captured.extend(os.read(terminal, 65536))
                except OSError as error:
                    if error.errno != errno.EIO:
                        raise
            if interrupt and not sent_interrupt:
                streams = {"terminal": bytes(captured), "stderr": (logs / "stderr").read_bytes()
                           if (logs / "stderr").exists() else b""}
                if all(value.encode("utf-8") in streams[key] for key, value in interrupt.items()):
                    os.write(terminal, b"\x03")
                    sent_interrupt = True
            waited, status = os.waitpid(child, os.WNOHANG)
            if waited:
                reaped = True
                while select.select([terminal], [], [], 0)[0]:
                    try:
                        remaining = os.read(terminal, 65536)
                    except OSError as error:
                        if error.errno == errno.EIO:
                            break
                        raise
                    if not remaining:
                        break
                    captured.extend(remaining)
                if interrupt and not sent_interrupt:
                    raise AssertionError("CLI exited before interrupt conditions were observed")
                return (os.waitstatus_to_exitcode(status), (logs / "stdout").read_bytes(),
                        (logs / "stderr").read_bytes(), bytes(captured))
        raise AssertionError(f"CLI exceeded {timeout} seconds")
    finally:
        if not reaped:
            try:
                os.killpg(child, signal.SIGKILL)
            except ProcessLookupError:
                pass
            os.waitpid(child, 0)
        os.close(terminal)
        (logs / "terminal").write_bytes(captured)


def check_output(checks, streams):
    for check in checks:
        text = streams[check["stream"]].decode("utf-8", errors="replace")
        for value in check.get("contains", []):
            if value not in text:
                raise AssertionError(f"{check['stream']} lacks {value!r}")
        for value in check.get("absent", []):
            if value in text:
                raise AssertionError(f"{check['stream']} contains unexpected {value!r}")
        position = 0
        for value in check.get("ordered", []):
            found = text.find(value, position)
            if found < 0:
                raise AssertionError(f"{check['stream']} lacks ordered {value!r}")
            position = found + len(value)
        if "pattern" not in check:
            continue
        matches = list(re.finditer(check["pattern"], text, re.MULTILINE))
        if len(matches) != check.get("count", len(matches)) or ("count" not in check and not matches):
            raise AssertionError(f"{check['stream']} pattern {check['pattern']!r} matched {len(matches)} times")
        if "sum_equals" in check:
            totals = list(re.finditer(check["sum_equals"], text, re.MULTILINE))
            if len(totals) != 1 or not matches:
                raise AssertionError("numeric sum requires components and exactly one total")
            values = [float(match.group(1)) for match in matches]
            total = float(totals[0].group(1))
            if not all(math.isfinite(value) and value >= 0 for value in [*values, total]):
                raise AssertionError("numeric sum contains a negative or nonfinite value")
            if check.get("positive") and total <= 0:
                raise AssertionError("numeric total must be positive")
            if not math.isclose(sum(values), total, rel_tol=check.get("relative_tolerance", 0)):
                raise AssertionError(f"components sum to {sum(values)}, expected {total}")


def check_result(config, status, stdout, stderr, report_path, outputs, terminal=b""):
    if config["expect"] == "interrupted":
        if status != -signal.SIGINT:
            raise AssertionError(f"expected SIGINT, got exit {status}")
    else:
        check_report(config, status, report_path)
    check_output(config.get("checks", []), {"stdout": stdout, "stderr": stderr, "terminal": terminal})
    if "stdout" in config and stdout != config["stdout"].encode("utf-8"):
        raise AssertionError("stdout differs from the documented result")
    if "stdout_same_as" in config and stdout != outputs[config["stdout_same_as"]]:
        raise AssertionError(f"stdout differs from step {config['stdout_same_as']}")
    if "stdout_lines" in config and len(stdout.splitlines()) != config["stdout_lines"]:
        raise AssertionError(f"expected {config['stdout_lines']} output lines, got {len(stdout.splitlines())}")
    if "stdout_bytes_min" in config and len(stdout) < config["stdout_bytes_min"]:
        raise AssertionError(f"stdout shorter than {config['stdout_bytes_min']} bytes")
    if "stderr_empty" in config and (not stderr) != config["stderr_empty"]:
        raise AssertionError("stderr emptiness differs from expectation")


def check_report(config, status, report_path):
    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise AssertionError(f"CLI did not produce a valid report (exit {status})") from error
    if not isinstance(report, dict) or type(report.get("version")) is not int or report["version"] != 1:
        raise AssertionError("unsupported CLI report")
    outcome, code = EXPECTATIONS[config["expect"]]
    if report.get("outcome") != outcome or status != code:
        raise AssertionError(f"expected {outcome}/exit {code}, got {report.get('outcome')}/exit {status}")


def run_case(case, command, *, timeout=30, keep_failed=False):
    with work_directory(keep_failed) as root:
        directory = root / "source"
        directory.mkdir()
        config = case.config
        if config["scope"] == "module":
            name = config.get("name", "Test")
            parameters = "(" + config["parameters"] + ")" if "parameters" in config else ""
            (directory / "root.ref").write_text(f"\\module {name}{parameters};\n", encoding="utf-8")
        elif config["scope"] == "package" and not (directory / "ref.toml").exists():
            (directory / "ref.toml").write_text('[package]\nname = "test"\n', encoding="utf-8")
        if case.scenario:
            write_sources(case, directory, case.sources)
            steps = case.steps
        else:
            steps = [Step(config, case.line, case.sources)]
        outputs = {}
        for index, step in enumerate(steps):
            settings = {**config, **step.config}
            settings["env"] = {**config.get("env", {}), **step.config.get("env", {})}
            label = f"{case.label}/{step.config['id']}" if case.scenario else case.label
            logs = root / "logs" / str(index)
            try:
                for path in settings.get("remove", []):
                    target = contained(directory, path)
                    if target.is_dir():
                        shutil.rmtree(target)
                    else:
                        target.unlink()
                write_sources(case, directory, step.sources)
                default_entry = "root.ref" if config["scope"] == "module" else "."
                entry = contained(directory, settings.get("entry", default_entry))
                cwd = contained(directory, settings.get("cwd", "."))
                report_path = logs / "report.json"
                arguments = [*command, str(entry), "--report-json", str(report_path)]
                arguments += settings.get("args", [])
                environment = {key: value for key, value in os.environ.items()
                               if not key.startswith("REF_TYPE_PROFILE_")
                               and key not in {"RUST_LOG", "REF_TYPE_COMPACT_DIAGNOSTICS"}}
                environment.update(settings["env"])
                if settings.get("terminal"):
                    result = invoke_terminal(arguments, cwd, environment, settings.get("timeout", timeout),
                                             logs, settings.get("interrupt"))
                else:
                    result = (*invoke(arguments, cwd, environment, settings.get("timeout", timeout), logs), b"")
                check_result(settings, *result[:3], report_path, outputs, terminal=result[3])
                outputs[step.config["id"]] = result[1]
            except (AssertionError, OSError, ValueError) as error:
                details = []
                for stream in ("stdout", "stderr", "terminal"):
                    path = logs / stream
                    if path.exists():
                        details.append(f"{stream}:\n" + path.read_bytes()[-8000:].decode("utf-8", errors="replace"))
                raise AssertionError(f"{label} ({case.document}:{step.line}): {error}\n"
                                     + "\n".join(details)) from error


def discover(paths):
    documents = set()
    for path in paths:
        if path.is_dir():
            documents.update(item.resolve() for item in path.rglob("*.md") if item.name != "README.md")
        elif path.is_file():
            documents.add(path.resolve())
        else:
            raise DefinitionError(f"test path does not exist: {path}")
    cases = []
    for document in sorted(documents):
        found = parse_document(document)
        if not found:
            raise DefinitionError(f"{document}: no test definitions")
        cases.extend(found)
    if not cases:
        raise DefinitionError("no tests found")
    return cases


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path, help="Markdown files or directories (default: tests)")
    target = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target"))
    parser.add_argument("--command", default=str(target / "debug/cli"), help="checker command, shell-quoted arguments")
    parser.add_argument("--filter", action="append", default=[], help="case label substring or glob; repeatable")
    parser.add_argument("--list", action="store_true", help="validate and list test definitions")
    parser.add_argument("--keep-failed", action="store_true", help="retain generated files and logs on failure")
    parser.add_argument("--timeout", type=float, default=30, help="default timeout per invocation in seconds")
    args = parser.parse_args(argv)
    try:
        if not 0 < args.timeout < float("inf"):
            raise DefinitionError("timeout must be positive and finite")
        cases = discover(args.paths or [ROOT / "tests"])
        cases = [case for case in cases if not args.filter or any(
            pattern in case.label or fnmatch.fnmatchcase(case.label, pattern) for pattern in args.filter)]
        if not cases:
            raise DefinitionError("no tests matched the filter")
        command = shlex.split(args.command)
        if not command:
            raise DefinitionError("checker command is empty")
        executable = shutil.which(command[0])
        if not args.list and executable is None:
            raise DefinitionError(f"checker does not exist: {command[0]}; build or specify --command")
        if executable is not None:
            command[0] = str(Path(executable).resolve())
        if args.list:
            for case in cases:
                print(case.label)
            return 0
    except (DefinitionError, OSError, ValueError) as error:
        print(f"test definition error: {error}", file=sys.stderr)
        return 2
    failures = 0
    for index, case in enumerate(cases, 1):
        print(f"[{index}/{len(cases)}] {case.label}", flush=True)
        try:
            run_case(case, command, timeout=args.timeout, keep_failed=args.keep_failed)
        except (AssertionError, DefinitionError, OSError) as error:
            failures += 1
            print(f"FAIL: {error}", file=sys.stderr, flush=True)
    print(f"{len(cases) - failures} passed, {failures} failed")
    return int(failures != 0)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)
