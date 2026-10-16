#!/usr/bin/env python3
"""Execute documented CLI acceptance tests using Python 3.11+ and its standard library."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import dataclass, field
import fnmatch
import json
import os
from pathlib import Path, PurePosixPath
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
SCOPES = {"module", "package", "workspace"}
EXPECTATIONS = {"accept": 0, "reject": 1}
COMMON = {"id", "expect", "cache", "args", "env", "entry", "cwd", "timeout",
          "remove", "cache_dir", "files"}
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
    outcomes = EXPECTATIONS
    if expectation and (not isinstance(config.get("expect"), str) or config["expect"] not in outcomes):
        raise DefinitionError(f"{context}: expect must be accept or reject")
    if "expect" in config and (not isinstance(config["expect"], str) or config["expect"] not in outcomes):
        raise DefinitionError(f"{context}: expect must be accept or reject")
    if "cache" in config and (not isinstance(config["cache"], str) or config["cache"] not in {"reused", "unused"}):
        raise DefinitionError(f"{context}: cache must be reused or unused")
    for key in ("args", "remove"):
        if key in config and (not isinstance(config[key], list)
                              or not all(isinstance(item, str) for item in config[key])):
            raise DefinitionError(f"{context}: {key} must be an array of strings")
    for key in ("entry", "cwd"):
        if key in config:
            relative_path(config[key], context)
    if "cache_dir" in config and config["cache_dir"] != "default":
        relative_path(config["cache_dir"], context)
    for path in config.get("remove", []):
        if str(relative_path(path, context)) == ".":
            raise DefinitionError(f"{context}: remove must name a file or subdirectory")
    for key in ("name", "parameters"):
        if key in config and not isinstance(config[key], str):
            raise DefinitionError(f"{context}: {key} must be a string")
    if "name" in config and not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", config["name"]):
        raise DefinitionError(f"{context}: invalid module name")
    if "timeout" in config and (type(config["timeout"]) not in (int, float)
                                or not 0 < config["timeout"] < float("inf")):
        raise DefinitionError(f"{context}: timeout must be a positive finite number")
    files = config.get("files", [])
    if not isinstance(files, list):
        raise DefinitionError(f"{context}: files must be an array of tables")
    for item in files:
        if not isinstance(item, dict) or item.keys() - {"path", "same_as", "nonempty"}:
            raise DefinitionError(f"{context}: invalid file expectation")
        relative_path(item.get("path"), context)
        if "same_as" in item and not isinstance(item["same_as"], str):
            raise DefinitionError(f"{context}: same_as must name an earlier step")
        if "nonempty" in item and type(item["nonempty"]) is not bool:
            raise DefinitionError(f"{context}: nonempty must be a boolean")
    environment = config.get("env", {})
    if not isinstance(environment, dict) or not all(
        isinstance(key, str) and key and "=" not in key and "\0" not in key
        and isinstance(value, str) and "\0" not in value
        for key, value in environment.items()
    ):
        raise DefinitionError(f"{context}: env must map environment names to strings")
    for arg in config.get("args", []):
        if arg.split("=", 1)[0] in {"--report-json", "--cache-dir", "--worker"}:
            raise DefinitionError(f"{context}: {arg} is managed by the runner")


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
                if scenario and ("expect" in config or "cache" in config):
                    raise DefinitionError(f"{context}: put expectations on scenario steps")
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
        snapshots = {}
        for item in case.steps if case.scenario else [Step(case.config, case.line, case.sources)]:
            if item.config["id"] in previous:
                raise DefinitionError(f"{document}:{item.line}: duplicate step id")
            settings = {**case.config, **item.config}
            for entry in settings.get("files", []):
                if "same_as" in entry and entry["path"] not in snapshots.get(entry["same_as"], set()):
                    raise DefinitionError(f"{document}:{item.line}: same_as requires an earlier snapshot of the path")
            snapshots[item.config["id"]] = {entry["path"] for entry in settings.get("files", [])}
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
    return child.returncode


def check_result(config, status, report_path):
    code = EXPECTATIONS[config["expect"]]
    if status != code:
        raise AssertionError(f"expected {config['expect']}/exit {code}, got exit {status}")
    if "cache" not in config:
        return
    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise AssertionError("CLI did not produce a valid cache report") from error
    cache = report.get("cache") if isinstance(report, dict) else None
    reused = cache.get("verification_reused") if isinstance(cache, dict) else None
    if type(reused) is not bool:
        raise AssertionError("CLI report lacks boolean cache.verification_reused")
    if reused != (config["cache"] == "reused"):
        raise AssertionError(f"expected cache {config['cache']}, got {cache}")


def check_files(expectations, directory, snapshots):
    current = {}
    for item in expectations:
        path = contained(directory, item["path"])
        if not path.exists():
            raise AssertionError(f"snapshot path does not exist: {item['path']}")
        contents = {str(file.relative_to(path)): file.read_bytes()
                    for file in path.rglob("*") if file.is_file()} if path.is_dir() else {".": path.read_bytes()}
        if "nonempty" in item and bool(contents) != item["nonempty"]:
            raise AssertionError(f"snapshot has unexpected file count: {item['path']}")
        if "same_as" in item and contents != snapshots[item["same_as"]][item["path"]]:
            raise AssertionError(f"files at {item['path']} differ from step {item['same_as']}")
        current[item["path"]] = contents
    return current


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
        snapshots = {}
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
                arguments = [*command, str(entry)]
                if "cache" in settings:
                    arguments += ["--report-json", str(report_path)]
                cache = settings.get("cache_dir", "cache")
                if cache != "default":
                    cache_path = contained(root, cache)
                    arguments += ["--cache-dir", str(cache_path)]
                arguments += settings.get("args", [])
                environment = {key: value for key, value in os.environ.items()
                               if not key.startswith("REF_TYPE_PROFILE_")
                               and key not in {"RUST_LOG", "REF_TYPE_COMPACT_DIAGNOSTICS", "REF_TYPE_CACHE_SESSION"}}
                environment.update(settings["env"])
                status = invoke(arguments, cwd, environment, settings.get("timeout", timeout), logs)
                check_result(settings, status, report_path)
                snapshots[step.config["id"]] = check_files(settings.get("files", []), directory, snapshots)
            except (AssertionError, OSError, ValueError) as error:
                details = []
                for stream in ("stdout", "stderr"):
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
