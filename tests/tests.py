#!/usr/bin/env python3
"""Check acceptance and rejection of documented sources using Python 3.11+ and its standard library."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import fnmatch
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile

from documents import EXPECTATIONS, ROOT, DefinitionError, Step, discover, relative_path


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


def invoke(command, cwd, timeout, logs):
    logs.mkdir(parents=True, exist_ok=True)
    (logs / "command").write_text(shlex.join(command) + "\n", encoding="utf-8")
    # File redirection drains both outputs without a pipe-buffer deadlock.
    with (logs / "stdout").open("wb") as stdout, (logs / "stderr").open("wb") as stderr:
        child = subprocess.Popen(command, cwd=cwd, stdin=subprocess.DEVNULL,
                                 stdout=stdout, stderr=stderr, start_new_session=os.name == "posix")
        try:
            child.wait(timeout=timeout)
        except subprocess.TimeoutExpired as error:
            raise AssertionError(f"checker exceeded {timeout} seconds") from error
        finally:
            terminate(child)
    return child.returncode


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
        for index, step in enumerate(steps):
            settings = {**config, **step.config}
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
                status = invoke([*command, str(entry)], directory, timeout, logs)
                if status != EXPECTATIONS[settings["expect"]]:
                    raise AssertionError(f"expected {settings['expect']}, got exit {status}")
            except (AssertionError, OSError, ValueError) as error:
                details = []
                for stream in ("stdout", "stderr"):
                    path = logs / stream
                    if path.exists():
                        details.append(f"{stream}:\n" + path.read_bytes()[-8000:].decode("utf-8", errors="replace"))
                raise AssertionError(f"{label} ({case.document}:{step.line}): {error}\n"
                                     + "\n".join(details)) from error


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
