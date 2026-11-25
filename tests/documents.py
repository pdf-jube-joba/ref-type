from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
import re
import shlex
import tomllib

ROOT = Path(__file__).resolve().parents[1]
SCOPES = {"module", "package", "workspace"}
EXPECTATIONS = {"accept": 0, "reject": 1}
COMMON = {"id", "expect", "entry", "remove"}
CONFIG = COMMON | {"scope", "name", "parameters"}


class DefinitionError(ValueError):
    pass


@dataclass
class Source:
    path: str | None
    text: str


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
    if expectation and "expect" not in config:
        raise DefinitionError(f"{context}: expect must be accept or reject")
    if "expect" in config and (not isinstance(config["expect"], str) or config["expect"] not in EXPECTATIONS):
        raise DefinitionError(f"{context}: expect must be accept or reject")
    if "entry" in config:
        relative_path(config["entry"], context)
    if "remove" in config:
        if not isinstance(config["remove"], list):
            raise DefinitionError(f"{context}: remove must be an array of paths")
        for path in config["remove"]:
            if str(relative_path(path, context)) == ".":
                raise DefinitionError(f"{context}: remove must name a file or subdirectory")
    for key in ("name", "parameters"):
        if key in config and not isinstance(config[key], str):
            raise DefinitionError(f"{context}: {key} must be a string")
    if "name" in config and not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", config["name"]):
        raise DefinitionError(f"{context}: invalid module name")


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
                if key != "file" or key in attributes:
                    raise DefinitionError(f"{context}: invalid source attribute {key}")
                attributes[key] = value
            path = attributes.get("file")
            if path is None and (tokens[0] != "ref" or current.config["scope"] != "module"):
                raise DefinitionError(f"{context}: this source block requires file=")
            if path is not None:
                if str(relative_path(path, context)) == ".":
                    raise DefinitionError(f"{context}: file must name a file")
            (step.sources if step else current.sources).append(Source(path, body))
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
            paths = [source.path for source in item.sources]
            if len(paths) != len(set(paths)):
                raise DefinitionError(f"{document}:{item.line}: source file written twice in one step")
            previous.add(item.config["id"])
        paths = [source.path for source in case.sources]
        if len(paths) != len(set(paths)):
            raise DefinitionError(f"{context}: initial source file written twice")
    return cases


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
