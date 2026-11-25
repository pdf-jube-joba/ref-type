import hashlib
import os
from pathlib import Path
import tomllib


def packages(paths):
    ordered, visited, visiting = [], set(), set()

    def visit(path):
        path = path.resolve()
        if path in visiting:
            raise ValueError(f"cyclic package dependency: {path}")
        if path in visited:
            return
        visiting.add(path)
        manifest = tomllib.loads((path / "ref.toml").read_text(encoding="utf-8"))
        if "package" in manifest:
            for dependency in manifest.get("dependencies", {}).values():
                visit(path / dependency["path"])
            ordered.append(path)
        for member in manifest.get("workspace", {}).get("packages", []):
            member = (path / member).resolve()
            if member != path:
                visit(member)
        visiting.remove(path)
        visited.add(path)

    for path in paths:
        visit(path)
    return ordered


def source_digest(path):
    roots = packages([path]) if path.is_dir() and (path / "ref.toml").exists() else [path.parent]
    files = set()
    for root in roots:
        for directory, children, names in os.walk(root):
            children[:] = [name for name in children if name != "refcache"]
            files.update(Path(directory) / name for name in names
                         if name.endswith(".ref") or name == "ref.toml")
    digest = hashlib.sha256()
    for file in sorted(files):
        digest.update(str(file).encode() + b"\0" + file.read_bytes() + b"\0")
    return digest.hexdigest()


def package(root, name, dependencies, body):
    path = root / name
    (path / "src").mkdir(parents=True, exist_ok=True)
    manifest = f'[package]\nname = "{name}"\n[dependencies]\n'
    manifest += "".join(f'{dep} = {{path = "../{dep}"}}\n' for dep in dependencies)
    (path / "ref.toml").write_text(manifest, encoding="utf-8")
    (path / "src/root.ref").write_text(body, encoding="utf-8")
    return path


def definitions(width, carrier="A"):
    return "\n".join(rf"\definition id{i}[x: {carrier}]: {carrier} := x;" for i in range(width))


def namespace(root, width, imports, local=False):
    lines = [rf"\module Source(A: \Set) {{ {definitions(width)} }}",
             r"\inductive Unit: \Set := | unit: Unit;"]
    for i in range(imports):
        if local:
            lines.append(rf"\definition use{i}[A: \Set][x: A]: A := Source[A := A].id0 x;")
        elif i % 2:
            lines.extend([rf"\import Source[A := Unit -> Unit] \as S{i};",
                          rf"\definition use{i}[x: Unit]: Unit := S{i}.id0 (\fun (y: Unit) => y) x;"])
        else:
            lines.extend([rf"\import Source[A := Unit] \as S{i};",
                          rf"\definition use{i}: Unit := S{i}.id0 Unit::unit;"])
    return package(root, "namespaces", [], "\\module Main {\n" + "\n".join(lines) + "\n}")


def chain(root, size, width):
    previous = None
    for i in range(size):
        name = f"p{i}"
        lines = [r"\module Core {"]
        if previous:
            lines.append(rf"\import {previous}.Core[] \as D;")
        for j in range(width):
            body = rf"D.p{j}" if previous else r"\forall (P: \Prop) -> P -> P"
            lines.append(rf"\definition p{j}: \Prop := {body};")
        lines.append("}")
        entry = package(root, name, [previous] if previous else [], "\n".join(lines))
        previous = name
    return entry


def consumers(root, size, width):
    package(root, "base", [], rf"\module Core(A: \Set) {{ {definitions(width)} }}")
    names = []
    for i in range(size):
        name = f"user{i}"
        names.append(name)
        package(root, name, ["base"], r"\module Use(A: \Set) { \import base.Core[A := A] \as B; \definition id[x: A]: A := B.id0 x; }")
    (root / "ref.toml").write_text("[workspace]\npackages = [" + ", ".join(f'"{name}"' for name in names) + "]\n", encoding="utf-8")
    return root


def independent(root, size, width):
    groups = []
    for i in range(size):
        declarations = []
        for j in range(width):
            declarations.extend([
                rf"\inductive T{j}: \Set := | zero: T{j};",
                rf"\definition Carrier{j}: \Set := T{j};",
                rf"\definition id{j}[x: T{j}]: T{j} := x;",
                rf"\definition value{j}: T{j} := id{j} T{j}::zero;",
            ])
        groups.append(rf"\module G{i} {{ " + "\n".join(declarations) + " }")
    reads = []
    for i in range(size):
        reads.extend([
            rf"\import \root.G{i}[] \as G{i};",
            rf"\definition value{i}: G{i}.Carrier0 := G{i}.value0;",
        ])
    groups.append(r"\module ReadBack { " + "\n".join(reads) + " }")
    return package(root, "groups", [], "\n".join(groups))
