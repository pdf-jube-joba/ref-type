import hashlib
import os
from pathlib import Path
import re
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


def external_modules(text, parent=()):
    pattern = r'/\*|\*/|"[^"\n]*"|\\[A-Za-z][A-Za-z0-9-]*|\\[^A-Za-z0-9\s(){}$\[\]_,]+|[A-Za-z][A-Za-z0-9_]*|\S'
    scopes = [parent]
    comment_depth = 0
    module = None
    name = None
    header_depth = 0
    for match in re.finditer(pattern, text):
        token = match.group()
        if token == "/*":
            comment_depth += 1
        elif token == "*/":
            comment_depth = max(0, comment_depth - 1)
        elif comment_depth:
            continue
        elif module is not None:
            if name is None:
                if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", token):
                    module = None
                    continue
                name = token
            elif header_depth == 0 and token in ("{", ";"):
                module_path = (*module, name)
                if token == ";":
                    yield module_path
                else:
                    scopes.append(module_path)
                module = None
            elif token in ("(", "[", "{"):
                header_depth += 1
            elif token in (")", "]", "}"):
                header_depth -= 1
        elif token == "\\module" and scopes[-1] is not None:
            module, name, header_depth = scopes[-1], None, 0
        elif token in ("(", "[", "{"):
            scopes.append(None)
        elif token in (")", "]", "}") and len(scopes) > 1:
            scopes.pop()


def source_digest(path):
    path = path.resolve()
    base = path if path.is_dir() else path.parent
    files = {}

    def add_modules(entry):
        source_root = entry.parent
        visited = set()

        def visit(file, parent):
            identity = file.resolve()
            if identity in visited:
                return
            visited.add(identity)
            content = file.read_bytes()
            files[os.path.relpath(file, base)] = content
            for module in external_modules(content.decode("utf-8"), parent):
                visit(source_root.joinpath(*module).with_suffix(".ref"), module)

        visit(entry, ())

    if path.is_dir():
        files["ref.toml"] = (path / "ref.toml").read_bytes()
        for root in packages([path]):
            files[os.path.relpath(root / "ref.toml", base)] = (root / "ref.toml").read_bytes()
            add_modules(root / "src/root.ref")
    else:
        add_modules(path)
    digest = hashlib.sha256()
    for name, content in sorted(files.items()):
        digest.update(name.encode() + b"\0" + content + b"\0")
    return digest.hexdigest()


def package(root, name, dependencies, body):
    path = root / name
    (path / "src").mkdir(parents=True, exist_ok=True)
    manifest = f'[package]\nname = "{name}"\n[dependencies]\n'
    manifest += "".join(f'{dep} = {{path = "../{dep}"}}\n' for dep in dependencies)
    (path / "ref.toml").write_text(manifest, encoding="utf-8")
    (path / "src/root.ref").write_text(body, encoding="utf-8")
    return path
