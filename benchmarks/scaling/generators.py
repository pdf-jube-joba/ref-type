from common.sources import package


def workspace(root, names):
    (root / "ref.toml").write_text("[workspace]\npackages = [" + ", ".join(f'"{name}"' for name in names) + "]\n", encoding="utf-8")
    return root


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
    return workspace(root, names)


def independent(root, size, width, *, name="groups"):
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
    return package(root, name, [], "\n".join(groups))


def checkpoint_disk(root, size, width):
    names = [f"p{i}" for i in range(size)]
    for name in names:
        independent(root, 32, width, name=name)
    return workspace(root, names)


def layered(root, size, width):
    def layer(name, dependencies):
        lines = [r"\module Core {"]
        for i, dependency in enumerate(dependencies):
            lines.append(rf"\import {dependency}.Core[] \as Dep{i};")
        for j in range(width):
            if dependencies:
                parts = " -> ".join(f"Dep{i}.p{j}" for i in range(len(dependencies)))
                value = f"{parts} -> Dep0.p{j}"
            else:
                value = r"\forall (P: \Prop) -> P -> P"
            lines.append(rf"\definition p{j}: \Prop := {value};")
        lines.append("}")
        package(root, name, dependencies, "\n".join(lines))

    bs = [f"b{i}" for i in range(size)]
    cs = [f"c{i}" for i in range(size)]
    layer("a", [])
    for name in bs:
        layer(name, ["a"])
    for name in cs:
        layer(name, bs)
    layer("d", cs)
    return workspace(root, ["a", *bs, *cs, "d"])
