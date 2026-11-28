from common.sources import package


def transport(size):
    points = ", ".join(f"p{i}" for i in range(size + 1))
    edges = "".join(f"[e{i}: p{i} = p{i+1}]" for i in range(size))
    term = "seed"
    for i in range(size):
        term = (rf"\idelim p{i} = p{i+1} \with at: A => F at "
                rf"\by {{ base: {term}, equality: e{i} }}")
    return (rf"\definition carry[A: \Set][F: A -> \Set][{points}: A]{edges}"
            rf"[seed: F p0]: F p{size} := {term};")


def constructor_equations(size):
    constructors = "\n".join(f"| tag{i}: Code" for i in range(size))
    arms = "\n".join(f"| tag{i}: Code::tag{(i + 1) % size}" for i in range(size))
    laws = "\n".join(
        rf"\definition law{i}: rotate Code::tag{i} = Code::tag{(i + 1) % size} "
        rf":= \refl(Code::tag{(i + 1) % size});" for i in range(size))
    return (rf"\inductive Code: \Set := {constructors};" + "\n"
            + rf"\definition rotate[c: Code]: Code := \match c \in Code "
            + rf"\return (\fun (_: Code) => Code) \with {{ {arms} }};" + "\n" + laws)


def program_binds(size):
    binds = "\n".join(rf"\bind v{i+1}: A <- (\force step) v{i} \then" for i in range(size))
    return (rf"\definition pipeline[A: \VType][step: \U(A ~> \F(A))][v0: A]: \F(A) := "
            rf"\program {{ {binds} \return v{size} }};")


def refinement(size):
    lines = [r"\definition Layer0[A: \Set]: \Set := A;"]
    for i in range(size):
        base = f"(Layer{i} A)"
        subset = f"(Subset{i} A)"
        lines.extend([
            rf"\definition Subset{i}[A: \Set]: \Pow {base} := {{ x: {base} \where x = x }};",
            rf"\definition Layer{i+1}[A: \Set]: \Set := \Cast[{base}] {subset};",
            rf"\definition wrap{i}[A: \Set][x: {base}]: Layer{i+1} A := "
            rf"\into[{base}](x, {subset}) \by {{ \refl(x) }};",
            rf"\definition certificate{i}[A: \Set][x: Layer{i+1} A]: \In[{base}] {subset} x := "
            rf"\bysub({base}, {subset}, x);",
        ])
    lines.append(rf"\definition forget[A: \Set][x: Layer{size} A]: A := x;")
    return "\n".join(lines)


def witnesses(size):
    steps = "\n".join(rf"\takefrom x{i+1}: A \by next x{i} \then" for i in range(size))
    return (rf"\definition follow[A: \Set][x0: A][next: A -> \exists A]: \exists A := "
            rf"\block {{ {steps} \return \exact(x{size}, A) }};")


def recursive_notation(size):
    arguments = " ".join("seed" for _ in range(size))
    return (r"\macro pipeline($f, $first, ..tail) := \tmatch tail {"
            r" | () => $first"
            r" | ($arg, ..more) => pipeline!{$f {$f $first $arg} ..more} };" + "\n"
            + rf"\definition fold[A: \Set][combine: A -> A -> A][seed: A]: A := "
            + rf"pipeline!{{combine {arguments}}};")


def step_motive(size):
    declarations = []
    for i in range(size):
        declarations.extend([
            rf"\definition goal{i}[A: \Set][P: A -> \Prop]: \RunStep[A, A] -> \Prop := "
            rf"\step-match s: \RunStep[A, A] \return \Prop \with {{ "
            rf"| \continue a: P a | \finish b: b = b }};",
            rf"\definition prove{i}[A: \Set][P: A -> \Prop][h: \forall (a: A) -> P a]: "
            rf"\forall (s: \RunStep[A, A]) -> goal{i} A P s := "
            rf"\step-match s: \RunStep[A, A] \return goal{i} A P s \with {{ "
            rf"| \continue a: h a | \finish b: \refl(b) }};",
        ])
    return "\n".join(declarations)


def focused_files(root, size):
    modules = [rf"\module Side{i};" for i in range(size)]
    modules.append(r"\module Focus;")
    entry = package(root, "sample", [], "\n".join(modules))
    for i in range(size):
        (entry / f"src/Side{i}.ref").write_text(
            rf"\definition id{i}[A: \Set][x: A]: A := x;", encoding="utf-8")
    (entry / "src/Focus.ref").write_text(r"\definition choose[P: \Prop]: \Prop := P;", encoding="utf-8")
    return entry
