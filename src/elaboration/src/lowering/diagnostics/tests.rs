use super::*;
use crate::{
    elaborator::GlobalEnvironment,
    raw::{environment::ModuleItem, ids::DefId},
};

fn environment(source: &str) -> GlobalEnvironment {
    let modules = syntax::parse::str_parse_modules(source).unwrap();
    let mut global = GlobalEnvironment::default();
    global.add_modules_to_root(&modules).unwrap();
    global
}

fn definition(global: &GlobalEnvironment, module: &str, name: &str) -> DefId {
    let raw = global.crate_env();
    let module = raw
        .module(raw.root_module())
        .children()
        .iter()
        .copied()
        .find(|&id| raw.module(id).name() == module)
        .unwrap();
    let ModuleItem::Definition { definition, .. } = raw.module(module).item(name).unwrap() else {
        panic!("definition")
    };
    *definition
}

fn mismatch(global: &GlobalEnvironment, module: &str, actual: &str, expected: &str) -> String {
    let env = global.kernel_env();
    let id = global.crate_env().kernel_definitions.borrow()[&definition(global, module, actual)];
    let actual = env.definition(id).unwrap();
    let expected = env
        .definition(
            global.crate_env().kernel_definitions.borrow()[&definition(global, module, expected)],
        )
        .unwrap();
    let arguments = actual
        .context
        .iter()
        .enumerate()
        .map(|(i, _)| env.arena().bound(actual.context.len() - i - 1))
        .collect();
    let term = env.reference(id, arguments).unwrap();
    let error = kernel::check::Checker::new(
        &env,
        &mut kernel::metavariables::MetaContext::new(),
        actual.context.clone(),
    )
    .check(term, expected.ty)
    .unwrap_err();
    format_error(global.crate_env(), &error)
}

#[test]
fn named_types_survive_conversion_failure() {
    let global = environment(
        r"\module M {
        \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
        \inductive Bool: \Set := | no: Bool | yes: Bool;
        \definition N: \Set := Nat;
        \definition n: N := Nat::zero;
        \definition b: Bool := Bool::yes;
        \definition f: (N -> N) -> N := \fun (g: N -> N) => g n;
        \definition g: Bool -> Bool := \fun (x: Bool) => x;
    }",
    );
    let error = mismatch(&global, "M", "n", "b");
    assert!(
        error.contains("inferred: \\root.M.N\nexpected: \\root.M.Bool"),
        "{error}"
    );
    let error = mismatch(&global, "M", "f", "g");
    assert!(
        error.contains("inferred: (\\root.M.N -> \\root.M.N) -> \\root.M.N"),
        "{error}"
    );
    assert!(
        error.contains("expected: \\root.M.Bool -> \\root.M.Bool"),
        "{error}"
    );
}

#[test]
fn constructors_and_application_precedence_are_readable() {
    let global = environment(
        r"\module M {
        \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
        \definition P (n: Nat): \Prop := n = Nat::zero;
        \definition left: P (Nat::succ Nat::zero) -> P Nat::zero :=
            \fun (p: P (Nat::succ Nat::zero)) => \refl(Nat::zero);
        \definition right: P Nat::zero := \refl(Nat::zero);
    }",
    );
    let error = mismatch(&global, "M", "left", "right");
    assert!(error.contains("inferred: \\root.M.P (\\root.M.Nat::succ \\root.M.Nat::zero) -> \\root.M.P \\root.M.Nat::zero"), "{error}");
}

#[test]
fn program_types_use_surface_arrows_and_names() {
    let global = environment(
        r"\module M {
        \inductive A: \VType := | a: A;
        \inductive B: \VType := | b: B;
        \definition f: A ~> \F(A) := \cfun (x: A) => \return x;
        \definition g: B ~> \F(B) := \cfun (x: B) => \return x;
    }",
    );
    let error = mismatch(&global, "M", "f", "g");
    assert!(
        error.contains("inferred: \\root.M.A ~> \\F(\\root.M.A)"),
        "{error}"
    );
    assert!(
        error.contains("expected: \\root.M.B ~> \\F(\\root.M.B)"),
        "{error}"
    );
}

#[test]
fn binders_are_renamed_without_capturing_context_variables() {
    use kernel::{
        environment::Environment,
        sort::{BaseSort, Sort},
    };
    let mut raw = CrateEnv::new();
    let a_name = raw.intern("A");
    let x_name = raw.intern("x");
    let env = Environment::new();
    let arena = env.arena();
    let kind = arena.sort(Sort::Base(BaseSort::Set(0)));
    let a_at_prefix = arena.bound(0);
    let a = arena.bound(1);
    let x = arena.bound(0);
    let outer_x = arena.bound(1);
    let equality = arena.alloc(Node::Equal {
        left: outer_x,
        right: x,
    });
    let expected = arena.alloc(Node::Product {
        var: x_name,
        domain: a,
        body: equality,
    });
    let context = vec![
        Binding {
            var: a_name,
            ty: kind,
        },
        Binding {
            var: x_name,
            ty: a_at_prefix,
        },
    ];
    let error = kernel::check::Checker::new(
        &env,
        &mut kernel::metavariables::MetaContext::new(),
        context,
    )
    .check(x, expected)
    .unwrap_err();
    let text = format_error(&raw, &error);
    assert!(
        text.contains("inferred: A\nexpected: \\forall (x1: A) -> x = x1\ncontext: A: \\Set, x: A"),
        "{text}"
    );
}

#[test]
fn instantiated_module_types_remain_distinguishable() {
    let global = environment(
        r"\module Template(A: \Set) {
        \inductive Wrapped: \Set := | wrap: A -> Wrapped;
    }
    \module M {
        \inductive A: \Set := | a: A;
        \inductive B: \Set := | b: B;
        \import \root.Template[A := A] \as TA;
        \import \root.Template[A := B] \as TB;
        \definition a: TA.Wrapped := TA.Wrapped::wrap A::a;
        \definition b: TB.Wrapped := TB.Wrapped::wrap B::b;
    }",
    );
    let error = mismatch(&global, "M", "a", "b");
    assert!(error.contains(r"Template.Wrapped[\root.M.A]"), "{error}");
    assert!(error.contains(r"Template.Wrapped[\root.M.B]"), "{error}");
    let inferred = error
        .lines()
        .find(|line| line.starts_with("inferred:"))
        .unwrap();
    let expected = error
        .lines()
        .find(|line| line.starts_with("expected:"))
        .unwrap();
    assert_ne!(
        inferred.strip_prefix("inferred: "),
        expected.strip_prefix("expected: ")
    );
    assert!(!error.contains("ind#"), "{error}");
}

#[test]
fn parameterized_inductives_use_brackets_before_constructor_names() {
    let global = environment(
        r"\module M {
        \inductive Nat: \Set := | zero: Nat;
        \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
        \definition p: List[Nat]::nil = List[Nat]::nil := \refl(List[Nat]::nil);
        \definition q: Nat::zero = Nat::zero := \refl(Nat::zero);
    }",
    );
    let error = mismatch(&global, "M", "p", "q");
    assert!(
        error
            .contains(r"inferred: \root.M.List[\root.M.Nat]::nil = \root.M.List[\root.M.Nat]::nil"),
        "{error}"
    );
}

#[test]
fn query_boundary_formats_the_structured_kernel_error() {
    use crate::raw::{environment::DefinedConstant, exp::ExpNode};
    let global = environment(
        r"\module M {
        \inductive Nat: \Set := | zero: Nat;
        \inductive Bool: \Set := | yes: Bool;
        \definition n: Nat := Nat::zero;
        \definition b: Bool := Bool::yes;
    }",
    );
    let raw = global.crate_env();
    let n = definition(&global, "M", "n");
    let b = definition(&global, "M", "b");
    let term = raw.arena().alloc(ExpNode::DefinedConstant(n));
    let DefinedConstant::Pts { ty, .. } = *raw.definition(b) else {
        panic!("logical term")
    };
    let mut kernel = kernel::environment::Environment::new();
    let error = crate::lowering::Lowerer::new(raw, &mut kernel)
        .check_query(&vec![], n.module, term, ty)
        .unwrap_err();
    assert!(
        error
            .render(raw)
            .contains("inferred: \\root.M.Nat\nexpected: \\root.M.Bool"),
        "{error}"
    );
}

#[test]
fn choice_equality_rendering_roundtrips() {
    let prefix = r"\module M(A: \Set, a: A, unique: \forall (x, y: A) -> x = y) {
        \definition chosen: A :=
            \choice A \by { existence: \exact(a, A), uniqueness: unique };
        \definition proof: a = chosen := ";
    let global = environment(&format!(
        "{prefix}\\choiceeq a \\of A \\by {{ existence: \\exact(a, A), uniqueness: unique }}; }}"
    ));
    let raw = global.crate_env();
    let env = global.kernel_env();
    let id = raw.kernel_definitions.borrow()[&definition(&global, "M", "proof")];
    let proof = env.definition(id).unwrap();
    let rendered = format_expression(raw, &proof.context, proof.body);
    assert!(rendered.contains(r"\choiceeq (a) \of (A)"), "{rendered}");
    assert!(rendered.contains(r"existence: \exact(a, A)"), "{rendered}");
    environment(&format!("{prefix}{rendered}; }}"));
}
