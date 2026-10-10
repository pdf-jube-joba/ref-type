use elaboration::Checker;
fn check(source: &str) -> Result<(), String> {
    let modules = syntax::parse::str_parse_modules(source).map_err(|e| e.to_string())?;
    let project = resolve::resolve(&modules).map_err(|e| e.to_string())?;
    Checker::default()
        .check(&project)
        .map(|_| ())
        .map_err(|e| e.to_string())
}

#[test]
fn forward_uses_specialize_two_equalities_with_aliases() {
    check(
        r#"\module Consumer(
      A: \Set, a: A,
      leftEq: A -> A -> \Prop, leftRefl: \forall (x: A) -> leftEq x x,
      rightEq: A -> A -> \Prop, rightRefl: \forall (x: A) -> rightEq x x
    ) {
      \module Child {
        \definition leftProof: leftEq a a := refl_left!{a};
        \definition rightProof: rightEq a a := refl_right!{a};
      }
      \use \root.Equality[A := A, eq := leftEq, refl := leftRefl]::reflexive \as refl_left;
      \use \root.Equality[A := A, eq := rightEq, refl := rightRefl]::reflexive \as refl_right;
    }
    \module Equality(A: \Set, eq: A -> A -> \Prop, refl: \forall (x: A) -> eq x x) {
      \macro reflexive($x) := refl $x;
    }"#,
    )
    .unwrap();
}

#[test]
fn lexical_shadowing_and_definition_site_internal_references() {
    check(
        r#"\module M(A: \Set, a, b: A) {
      \definition before: a = a := \refl(value!{});
      \macro wrapped() := value!{};
      \macro value() := a;
      \module Child {
        \definition local: b = b := \refl(value!{});
        \definition captured: a = a := \refl(wrapped!{});
        \macro value() := b;
        \module Grandchild { \definition local: b = b := \refl(value!{}); }
      }
      \module Sibling { \definition local: a = a := \refl(value!{}); }
    }"#,
    )
    .unwrap();
}

#[test]
fn forward_mutual_recursion_and_aliased_self_recursion() {
    check(
        r#"\module Templates(A: \Set, a: A) {
      \macro first(..xs) := \tmatch xs { | () => a | ("next", ..rest) => second!{..rest} };
      \macro second(..xs) := \tmatch xs { | () => a | ("next", ..rest) => first!{..rest} };
    }
    \module Consumer(A: \Set, a: A) {
      \definition law: a = a := \refl(start!{"next" "next" "next"});
      \use \root.Templates[A := A, a := a]::first \as start;
    }"#,
    )
    .unwrap();
}

#[test]
fn late_use_arguments_keep_their_declaration_position() {
    check(
        r#"\module Templates(A: \Set, a: A) { \macro value() := a; }
    \module Consumer(A: \Set, a: A) {
      \module Child { \definition proof: a = a := \refl(value!{}); }
      \definition later: A := a;
      \use \root.Templates[A := A, a := later]::value;
    }"#,
    )
    .unwrap();
    assert!(
        check(
            r#"\module M(A: \Set, a: A) {
      \module Child { \definition wrong: A := later; }
      \definition later: A := a;
    }"#
        )
        .is_err()
    );
}

#[test]
fn duplicate_names_and_instantiation_cycles_have_diagnostics() {
    for body in [
        r"\macro value() := a; \macro value() := a;",
        r"\macro value() := a; \use \root.T[A := A, a := a]::value;",
        r"\use \root.T[A := A, a := a]::value; \use \root.T[A := A, a := a]::value;",
    ] {
        let source = format!(
            r"\module T(A: \Set, a: A) {{ \macro value() := a; }} \module M(A: \Set, a: A) {{ {body} }}"
        );
        let error = check(&source).unwrap_err();
        assert!(error.contains("Duplicate macro 'value'"), "{error}");
    }
    let error = check(
        r#"\module T(A: \Set, a: A) { \macro value() := a; }
      \module M(A: \Set, a: A) { \use \root.T[A := A, a := value!{}]::value; }"#,
    )
    .unwrap_err();
    assert!(
        error.contains("Cyclic") && error.contains(" -> "),
        "{error}"
    );
}

#[test]
fn import_alias_and_parameterized_child_use() {
    check(
        r#"\module T(A: \Set, a: A) {
      \macro value() := a;
      \module Child(b: A) { \macro value() := b; }
    }
    \module M(A: \Set, a: A) {
      \definition law: a = a := \refl(parent!{});
      \definition childLaw: a = a := \refl(child!{});
      \import \root.T[A := A, a := a] \as T;
      \use T::value \as parent;
      \use T::Child[b := a]::value \as child;
    }"#,
    )
    .unwrap();
}

#[test]
fn math_shadowing_priority_and_parent_parameter_scope() {
    check(
        r"\module M(A: \Set, a, b: A) {
      \macro carrier() := A;
      \definition before: a = a := \refl(\(a + b\));
      \math-macro plus($x, \+, $y) := $x;
      \module Child(x: carrier!{}) {
        \definition nearest: b = b := \refl(\(a + b\));
        \math-macro other($x, \+, $y) := $y;
        \math-macro plus($x, \+, $y) := $y;
        \macro carrier() := b;
      }
      \module Sibling {
        \definition first: a = a := \refl(\(a + b\));
        \math-macro earlier($x, \+, $y) := $x;
        \math-macro later($x, \+, $y) := $y;
      }
    }",
    )
    .unwrap();
}

#[test]
fn direct_use_flattens_structure_arguments() {
    check(
        r"\module Playground { \structure Point[Carrier: \Set] { value: Carrier }
      \module T(A: \Set, point: Point[A]) { \macro value() := point.value; }
      \module M(A: \Set, a: A) {
        \definition law: a = a := \refl(value!{});
        \use \root.Playground[].T[A := A, point := Point[A] { value := a }]::value;
      }}",
    )
    .unwrap();
}

#[test]
fn recursion_limit_reports_definition_and_call() {
    let error = check(r"\module M { \macro again() := again!{}; \infer again!{}; }").unwrap_err();
    assert!(
        error.contains("128") && error.contains("again") && error.contains("M"),
        "{error}"
    );
}

#[test]
fn scoped_macro_exports_preserve_private_template_bindings() {
    use syntax::syntax::{Identifier, ModuleBody, ModuleItem};
    let mut modules = syntax::parse::str_parse_modules(
        r"\module M(A: \Set, a, b: A) {
      \definition before: b = b := \refl(wrapped!{});
      \macro value() := a;
      \definition outside: a = a := \refl(value!{});
      \macro wrapped() := value!{};
      \macro value() := b;
    }",
    )
    .unwrap();
    let ModuleBody::Inline(items) = &mut modules[0].body else {
        unreachable!()
    };
    let local = items.split_off(3);
    items.push(ModuleItem::Scoped {
        exports: vec![Identifier("wrapped".into())],
        items: local,
    });
    modules[0].declaration_spans.truncate(4);
    let project = resolve::resolve(&modules).unwrap();
    Checker::default().check(&project).unwrap();
}

#[test]
fn math_in_use_arguments_can_use_independent_local_templates() {
    check(
        r"\module T(A: \Set, a: A) { \macro value() := a; }
      \module M(A: \Set, a: A) {
        \definition law: a = a := \refl(value!{});
        \use \root.T[A := A, a := \(a + a\)]::value;
        \math-macro plus($x, \+, $y) := $x;
      }",
    )
    .unwrap();
}

#[test]
fn math_use_arguments_report_their_own_instantiation_cycle() {
    let error = check(
        r"\module T(A: \Set, a: A) { \math-macro plus($x, \+, $y) := a; }
      \module M(A: \Set, a: A) { \use \root.T[A := A, a := \(a + a\)]::plus; }",
    )
    .unwrap_err();
    assert!(
        error.contains("Cyclic") && error.contains(" -> "),
        "{error}"
    );
}

#[test]
fn several_forward_calls_do_not_create_spurious_declaration_dependencies() {
    check(
        r"\module T(A: \Set, a: A) { \macro value() := a; }
      \module M(A: \Set, a: A) {
        \definition first: a = a := \refl(local!{});
        \definition second: a = a := \refl(local!{});
        \macro local() := value!{};
        \definition argument: A := a;
        \use \root.T[A := A, a := argument]::value;
      }",
    )
    .unwrap();
    let error = check(
        r"\module T(A: \Set, a: A) { \macro value() := a; }
      \module M(A: \Set, a: A) {
        \definition argument: A := value!{};
        \use \root.T[A := A, a := argument]::value;
      }",
    )
    .unwrap_err();
    assert!(
        error.contains("Cyclic") && error.contains(" -> "),
        "{error}"
    );
}

#[test]
fn generated_block_math_priority_is_stable_after_lazy_preparation() {
    use syntax::syntax::{ModuleBody, ModuleItem};
    let mut modules = syntax::parse::str_parse_modules(
        r"\module M(A: \Set, a, b: A) {
      \math-macro first($x, \+, $y) := $x;
      \math-macro second($x, \+, $y) := $y;
      \definition one: a = a := \refl(\(a + b\));
      \definition two: a = a := \refl(\(a + b\));
    }",
    )
    .unwrap();
    let ModuleBody::Inline(items) = &mut modules[0].body else {
        unreachable!()
    };
    let local = std::mem::take(items);
    items.push(ModuleItem::Scoped {
        exports: Vec::new(),
        items: local,
    });
    modules[0].declaration_spans.truncate(1);
    let project = resolve::resolve(&modules).unwrap();
    Checker::default().check(&project).unwrap();
}
