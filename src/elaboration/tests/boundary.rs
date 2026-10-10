use elaboration::Checker;
use resolve::{Project, hir::*};

fn resolve(source: &str) -> Project {
    resolve::resolve(&syntax::parse::str_parse_modules(source).unwrap()).unwrap()
}

#[test]
fn structure_signature_term_diagnostics_identify_the_reference_and_suggest_a_sort() {
    use diagnostics::DiagnosticError;
    use std::sync::Arc;

    for (text, reference) in [
        (
            r"\module Playground {
                \structure A[Carrier: \Set] { op1: Carrier }
                \definition F: \forall (Carrier: \Set) -> \Set :=
                    \fun (Carrier: \Set) => A[Carrier];
            }",
            "A",
        ),
        (
            r"\module Library { \structure A[Carrier: \Set] { op1: Carrier } }
            \module Playground {
                \import \root.Library[] \as L;
                \definition F: \forall (Carrier: \Set) -> \Set :=
                    \fun (Carrier: \Set) => L.A[Carrier];
            }",
            "L.A",
        ),
        (
            r"\module Library { \structure A[Carrier: \Set] { op1: Carrier } }
            \module Playground {
                \definition F: \forall (Carrier: \Set) -> \Set :=
                    \fun (Carrier: \Set) => \root.Library[].A[Carrier];
            }",
            "Library.A",
        ),
    ] {
        let source = Arc::new(SourceFile {
            id: SourceId("/virtual/structure-error.ref".into()),
            text: text.into(),
        });
        let mut modules = syntax::parse::parse_modules_from_source(&source).unwrap();
        for module in &mut modules {
            module.source = Some(source.clone());
            module.header_source = Some(source.clone());
        }
        let project = resolve::resolve(&modules).unwrap();
        let diagnostic = Checker::default().check(&project).unwrap_err();
        let message = diagnostic.message.clone();
        assert!(
            message.contains(&format!("Structure '{reference}' is a signature")),
            "{message}"
        );
        assert!(message.contains("add ': \\Set'"), "{message}");
        let data = diagnostic.diagnostic_data();
        assert_eq!(data.code, "elaboration.StructureSignatureUsedAsTerm");
        assert_eq!(data.arguments["access_path"], reference.into());
        let location = diagnostic.location.unwrap();
        let snippet = &source.text[location.span.start..location.span.end];
        assert_eq!(
            snippet,
            if reference == "Library.A" {
                "\\root.Library[].A"
            } else {
                reference
            }
        );
    }
}

#[test]
fn structure_with_an_explicit_sort_can_be_returned_as_a_set() {
    let project = resolve(
        r"\module Playground {
            \structure A[Carrier: \Set]: \Set { op1: Carrier }
            \definition F: \forall (Carrier: \Set) -> \Set :=
                \fun (Carrier: \Set) => A[Carrier];
        }",
    );
    Checker::default().check(&project).unwrap();
}

#[test]
fn missing_items_use_the_display_path_in_text_and_diagnostic_data() {
    use diagnostics::DiagnosticError;
    let error = elaboration::error::Error::UnknownAccess {
        access_path: LocalAccess::Resolved {
            module: ModuleId(1),
            span: SourceSpan { start: 12, end: 15 },
            access: Name("internal_name".into(), Some(BindingId(6))),
            display: "Library.A".into(),
        },
    };
    assert_eq!(error.to_string(), "Item 'Library.A' was not found");
    let data = error.diagnostic_data();
    assert_eq!(data.code, "elaboration.UnknownAccess");
    assert_eq!(data.arguments["access_path"], "Library.A".into());
}

#[test]
fn checking_uses_binding_ids_and_keeps_a_reusable_hir() {
    let mut project = resolve(
        r"\module M {
        \definition P: \Prop := \forall (A: \Prop) -> A -> A;
        \definition id (A: \Prop) (x: A): A := x;
        \definition Q: \Prop := P;
    }",
    );
    let ModuleBody::Inline(items) = &mut project.modules[0].body else {
        panic!()
    };
    for item in items {
        if let ModuleItem::Definition {
            body: SExp::AccessPath { access, .. },
            ..
        } = item
        {
            let name = match access {
                LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. } => {
                    access
                }
                _ => panic!("unresolved access"),
            };
            assert!(name.1.is_some());
            name.0 = "display_name_only".into();
        }
    }
    let mut first = Checker::default();
    let mut second = Checker::default();
    first.check(&project).unwrap();
    second
        .check(&resolve(
            r"\module Prefix { \definition S: \SetKind := \Set; }",
        ))
        .unwrap();
    second.check(&project).unwrap();
    assert_eq!(
        format!("{:?}", first.analysis()),
        format!("{:?}", second.analysis())
    );
    assert_eq!(
        first.statistics().kernel_declaration_nodes,
        second.statistics().kernel_declaration_nodes
    );
}

#[test]
fn resolved_module_routes_are_independent_of_display_names() {
    let mut project = resolve(
        r"\module Base { \module Inner { \definition P: \Prop := \forall (A: \Prop) -> A -> A; } }
        \module Use { \import \root.Base[] \as B; \import B.Inner[] \as I; \definition Q: \Prop := I.P; }",
    );
    for module in &mut project.modules {
        let ModuleBody::Inline(items) = &mut module.body else {
            panic!()
        };
        for item in items {
            if let ModuleItem::Import { path, .. } = item {
                let calls = match path {
                    ModuleInstantiatePath::FromRoot { calls }
                    | ModuleInstantiatePath::FromModule { calls, .. }
                    | ModuleInstantiatePath::FromCurrent { calls, .. } => calls,
                    ModuleInstantiatePath::FromImport { import_name, calls } => {
                        assert!(import_name.1.is_some());
                        import_name.0 = "display_alias".into();
                        calls
                    }
                };
                for (name, _) in calls {
                    assert!(name.1.is_some());
                    name.0 = "display_module".into();
                }
            }
        }
    }
    Checker::default().check(&project).unwrap();
}

#[test]
fn resolver_orders_dependencies_of_children_in_mixed_scopes() {
    let project = resolve(
        r"\module B {
        \import \root.A[] \as A0;
        \module C { \import A0.D[] \as D0; \definition P: \Prop := D0.P; }
    }
    \module A { \module D { \definition P: \Prop := \forall (P: \Prop) -> P -> P; } }",
    );
    Checker::default().check(&project).unwrap();
}

#[test]
fn resolution_succeeds_before_an_ill_typed_term_is_rejected() {
    let project = resolve(r"\module M { \definition bad: \Prop := \Set; }");
    assert!(Checker::default().check(&project).is_err());
}

#[test]
fn parent_definitions_are_checked_before_importing_nested_children() {
    let project = resolve(
        r"
        \module Parent(A: \Set, value: A) {
            \definition Carrier: \Set := A;
            \definition shared: Carrier := value;
            \module Math {
                \module Specification {
                    \module Def { \definition result: Carrier := shared; }
                    \module Prop {
                        \import \parent.Def[] \as Def;
                        \definition result: Carrier := Def.result;
                    }
                }
            }
            \import \root.Parent[A := A, value := value].Math[].Specification[].Def[] \as D;
            \definition result: Carrier := D.result;
        }
        \module Consumer {
            \inductive Unit: \Set := | unit: Unit;
            \import \root.Parent[A := Unit, value := Unit::unit] \as P;
            \import P.Math[].Specification[].Prop[] \as Laws;
            \definition direct: P.result = Unit::unit := \refl(Unit::unit);
            \definition nested: Laws.result = P.result := \refl(Unit::unit);
        }
    ",
    );
    Checker::default().check(&project).unwrap();
}

#[test]
fn instantiated_sibling_uses_common_parent_definitions_and_imports() {
    let project = resolve(
        r"
        \module Source(A: \Set, value: A) { \definition get: A := value; }
        \module Parent(A: \Set, value: A) {
            \import \root.Source[A := A, value := value] \as Shared;
            \definition Carrier: \Set := A;
            \definition common: Carrier := Shared.get;
            \module Limit {
                \module Def { \definition result: Carrier := common; }
                \module Prop {
                    \import \parent.Def[] \as Def;
                    \definition result: Carrier := Def.result;
                }
            }
        }
        \module Consumer {
            \inductive Unit: \Set := | unit: Unit;
            \import \root.Parent[A := Unit, value := Unit::unit].Limit[].Prop[] \as P;
            \definition result: P.result = Unit::unit := \refl(Unit::unit);
        }
    ",
    );
    Checker::default().check(&project).unwrap();
}

#[test]
fn proposition_structure_defaults_follow_parameters_and_supplied_fields() {
    let project = resolve(
        r"\module Defaults {
            \module Definitions(A: \Set) {
                \structure Data: \Set { value: A }
                \structure Laws[data: Data]: \Prop {
                    required: data.value = data.value,
                    copy: data.value = data.value := required,
                    final: data.value = data.value := copy,
                }
                \definition Bundle: \Set :=
                    \Cast[Data] ({ data: Data \where Laws[data] });
            }
            \module Use(A: \Set, a: A) {
                \import \parent.Definitions[A := A] \as D;
                \definition inferred: D.Bundle := D.Bundle {
                    value := a,
                    required := \refl(a),
                };
                \definition overridden: D.Bundle := D.Bundle {
                    value := a,
                    required := \refl(a),
                    copy := \refl(a),
                };
                \definition result: a = a := #final{overridden};
            }
        }",
    );
    Checker::default().check(&project).unwrap();
}

#[test]
fn proposition_structure_default_is_checked_when_declared() {
    let project = resolve(
        r"\module InvalidDefault(A: \Set, a: A) {
            \structure Laws: \Prop {
                invalid: a = a := a,
            }
        }",
    );
    assert!(Checker::default().check(&project).is_err());
}
