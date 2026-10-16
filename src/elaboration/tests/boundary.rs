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
                \structure A[Carrier: \Set] := { op1: Carrier };
                \definition F: \forall (Carrier: \Set) -> \Set :=
                    \fun (Carrier: \Set) => A[Carrier];
            }",
            "A",
        ),
        (
            r"\module Library { \structure A[Carrier: \Set] := { op1: Carrier }; }
            \module Playground {
                \import \root.Library[] \as L;
                \definition F: \forall (Carrier: \Set) -> \Set :=
                    \fun (Carrier: \Set) => L.A[Carrier];
            }",
            "L.A",
        ),
        (
            r"\module Library { \structure A[Carrier: \Set] := { op1: Carrier }; }
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
        \definition id [A: \Prop] [x: A]: A := x;
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
