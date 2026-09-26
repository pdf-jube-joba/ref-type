use elaboration::Checker;
use resolve::{Project, hir::*};

fn resolve(source: &str) -> Project {
    resolve::resolve(&syntax::parse::str_parse_modules(source).unwrap()).unwrap()
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
