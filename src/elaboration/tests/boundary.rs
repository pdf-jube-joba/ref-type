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
