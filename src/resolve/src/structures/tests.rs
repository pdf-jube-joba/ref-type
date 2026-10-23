use super::*;

#[test]
fn namespace_arguments_specialize_their_nested_namespace_references() {
    let modules = syntax::parse::str_parse_modules(
        r"
        \module Source(I: \Set, data: I -> I) {
            \definition chart[i: I]: I := data i;
            \module Use(frame: I -> I) {
                \definition value: I -> I := frame;
            }
            \import .Use[frame := \fun (i: I) => chart i] \as Build;
        }
        \module Consumer(A: \Set, f: A -> A) {}
        ",
    )
    .unwrap();
    let mut session = Session::default();
    for module in &modules {
        session.append(module).unwrap();
    }
    let resolver = &session.resolver;
    let source = resolver.scopes[0].children["Source"];
    let consumer = resolver.scopes[0].children["Consumer"];
    let build = resolver.scopes[source.0 as usize].imports["Build"];
    let reference = |module: ModuleId, name: &str| SExp::AccessPath {
        access: LocalAccess::Resolved {
            module,
            access: Name(
                name.to_owned(),
                Some(resolver.scopes[module.0 as usize].names[name]),
            ),
            display: name.to_owned(),
            span: SourceSpan::default(),
        },
        parameters: Vec::new(),
    };
    let substitutions = HashMap::from([
        (
            resolver.scopes[source.0 as usize].names["I"],
            reference(consumer, "A"),
        ),
        (
            resolver.scopes[source.0 as usize].names["data"],
            reference(consumer, "f"),
        ),
    ]);
    let mut specialized =
        resolver.substitute_front_expression(&reference(build, "value"), &substitutions);
    let mut charts = 0;
    macros::walk_sexp_mut(&mut specialized, &mut |node| {
        let SExp::AccessPath { access, .. } = node else {
            return;
        };
        let name = match access {
            LocalAccess::Resolved { access, .. } => access,
            LocalAccess::Instantiated { child, .. } => child,
            _ => return,
        };
        if name.as_str() != "chart" {
            return;
        }
        charts += 1;
        let LocalAccess::Instantiated { path, .. } = access else {
            panic!("chart still belongs to the generic source namespace");
        };
        let ModuleInstantiatePath::FromRoot { calls } = path.as_ref() else {
            panic!("expected an explicit source namespace");
        };
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].0.as_str(), "Source");
        for (label, caller) in [("I", "A"), ("data", "f")] {
            let (_, argument) = calls[0].1.iter().find(|(name, _)| name.0 == label).unwrap();
            let SExp::AccessPath {
                access: LocalAccess::Resolved { access, .. },
                ..
            } = argument
            else {
                panic!("caller argument was replaced again");
            };
            assert_eq!(
                access.1,
                Some(resolver.scopes[consumer.0 as usize].names[caller])
            );
        }
    });
    assert_eq!(charts, 1);
}
