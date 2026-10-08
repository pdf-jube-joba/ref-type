use resolve::{hir::*, resolve};

#[test]
fn local_definition_shadowing_does_not_escape_its_expression() {
    use syntax::syntax as ast;
    let mut modules =
        syntax::parse::str_parse_modules(r"\module M(x: \Set) { \definition f: _ := x x; }")
            .unwrap();
    let ast::ModuleBody::Inline(items) = &mut modules[0].body else {
        panic!()
    };
    let ast::ModuleItem::Definition {
        body: ast::SExp::App { func, .. },
        ..
    } = &mut items[0]
    else {
        panic!()
    };
    let clause = (
        ast::Identifier("x".into()),
        ast::SExp::Sort(syntax::sort::Sort::Set(0)),
        func.as_ref().clone(),
    );
    **func = ast::SExp::Where {
        exp: func.clone(),
        clauses: vec![clause.clone(), clause],
        span: None,
    };
    let project = resolve(&modules).unwrap();
    let ModuleBody::Inline(items) = &project.modules[0].body else {
        panic!()
    };
    let ModuleItem::Definition {
        body: SExp::App { arg, .. },
        ..
    } = &items[0]
    else {
        panic!()
    };
    let SExp::AccessPath {
        access: LocalAccess::Resolved { access, .. },
        ..
    } = arg.as_ref()
    else {
        panic!("local definition escaped into the argument")
    };
    assert_eq!(access.1, project.modules[0].parameters[0].vars[0].1);
}

#[test]
fn diagnostics_distinguish_repeated_module_names() {
    let modules = syntax::parse::str_parse_modules(
        r"\module M { \module N {} }
        \module M { \module N {} \module N { \definition x: _ := missing; } }",
    )
    .unwrap();
    let error = resolve(&modules).unwrap_err();
    assert_eq!(error.module, ["M#2", "N#2"]);
    assert!(error.message.contains("missing"));
}

#[test]
fn shadowed_binders_have_distinct_ids_before_typing() {
    let modules = syntax::parse::str_parse_modules(
        r"\module M { \definition f: _ := \fun (x: _) => \fun (x: _) => x; }",
    )
    .unwrap();
    let project = resolve(&modules).unwrap();
    let ModuleBody::Inline(items) = &project.modules[0].body else {
        panic!()
    };
    let ModuleItem::Definition {
        body: SExp::Lam {
            bind: Bind::Named(outer),
            body,
        },
        ..
    } = &items[0]
    else {
        panic!()
    };
    let SExp::Lam {
        bind: Bind::Named(inner),
        body,
    } = body.as_ref()
    else {
        panic!()
    };
    let SExp::AccessPath {
        access: LocalAccess::Current { access, .. },
        ..
    } = body.as_ref()
    else {
        panic!()
    };
    assert_ne!(outer.vars[0].1, inner.vars[0].1);
    assert_eq!(access.1, inner.vars[0].1);
    assert!(access.1.is_some());
}

#[test]
fn resolves_macro_capture_without_type_inference() {
    let modules = syntax::parse::str_parse_modules(
        r"\module M(A: \Set, x: A) { \macro element() := x; \definition value: A := element!{}; }",
    )
    .unwrap();
    let project = resolve(&modules).unwrap();
    let ModuleBody::Inline(items) = &project.modules[0].body else {
        panic!()
    };
    let ModuleItem::Definition {
        body:
            SExp::AccessPath {
                access: LocalAccess::Resolved { module, access, .. },
                ..
            },
        ..
    } = &items[0]
    else {
        panic!()
    };
    assert_eq!(*module, project.modules[0].id);
    assert_eq!(access.1, project.modules[0].parameters[1].vars[0].1);
}

#[test]
fn existing_valid_sources_resolve_without_a_kernel_dependency() {
    fn files(path: &std::path::Path, output: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(path).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                files(&path, output);
            } else if path.extension().is_some_and(|ext| ext == "ref") {
                output.push(path);
            }
        }
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut paths = Vec::new();
    files(&root.join("tests/ok"), &mut paths);
    paths.sort();
    let mut failures = Vec::new();
    for path in paths {
        let modules = project::module_loader::load_modules_from_root(&path).unwrap();
        if let Err(error) = resolve(&modules) {
            failures.push(format!("{}: {}", path.display(), error));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn library_resolves_without_type_inference() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../libs/std");
    let package = project::package_loader::load_package(&root).unwrap();
    if let Err(error) = resolve(&package.modules) {
        panic!("{} at {:?}", error, error.module);
    }
}

#[test]
fn macro_value_let_uses_callers_type_and_its_own_binder() {
    let modules = syntax::parse::str_parse_modules(
        r"\module M(A: \Set, a: A) {
        \macro local($type, $value) := (\let A: $type := $value \in \return(A));
        \definition result: \F A := local!{A a};
    }",
    )
    .unwrap();
    let project = resolve(&modules).unwrap();
    let ModuleBody::Inline(items) = &project.modules[0].body else {
        panic!()
    };
    let ModuleItem::Definition {
        body:
            SExp::ValueLet {
                var,
                value_ty,
                value,
                body,
            },
        ..
    } = &items[0]
    else {
        panic!()
    };
    assert!(var.1.is_some());
    let SExp::AccessPath {
        access: LocalAccess::Resolved { access: ty, .. },
        ..
    } = value_ty.as_ref()
    else {
        panic!()
    };
    assert_eq!(ty.1, project.modules[0].parameters[0].vars[0].1);
    let SExp::AccessPath {
        access: LocalAccess::Resolved { access: arg, .. },
        ..
    } = value.as_ref()
    else {
        panic!()
    };
    assert_eq!(arg.1, project.modules[0].parameters[1].vars[0].1);
    let SExp::Return { value } = body.as_ref() else {
        panic!()
    };
    let SExp::AccessPath {
        access: LocalAccess::Current { access, .. },
        ..
    } = value.as_ref()
    else {
        panic!()
    };
    assert_eq!(access.1, var.1);
}

#[test]
fn normalization_records_each_source_occurrence_once() {
    use std::{collections::HashSet, sync::Arc};
    let text = r"\module M(A: \Set, a: A) {
        \definition identity(x: A): A := x;
        \definition value: A := identity a;
        \definition bound: A := (\fun (x: A) => identity x) a;
    }";
    let source = Arc::new(SourceFile {
        id: SourceId("/virtual/M.ref".into()),
        text: text.into(),
    });
    let mut modules = syntax::parse::parse_modules_from_source(&source).unwrap();
    modules[0].source = Some(source);
    let project = resolve(&modules).unwrap();
    let mut occurrences = HashSet::new();
    for reference in &project.references {
        assert!(
            occurrences.insert((
                &reference.module,
                reference.location.span.start,
                reference.location.span.end,
                &reference.target_module,
                &reference.target_name,
            )),
            "duplicate source occurrence: {reference:?}"
        );
    }
    let uses: Vec<_> = project
        .references
        .iter()
        .filter(|reference| reference.target_name == "identity")
        .collect();
    assert_eq!(uses.len(), 2);
    assert_ne!(uses[0].location.span, uses[1].location.span);
    for reference in uses {
        assert_eq!(
            &text[reference.location.span.start..reference.location.span.end],
            "identity"
        );
    }
}
