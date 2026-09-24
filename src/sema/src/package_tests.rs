use super::*;

fn workspace(files: &[(&str, &str)]) -> AnalysisHost {
    let mut host = AnalysisHost::new("/virtual/app/ref.toml").unwrap();
    for (path, text) in files {
        host.sources_mut()
            .set_overlay(format!("/virtual/{path}"), (*text).into());
    }
    host
}

#[test]
fn dependency_aliases_share_package_identity_and_local_imports_are_explicit() {
    let host = workspace(&[
        (
            "app/ref.toml",
            "[package]\nname='app'\n[dependencies]\none={path='../dep'}\ntwo={path='../dep'}",
        ),
        ("dep/ref.toml", "[package]\nname='shared'"),
        (
            "dep/src/root.ref",
            r"\definition RootType: \SetKind := \Set; \module Types { \inductive T: \Set := | value: T; }",
        ),
        (
            "app/src/root.ref",
            r"\module Consumer {
            \module one { \definition A: \SetKind := \Set; }
            \import .one[] \as Local;
            \import one \as Root; \definition rootType: \SetKind := Root.RootType; \import one.Types[] \as A;
            \import two.Types[] \as B;
            \definition shared: A.T := B.T::value;
            \definition local: \SetKind := Local.A;
        }",
        ),
    ]);
    let snapshot = host.snapshot();
    assert_eq!(snapshot.packages().packages.len(), 2);
    assert_eq!(
        snapshot.check().status,
        CheckStatus::Checked,
        "{:?}",
        snapshot.check().diagnostics
    );
    let app = &snapshot.packages().packages[&snapshot.packages().root.unwrap()];
    assert_eq!(app.dependencies["one"], app.dependencies["two"]);
    let source = snapshot
        .sources()
        .file_id("/virtual/app/src/root.ref")
        .unwrap();
    let text = &snapshot.sources().file(source).unwrap().source.text;
    let definition = snapshot
        .definition_at(source, text.find("B.T::").unwrap() + 2)
        .unwrap();
    let target = snapshot.sources().file(definition.file).unwrap();
    assert_eq!(
        target.source.id.0.to_str().unwrap(),
        "/virtual/dep/src/root.ref"
    );
    assert!(
        snapshot.outline().iter().all(|item| !item
            .key
            .module
            .iter()
            .any(|name| name.starts_with('$')))
    );
}

#[test]
fn same_named_packages_have_distinct_nominal_types() {
    let host = workspace(&[
        (
            "app/ref.toml",
            "[package]\nname='app'\n[dependencies]\na={path='../left'}\nb={path='../right'}",
        ),
        ("left/ref.toml", "[package]\nname='same'"),
        ("right/ref.toml", "[package]\nname='same'"),
        (
            "left/src/root.ref",
            r"\definition RootType: \SetKind := \Set; \module Types { \inductive T: \Set := | value: T; }",
        ),
        (
            "right/src/root.ref",
            r"\definition RootType: \SetKind := \Set; \module Types { \inductive T: \Set := | value: T; }",
        ),
        (
            "app/src/root.ref",
            r"\module Consumer {
            \import a.Types[] \as A;
            \import b.Types[] \as B;
            \definition wrong: A.T := B.T::value;
        }",
        ),
    ]);
    let snapshot = host.snapshot();
    assert_eq!(snapshot.packages().packages.len(), 3);
    assert_eq!(snapshot.check().status, CheckStatus::Failed);
    let items = snapshot
        .outline()
        .iter()
        .filter(|item| item.key.name == "T")
        .collect::<Vec<_>>();
    assert_eq!(items.len(), 2);
    assert_ne!(items[0].key.package, items[1].key.package);
    assert_ne!(items[0].id, items[1].id);
}

#[test]
fn package_edits_are_snapshot_inputs_and_macro_helpers_keep_definition_scope() {
    let mut host = workspace(&[
        (
            "app/ref.toml",
            "[package]\nname='app'\n[dependencies]\nexternal={path='../dep'}",
        ),
        ("dep/ref.toml", "[package]\nname='different-display-name'"),
        (
            "dep/src/root.ref",
            r"\module Provider { \inductive Flag: \Set := | yes: Flag | no: Flag; \definition hidden: Flag := Flag::yes; \macro helper() := hidden; }",
        ),
        (
            "app/src/root.ref",
            r"\module Consumer {
            \import external.Provider[] \as P;
            \use P.helper;
            \definition hidden: P.Flag := P.Flag::no;
            \definition result: P.Flag := helper!{};
            \definition verified: result = P.Flag::yes := \refl(P.Flag::yes);
        }",
        ),
    ]);
    let before = host.snapshot();
    assert_eq!(
        before.check().status,
        CheckStatus::Checked,
        "{:?}",
        before.check().diagnostics
    );
    host.sources_mut().set_overlay("/virtual/dep/src/root.ref", r"\module Provider { \inductive Flag: \Set := | yes: Flag | no: Flag; \definition hidden: Flag := Flag::no; \macro helper() := hidden; }".into());
    let after = host.snapshot();
    assert_eq!(after.check().status, CheckStatus::Failed);
    assert_eq!(before.check().status, CheckStatus::Checked);
    assert_eq!(before.packages().root, after.packages().root);
}

#[test]
fn dependency_cycles_and_missing_manifests_have_source_locations() {
    let host = workspace(&[
        (
            "app/ref.toml",
            "[package]\nname='app'\n[dependencies]\nb={path='../dep'}\nmissing={path='../absent'}",
        ),
        ("app/src/root.ref", ""),
        (
            "dep/ref.toml",
            "[package]\nname='dep'\n[dependencies]\na={path='../app'}",
        ),
        ("dep/src/root.ref", ""),
    ]);
    let snapshot = host.snapshot();
    let report = snapshot.parse_diagnostics();
    assert_eq!(report.diagnostics.len(), 2, "{:?}", report.diagnostics);
    assert!(
        report
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.primary.is_some())
    );
    let cycle = report
        .diagnostics
        .iter()
        .find(|d| d.message.contains("cyclic"))
        .unwrap();
    assert_eq!(cycle.secondary.len(), 2);
}
