use sema::{Database, ParseKind, SourceSnapshot};

#[test]
fn continuous_edits_keep_two_generations_and_external_results_alive() {
    let mut database = Database::new();
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert(
        "/virtual/root.ref",
        r"\module Main { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }",
    );
    let first = database.check(&snapshot);
    assert!(first.is_success());
    let first_snapshot = snapshot.clone();
    for index in 0..40 {
        snapshot.insert(
            "/virtual/root.ref",
            format!(
                r"\module Main {{ \definition P{index}: \Prop := \forall (P: \Prop) -> P -> P; }}"
            ),
        );
        assert!(database.check(&snapshot).is_success());
        let retained = database.memory_cache_stats();
        assert!(retained.parse_entries <= 2, "{retained:?}");
        assert!(retained.query_results <= 2, "{retained:?}");
        assert!(retained.module_results <= 2, "{retained:?}");
    }
    assert!(first.declarations().any(|d| d.id.name == "P"));
    assert!(database.check(&first_snapshot).is_success());
    database.clear_memory();
    assert_eq!(database.memory_cache_stats().parse_entries, 0);
    assert!(first.declarations().any(|d| d.id.name == "P"));
}

#[test]
fn parse_only_clients_also_release_old_snapshots() {
    let mut database = Database::new();
    let mut snapshot = SourceSnapshot::new("/virtual/root.ref");
    snapshot.insert("/virtual/root.ref", r"\module Original {}");
    let original = database.parse(&snapshot, "/virtual/root.ref", ParseKind::Root);
    for index in 0..40 {
        snapshot.insert("/virtual/root.ref", format!(r"\module V{index} {{}}"));
        let parsed = database.parse(&snapshot, "/virtual/root.ref", ParseKind::Root);
        assert!(parsed.error.is_none());
        assert!(database.memory_cache_stats().parse_entries <= 2);
    }
    assert!(original.source.text.contains("Original"));
}
