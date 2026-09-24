use super::*;

// Compare public meaning after replacing process-local IDs and file revisions.
fn observations(snapshot: &AnalysisSnapshot) -> Vec<String> {
    let key = |id| {
        &snapshot
            .outline()
            .iter()
            .find(|item| item.id == id)
            .unwrap()
            .key
    };
    let location = |location: Location| {
        let file = snapshot.sources().file(location.file).unwrap();
        (file.source.id.0.clone(), location.range)
    };
    let checked = snapshot.check();
    let mut result = vec![format!("{:?} {:?}", checked.status, checked.outputs)];
    for item in &checked.items {
        let status = match &item.status {
            ItemCheckStatus::Blocked { dependencies } => {
                format!(
                    "Blocked {:?}",
                    dependencies.iter().map(|id| key(*id)).collect::<Vec<_>>()
                )
            }
            status => format!("{status:?}"),
        };
        result.push(format!("item {:?}: {status}", key(item.item)));
    }
    for diagnostic in &checked.diagnostics {
        result.push(format!(
            "diagnostic {:?} {:?} {:?} {:?} {:?} {:?}",
            diagnostic.code,
            diagnostic.severity,
            diagnostic.message,
            diagnostic.primary.map(location),
            diagnostic
                .secondary
                .iter()
                .map(|(loc, note)| (location(*loc), note))
                .collect::<Vec<_>>(),
            diagnostic.notes,
        ));
    }
    for goal in &checked.goals {
        result.push(format!(
            "goal {:?} {:?} {:?} {:?} {:?} {:?} {:?}",
            key(goal.id.owner),
            goal.flavor,
            goal.context,
            goal.target,
            goal.constraints,
            goal.occurrences
                .iter()
                .map(|loc| location(*loc))
                .collect::<Vec<_>>(),
            goal.dependencies
                .iter()
                .map(|id| (key(id.owner), id.local))
                .collect::<Vec<_>>(),
        ));
    }
    for occurrence in &checked.occurrences {
        let target = match occurrence.target {
            SemanticRef::Item(id) => format!("{:?}", key(id)),
            SemanticRef::Local(loc) => format!("{:?}", location(loc)),
        };
        result.push(format!(
            "reference {:?} {target} {:?}",
            location(occurrence.location),
            occurrence.ty
        ));
    }
    result.sort();
    result
}

#[test]
fn editing_and_cancellation_match_fresh_analysis() {
    let mut host = AnalysisHost::new("/virtual/root.ref").unwrap();
    let revisions = [
        r"\module M { \definition A: \SetKind := \Set; \definition B: \SetKind := A; }",
        r"\module M { \definition A: \SetKind := \Prop; \definition B: \SetKind := A; }",
        r"\module M { \definition C: \SetKind := \Set; \definition A: \SetKind := C; \definition B: \SetKind := A; }",
        r"\module M { \definition C: \SetKind := \Set; \definition B: \SetKind := A; }",
        r"\module M { \definition C: \SetKind := \Set; \definition B: \SetKind := C; }",
        r"\module M { \definition C: \SetKind := \Set; \module N { \definition C: \SetKind := ?; \definition B: \SetKind := C; } }",
        r"\module M { \definition C: \SetKind := \Set; \module N { \definition C: \SetKind := ; \definition B: \SetKind := C; } }",
        r"\module M { \definition C: \SetKind := \Set; \module N { \definition C: \SetKind := \Prop; \definition B: \SetKind := C; } }",
        r"\module M { \module N { \definition C: \SetKind := \Set; } \import .N \as I; \definition B: \SetKind := I.C; }",
        r"\module M { \module N { \definition C: \SetKind := \Prop; } \import .N \as I; \definition B: \SetKind := I.C; }",
    ];
    for text in revisions {
        host.sources_mut()
            .set_overlay("/virtual/root.ref", text.into());
        let snapshot = host.snapshot();
        let control = kernel::control::CancellationToken::default();
        control.cancel();
        assert!(snapshot.check_with_control(control, None).is_err());
        let mut fresh = AnalysisHost::new("/virtual/root.ref").unwrap();
        *fresh.sources_mut() = host.sources().clone();
        let fresh = fresh.snapshot();
        let file = snapshot.sources().file_id("/virtual/root.ref").unwrap();
        let _ = snapshot.goals(file);
        let _ = fresh.definition_at(file, 0);
        assert_eq!(observations(&snapshot), observations(&fresh), "{text}");
        assert!(std::ptr::eq(snapshot.check(), host.snapshot().check()));
    }
}

#[test]
fn source_branches_and_replacement_cannot_reuse_revisions() {
    let mut host = AnalysisHost::new("/virtual/root.ref").unwrap();
    host.sources_mut()
        .set_overlay("/virtual/root.ref", r"\module M {}".into());
    let before = host.snapshot();
    let mut left = host.sources().clone();
    let mut right = host.sources().clone();
    left.set_overlay("/virtual/root.ref", r"\module Left {}".into());
    right.set_overlay("/virtual/root.ref", r"\module Right {}".into());
    assert_ne!(left.revision(), right.revision());
    *host.sources_mut() = left;
    let left = host.snapshot();
    *host.sources_mut() = right;
    let right = host.snapshot();
    assert_eq!(before.outline()[0].key.name, "M");
    assert_eq!(left.outline()[0].key.name, "Left");
    assert_eq!(right.outline()[0].key.name, "Right");
}
