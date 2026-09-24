use super::*;

/// A checked item and the immutable environment that owns its raw and kernel
/// nodes. Cloning an artifact keeps its complete dependency environment alive.
#[derive(Clone)]
pub struct CheckedArtifact {
    pub item: ItemId,
    pub version: ItemVersion,
    environment: Rc<GlobalEnvironment>,
}

impl CheckedArtifact {
    pub fn environment_id(&self) -> kernel::syntax::ArenaId {
        self.environment.kernel_env().arena().id()
    }
    pub fn retained_raw_nodes(&self) -> [(&'static str, usize); 5] {
        self.environment.arena().node_counts()
    }
    pub(super) fn new(item: &OutlineItem, environment: Rc<GlobalEnvironment>) -> Self {
        Self {
            item: item.id,
            version: item.version,
            environment,
        }
    }
}

impl std::fmt::Debug for CheckedArtifact {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CheckedArtifact")
            .field("item", &self.item)
            .field("version", &self.version)
            .field("environment", &self.environment_id())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn old_environment_lives_exactly_as_long_as_its_artifacts() {
        let mut host = AnalysisHost::new("/virtual/root.ref").unwrap();
        host.sources_mut().set_overlay(
            "/virtual/root.ref",
            r"\module M { \definition A: \SetKind := \Set; }".into(),
        );
        let snapshot = host.snapshot();
        let artifact = snapshot.check().artifacts[0].clone();
        let old = Rc::downgrade(&artifact.environment);
        host.sources_mut().set_overlay(
            "/virtual/root.ref",
            r"\module M { \definition B: \SetKind := \Set; }".into(),
        );
        let next = host.snapshot();
        assert_ne!(
            artifact.environment_id(),
            next.check().artifacts[0].environment_id()
        );
        drop(snapshot);
        assert!(old.upgrade().is_some());
        drop(artifact);
        assert!(old.upgrade().is_none());
    }
}
