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
    /// Recheck this artifact's dependency environment in a fresh kernel arena.
    /// The result contains no handles into the raw elaboration environment.
    pub fn transfer_kernel(&self) -> Result<KernelArtifact, String> {
        let (environment, stats) = self.environment.kernel_env().transfer_with_stats()?;
        let environment = Rc::new(environment);
        Ok(KernelArtifact {
            item: self.item,
            version: self.version,
            environment,
            transfer_stats: stats,
        })
    }

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

#[derive(Debug, Clone)]
pub struct KernelArtifact {
    pub item: ItemId,
    pub version: ItemVersion,
    environment: Rc<elab::lowering::KernelEnvironment>,
    pub transfer_stats: kernel::transfer::TransferStats,
}

impl KernelArtifact {
    pub fn environment(&self) -> &kernel::environment::Environment {
        &self.environment
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

    #[test]
    fn transferred_artifacts_release_the_source_and_recheck_dependencies() {
        let mut host = AnalysisHost::new("/virtual/root.ref").unwrap();
        host.sources_mut().set_overlay(
            "/virtual/root.ref",
            include_str!("../../../tests/ok/modules/program_inductive_instance.ref").into(),
        );
        let snapshot = host.snapshot();
        let result = snapshot.check();
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let artifact = result.artifacts.last().unwrap().clone();
        let old = Rc::downgrade(&artifact.environment);
        let copied = artifact.transfer_kernel().unwrap();
        assert_ne!(artifact.environment_id(), copied.environment().arena().id());
        assert_eq!(copied.item, artifact.item);
        let target = Rc::downgrade(&copied.environment);
        drop(artifact);
        drop(snapshot);
        drop(host);
        assert!(old.upgrade().is_none());
        let again = copied.environment().transfer().unwrap().0;
        assert_eq!(
            again.declaration_node_count(),
            copied.environment().declaration_node_count()
        );
        drop(copied);
        assert!(target.upgrade().is_none());
    }

    #[test]
    fn transfer_preserves_nested_instances_proof_parameters_and_program_mirrors() {
        for source in [
            include_str!("../../../tests/ok/modules/substitution-identity.ref"),
            include_str!("../../../tests/ok/program-items/modules.ref"),
            include_str!("../../../tests/ok/program-items/namespace-identity.ref"),
        ] {
            let modules = syntax::parse::str_parse_modules(source).unwrap();
            let mut global = GlobalEnvironment::default();
            global.add_modules_to_root(&modules).unwrap();
            let mut copied = global.kernel_env().transfer().unwrap();
            let counts = copied.declaration_node_count();
            drop(global);
            // Repeated reconstruction must not accumulate old environments or
            // duplicate nominal declarations and their reflected counterparts.
            for _ in 0..4 {
                copied = copied.transfer().unwrap();
                assert_eq!(copied.declaration_node_count(), counts);
            }
        }
    }

    #[test]
    #[ignore = "full library transfer measurement"]
    fn library_transfer_measurement() {
        let root =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/library/ref.toml");
        let mut host = AnalysisHost::new(root).unwrap();
        host.refresh_disk();
        let snapshot = host.snapshot();
        let started = std::time::Instant::now();
        let checked = snapshot.check();
        assert!(checked.diagnostics.is_empty(), "{:?}", checked.diagnostics);
        let elaboration = started.elapsed();
        let artifact = checked.artifacts.last().unwrap();
        let copied = artifact.transfer_kernel().unwrap();
        eprintln!(
            "cold={elaboration:?}, transfer={:?}, retained={}",
            copied.transfer_stats,
            copied.environment().declaration_node_count()
        );
        assert_eq!(
            copied.environment().declaration_node_count(),
            artifact.environment.kernel_env().declaration_node_count()
        );
    }
}
