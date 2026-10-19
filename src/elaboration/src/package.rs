//! Resumable, dependency-ordered package checking, including frontend state.
use crate::{Checker, api::CheckStepProgress, elaborator::GlobalEnvironment};
use std::{
    collections::{BTreeSet, HashMap},
    sync::Arc,
    time::{Duration, Instant},
};
use syntax::syntax::{Module, SourceFile, SourceId};

pub enum PackageProgress {
    Prepared {
        paths: Vec<Vec<String>>,
        start: usize,
        selected: BTreeSet<usize>,
    },
    Step(CheckStepProgress),
    Saving,
    Checkpoint {
        steps: usize,
        bytes: postcard::Result<Vec<u8>>,
    },
    ArtifactCheckpoint {
        steps: usize,
        artifact: artifact::Result<PackageArtifact>,
    },
}

pub const MAX_PACKAGE_BYTES: usize = 512 * 1024 * 1024;

#[derive(artifact::Relocate, Default, serde::Serialize, serde::Deserialize)]
pub struct PackageChecker {
    #[serde(serialize_with = "serialize_resolution")]
    resolution: resolve::Session,
    #[serde(serialize_with = "serialize_workspace")]
    workspace: GlobalEnvironment,
    steps: usize,
    pending: bool,
    completed: BTreeSet<usize>,
}

// The field order is the same as PackageChecker; borrow the live workspace
// rather than cloning it while writing a checkpoint between checking steps.
#[derive(serde::Serialize)]
struct Checkpoint<'a> {
    resolution: &'a resolve::Session,
    workspace: &'a GlobalEnvironment,
    steps: usize,
    pending: bool,
    completed: &'a BTreeSet<usize>,
}

struct ArtifactCheckpoint<'a> {
    owner: ArtifactOwner,
    input: ArtifactOwner,
    boundary: &'a ArtifactBoundary,
    catalog: &'a mut ArtifactCatalog,
}

fn serialize_resolution<S: serde::Serializer>(
    value: &resolve::Session,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let _phase = crate::profiling::Phase::start("package.serialize-resolver");
    serde::Serialize::serialize(value, serializer)
}

fn serialize_workspace<S: serde::Serializer>(
    value: &GlobalEnvironment,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    let _phase = crate::profiling::Phase::start("package.serialize-checker");
    serde::Serialize::serialize(value, serializer)
}

impl PackageChecker {
    pub fn has_resolution(&self, name: &str) -> bool {
        self.resolution.contains_package(name)
    }

    /// Resolve declarations without marking any type-checking step complete.
    pub fn append_resolution(&mut self, module: &Module) -> Result<(), crate::Diagnostic> {
        let project = self
            .resolution
            .append(module)
            .map_err(crate::Diagnostic::resolution)?;
        self.steps = project.order.len();
        Ok(())
    }

    /// Live shared syntax retained by this checker, excluding source snapshots.
    pub fn expression_count(&self) -> usize {
        self.workspace.crate_env.arena().core.len()
    }

    /// Live syntax and namespace entries, before portable export scratch tables.
    pub fn artifact_entry_count(&self) -> usize {
        self.expression_count() + self.workspace.crate_env.namespace_entry_count()
    }

    pub fn prepare_export(&mut self) {
        if self.artifact_entry_count() > 500_000 {
            self.workspace.crate_env.clear_caches();
        }
    }

    pub fn append(
        &mut self,
        module: &Module,
        progress: impl FnMut(PackageProgress),
    ) -> Result<(), crate::Diagnostic> {
        self.append_with_checkpoints(module, None, progress)
    }

    pub fn is_pending(&self) -> bool {
        self.pending
    }

    /// Checkpoint only at source-module completion boundaries. The callback
    /// receives a resumable prefix, not a fully verified package result.
    pub fn append_with_checkpoints(
        &mut self,
        module: &Module,
        interval: Option<Duration>,
        progress: impl FnMut(PackageProgress),
    ) -> Result<(), crate::Diagnostic> {
        self.append_selection(module, None, interval, None, progress)
    }

    pub fn append_selected_with_checkpoints(
        &mut self,
        module: &Module,
        selected_paths: &BTreeSet<Vec<String>>,
        interval: Option<Duration>,
        progress: impl FnMut(PackageProgress),
    ) -> Result<(), crate::Diagnostic> {
        self.append_selection(module, Some(selected_paths), interval, None, progress)
    }

    /// Emit owned package checkpoints directly from the live checking boundary.
    pub fn append_selected_with_artifact_checkpoints(
        &mut self,
        module: &Module,
        selected_paths: &BTreeSet<Vec<String>>,
        interval: Option<Duration>,
        owner: ArtifactOwner,
        input: ArtifactOwner,
        boundary: &ArtifactBoundary,
        catalog: &mut ArtifactCatalog,
        progress: impl FnMut(PackageProgress),
    ) -> Result<(), crate::Diagnostic> {
        self.append_selection(
            module,
            Some(selected_paths),
            interval,
            Some(ArtifactCheckpoint {
                owner,
                input,
                boundary,
                catalog,
            }),
            progress,
        )
    }

    fn append_selection(
        &mut self,
        module: &Module,
        selected_paths: Option<&BTreeSet<Vec<String>>>,
        mut interval: Option<Duration>,
        mut artifact_checkpoint: Option<ArtifactCheckpoint<'_>>,
        mut progress: impl FnMut(PackageProgress),
    ) -> Result<(), crate::Diagnostic> {
        let project = if self.pending || self.resolution.contains_package(module.name.as_str()) {
            self.resolution.project()
        } else {
            self.resolution
                .append(module)
                .map_err(crate::Diagnostic::resolution)?
        };
        self.pending = true;
        let end = project.order.len();
        fn collect(
            module: &resolve::hir::Module,
            prefix: &mut Vec<String>,
            paths: &mut std::collections::HashMap<resolve::hir::ModuleId, Vec<String>>,
            seen: &mut std::collections::HashSet<Vec<String>>,
        ) {
            prefix.push(module.name.0.clone());
            let mut occurrence = 1;
            while !seen.insert(prefix.clone()) {
                occurrence += 1;
                *prefix.last_mut().unwrap() = format!("{}#{occurrence}", module.name.0);
            }
            paths.insert(module.id, prefix.clone());
            if let resolve::hir::ModuleBody::Inline(items) = &module.body {
                for item in items {
                    if let resolve::hir::ModuleItem::ChildModule { module } = item {
                        collect(module, prefix, paths, seen);
                    }
                }
            }
            prefix.pop();
        }
        let mut paths = std::collections::HashMap::new();
        let mut seen = std::collections::HashSet::new();
        for root in &project.modules {
            collect(root, &mut Vec::new(), &mut paths, &mut seen);
        }
        let paths: Vec<_> = project
            .order
            .iter()
            .map(|step| {
                let id = match step {
                    resolve::CheckStep::Parameters(id)
                    | resolve::CheckStep::Declaration { module: id, .. } => id,
                };
                paths[id].clone()
            })
            .collect();
        let mut last = HashMap::new();
        for (position, path) in paths.iter().enumerate() {
            let end = path
                .iter()
                .position(|part| part.starts_with('<'))
                .unwrap_or(path.len());
            last.insert(&path[..end], position + 1);
        }
        let boundaries: BTreeSet<_> = last.into_values().collect();
        let selected: BTreeSet<_> = paths
            .iter()
            .enumerate()
            .filter_map(|(position, path)| {
                let source_end = path
                    .iter()
                    .position(|part| part.starts_with('<'))
                    .unwrap_or(path.len());
                let source_path = &path[..source_end];
                let requested = selected_paths.map_or(
                    path.first()
                        .is_some_and(|name| name == module.name.as_str()),
                    |selected| {
                        selected.iter().any(|request| {
                            request == source_path || request.starts_with(source_path)
                        })
                    },
                );
                (requested && !self.completed.contains(&position)).then_some(position)
            })
            .collect();
        let start = selected.first().copied().unwrap_or(end);
        progress(PackageProgress::Prepared {
            paths,
            start,
            selected: selected.clone(),
        });
        let mut completed = self.completed.clone();
        let mut checker = Checker {
            workspace: std::mem::take(&mut self.workspace),
        };
        let progress = std::cell::RefCell::new(&mut progress);
        let mut saved_at = Instant::now();
        let result = checker
            .workspace
            .add_project_range(
                &project,
                start,
                end,
                &selected,
                &mut |steps, workspace| {
                    completed.insert(steps - 1);
                    if steps == end
                        || !boundaries.contains(&steps)
                        || interval.is_none_or(|period| saved_at.elapsed() < period)
                    {
                        return;
                    }
                    let _time = timing::Scope::shared();
                    progress.borrow_mut()(PackageProgress::Saving);
                    let started = Instant::now();
                    if workspace.crate_env.arena().core.len()
                        + workspace.crate_env.namespace_entry_count()
                        > 500_000
                    {
                        workspace.crate_env.clear_judgements();
                    }
                    let failed = if let Some(checkpoint) = artifact_checkpoint.as_mut() {
                        let artifact = artifacts::State {
                            resolution: &self.resolution,
                            workspace,
                            steps,
                            pending: true,
                            completed: &completed,
                        }
                        .export_package_state(
                            checkpoint.owner,
                            checkpoint.input,
                            checkpoint.boundary,
                            checkpoint.catalog,
                        );
                        let failed = artifact.is_err();
                        progress.borrow_mut()(PackageProgress::ArtifactCheckpoint {
                            steps,
                            artifact,
                        });
                        failed
                    } else {
                        let bytes = crate::checkpoint::serialize_bounded::<MAX_PACKAGE_BYTES>(
                            &Checkpoint {
                                resolution: &self.resolution,
                                workspace,
                                steps,
                                pending: true,
                                completed: &completed,
                            },
                        );
                        let failed = bytes.is_err();
                        progress.borrow_mut()(PackageProgress::Checkpoint { steps, bytes });
                        failed
                    };
                    let cost = started.elapsed();
                    // A growing environment will not fit again after hitting the budget.
                    // Successful writes adapt the cadence to keep checkpoint I/O bounded.
                    interval = if failed {
                        None
                    } else {
                        interval.map(|period| {
                            if period.is_zero() {
                                period
                            } else {
                                period.max(cost.saturating_mul(10))
                            }
                        })
                    };
                    saved_at = Instant::now();
                },
                &mut |event| progress.borrow_mut()(PackageProgress::Step(event)),
            )
            .map_err(|error| checker.diagnostic(&error));
        self.workspace = checker.workspace;
        self.completed = completed;
        if result.is_ok() {
            self.steps = end;
            self.pending = false;
        }
        result
    }

    pub fn analysis(&self) -> &crate::analysis::Analysis {
        self.workspace.analysis()
    }

    /// Call after a successful append. In-flight prefixes are emitted as
    /// PackageProgress::Checkpoint; source text is supplied by the loader on restore.
    pub fn checkpoint(&self) -> postcard::Result<Vec<u8>> {
        crate::checkpoint::serialize_bounded::<MAX_PACKAGE_BYTES>(self)
    }

    pub fn restore(
        bytes: &[u8],
        sources: impl Fn(&SourceId) -> Option<Arc<SourceFile>>,
    ) -> Option<Self> {
        if bytes.len() > MAX_PACKAGE_BYTES {
            return None;
        }
        let inflate = crate::profiling::Phase::start("package.inflate");
        let decoded = crate::checkpoint::decompress::<MAX_PACKAGE_BYTES>(bytes)?;
        drop(inflate);
        let deserialize = crate::profiling::Phase::start("package.deserialize");
        let mut saved: Self = postcard::from_bytes(&decoded).ok()?;
        drop(decoded);
        drop(deserialize);
        let _reconnect = crate::profiling::Phase::start("package.reconnect");
        saved.resolution.restore_sources(sources)?;
        saved.workspace.crate_env.restore_shared_arena();
        saved
            .workspace
            .restore_artifact_analysis(&saved.resolution.references());
        Some(saved)
    }
}

#[path = "package_artifacts.rs"]
mod artifacts;
pub use artifacts::{ArtifactBoundary, ArtifactCatalog, ArtifactOwner, PackageArtifact};
