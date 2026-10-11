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
    },
    Step(CheckStepProgress),
    Saving,
    Checkpoint {
        steps: usize,
        bytes: postcard::Result<Vec<u8>>,
    },
}

pub const MAX_PACKAGE_BYTES: usize = 512 * 1024 * 1024;

#[derive(Default, serde::Serialize, serde::Deserialize)]
pub struct PackageChecker {
    #[serde(serialize_with = "serialize_resolution")]
    resolution: resolve::Session,
    #[serde(serialize_with = "serialize_workspace")]
    workspace: GlobalEnvironment,
    steps: usize,
    pending: bool,
}

// The field order is the same as PackageChecker; borrow the live workspace
// rather than cloning it while writing a checkpoint between checking steps.
#[derive(serde::Serialize)]
struct Checkpoint<'a> {
    resolution: &'a resolve::Session,
    workspace: &'a GlobalEnvironment,
    steps: usize,
    pending: bool,
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
        mut interval: Option<Duration>,
        mut progress: impl FnMut(PackageProgress),
    ) -> Result<(), crate::Diagnostic> {
        let project = if self.pending {
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
        progress(PackageProgress::Prepared {
            paths,
            start: self.steps,
        });
        let mut checker = Checker {
            workspace: std::mem::take(&mut self.workspace),
        };
        let progress = std::cell::RefCell::new(&mut progress);
        let mut saved_at = Instant::now();
        let result = checker
            .workspace
            .add_project_range(
                &project,
                self.steps,
                end,
                &(self.steps..end).collect(),
                &mut |steps, workspace| {
                    if steps == end
                        || !boundaries.contains(&steps)
                        || !interval.is_some_and(|period| saved_at.elapsed() >= period)
                    {
                        return;
                    }
                    let _time = timing::Scope::shared();
                    progress.borrow_mut()(PackageProgress::Saving);
                    let started = Instant::now();
                    let bytes =
                        crate::checkpoint::serialize_bounded::<MAX_PACKAGE_BYTES>(&Checkpoint {
                            resolution: &self.resolution,
                            workspace,
                            steps,
                            pending: true,
                        });
                    let failed = bytes.is_err();
                    progress.borrow_mut()(PackageProgress::Checkpoint { steps, bytes });
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
        let decoded = crate::checkpoint::decompress::<MAX_PACKAGE_BYTES>(bytes)?;
        let mut saved: Self = postcard::from_bytes(&decoded).ok()?;
        saved.resolution.restore_sources(sources)?;
        saved.workspace.crate_env.restore_shared_arena();
        Some(saved)
    }
}
