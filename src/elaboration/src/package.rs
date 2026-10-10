//! Resumable, dependency-ordered package checking, including frontend state.
use crate::{Checker, api::CheckStepProgress, elaborator::GlobalEnvironment};
use std::sync::Arc;
use syntax::syntax::{Module, SourceFile, SourceId};

pub enum PackageProgress {
    Prepared {
        paths: Vec<Vec<String>>,
        start: usize,
    },
    Step(CheckStepProgress),
}

pub const MAX_PACKAGE_BYTES: usize = 512 * 1024 * 1024;

#[derive(Default, serde::Serialize, serde::Deserialize)]
pub struct PackageChecker {
    #[serde(serialize_with = "serialize_resolution")]
    resolution: resolve::Session,
    #[serde(serialize_with = "serialize_workspace")]
    workspace: GlobalEnvironment,
    steps: usize,
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
        mut progress: impl FnMut(PackageProgress),
    ) -> Result<(), crate::Diagnostic> {
        let project = self
            .resolution
            .append(module)
            .map_err(crate::Diagnostic::resolution)?;
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
        let paths = project
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
        progress(PackageProgress::Prepared {
            paths,
            start: self.steps,
        });
        let mut checker = Checker {
            workspace: std::mem::take(&mut self.workspace),
        };
        let result = checker.check_range_with_progress(
            &project,
            self.steps,
            end,
            &(self.steps..end).collect(),
            &Default::default(),
            |_, _| {},
            |event| progress(PackageProgress::Step(event)),
        );
        self.workspace = checker.workspace;
        if result.is_ok() {
            self.steps = end;
        }
        result
    }

    pub fn analysis(&self) -> &crate::analysis::Analysis {
        self.workspace.analysis()
    }

    /// Call only after a successful append; source text is supplied by the loader on restore.
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
        let decoded =
            miniz_oxide::inflate::decompress_to_vec_with_limit(bytes, MAX_PACKAGE_BYTES).ok()?;
        let mut saved: Self = postcard::from_bytes(&decoded).ok()?;
        saved.resolution.restore_sources(sources)?;
        saved.workspace.crate_env.restore_shared_arena();
        Some(saved)
    }
}
