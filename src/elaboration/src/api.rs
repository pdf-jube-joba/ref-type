//! Arena-independent checking results.
use crate::{
    elaborator::GlobalEnvironment,
    metavariables::{self, ElaborationError},
};
use syntax::syntax::SourceLocation;

#[derive(Debug, Clone)]
pub struct Goal {
    pub name: String,
    pub location: Option<SourceLocation>,
    pub context: String,
    pub judgement: Option<String>,
    pub constraints: Vec<String>,
    pub dependencies: Vec<u32>,
    pub state: String,
    pub solution: Option<String>,
    pub occurrences: Vec<SourceLocation>,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub error: Box<ElaborationError>,
    pub message: String,
    pub location: Option<SourceLocation>,
    pub goals: Vec<Goal>,
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for Diagnostic {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(self.error.as_ref())
    }
}
impl diagnostics::DiagnosticError for Diagnostic {
    fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        self.error.diagnostic_data()
    }
}
impl Diagnostic {
    pub fn resolution(error: resolve::Diagnostic) -> Self {
        Self {
            message: format!("Resolution Error: {error}"),
            location: error.location.clone(),
            error: Box::new(crate::error::Error::from(error).into()),
            goals: Vec::new(),
        }
    }
}

/// Inspection data detached from the inference and kernel arenas.
#[derive(Debug, Clone)]
pub struct Statistics {
    pub raw_nodes: Vec<(&'static str, usize)>,
    pub raw_caches: Vec<(&'static str, usize)>,
    pub kernel_nodes: Vec<(&'static str, usize)>,
    pub kernel_caches: Vec<(&'static str, usize)>,
    pub kernel_declaration_nodes: usize,
    pub materialized_definitions: usize,
    pub materialized_inductives: usize,
    pub materialized_datatypes: usize,
}

impl Statistics {
    pub fn lines(&self) -> Vec<String> {
        vec![
            format!("raw nodes: {:?}", self.raw_nodes),
            format!("raw caches: {:?}", self.raw_caches),
            format!("kernel nodes: {:?}", self.kernel_nodes),
            format!("kernel caches: {:?}", self.kernel_caches),
            format!(
                "kernel declaration nodes: {}",
                self.kernel_declaration_nodes
            ),
        ]
    }
}

/// Owns checking state without exposing inference arenas or metavariables.
#[derive(Default)]
pub struct Checker {
    workspace: GlobalEnvironment,
}

impl Checker {
    pub fn check(&mut self, project: &resolve::Project) -> Result<(), Diagnostic> {
        self.workspace = GlobalEnvironment::default();
        self.workspace
            .add_project(project)
            .map_err(|error| self.diagnostic(&error))
    }

    pub fn analysis(&self) -> &crate::analysis::Analysis {
        self.workspace.analysis()
    }
    pub fn active_module_path(&self) -> Vec<String> {
        self.workspace.active_module_path()
    }
    pub fn kernel_environment(&self) -> std::cell::Ref<'_, kernel::environment::Environment> {
        self.workspace.kernel_env()
    }

    pub fn statistics(&self) -> Statistics {
        let workspace = &self.workspace;
        let materializations = workspace.crate_env().materialization_stats();
        Statistics {
            raw_nodes: workspace.arena().node_counts().to_vec(),
            raw_caches: workspace.crate_env().cache_counts().to_vec(),
            kernel_nodes: workspace.kernel_env().arena().node_counts(),
            kernel_caches: workspace.kernel_env().cache_counts().to_vec(),
            kernel_declaration_nodes: workspace.kernel_env().declaration_node_count(),
            materialized_definitions: materializations.definitions,
            materialized_inductives: materializations.inductives,
            materialized_datatypes: materializations.datatypes,
        }
    }

    fn diagnostic(&self, error: &ElaborationError) -> Diagnostic {
        let _profile = crate::diagnostics::DiagnosticProfile::start("render");
        let error = error.materialize(&self.workspace);
        let error = &error;
        let (location, error) = match error {
            ElaborationError::Located { location, error } => {
                (Some(location.clone()), error.as_ref())
            }
            error => (None, error),
        };
        let env = self.workspace.crate_env();
        let goals = error
            .goals()
            .iter()
            .map(|goal| Goal {
                name: goal.display_name(),
                dependencies: goal.dependencies.iter().map(|id| id.0).collect(),
                location: location.as_ref().map(|location| SourceLocation {
                    source: location.source.clone(),
                    span: goal.span,
                }),
                context: goal.context.clone(),
                judgement: goal.principal.clone(),
                constraints: goal.constraints.iter().map(ToString::to_string).collect(),
                state: goal.state.to_string(),
                solution: goal.solution.clone(),
                occurrences: goal
                    .occurrences
                    .iter()
                    .filter_map(|span| {
                        location.as_ref().map(|location| SourceLocation {
                            source: location.source.clone(),
                            span: *span,
                        })
                    })
                    .collect(),
            })
            .collect();
        Diagnostic {
            error: Box::new(error.clone()),
            message: crate::diagnostics::bounded(
                format!(
                    "Elaboration Error: {}",
                    metavariables::format_elaboration_error(env, error)
                ),
                crate::diagnostics::MESSAGE_BYTES,
            ),
            location,
            goals,
        }
    }
}

impl Checker {
    /// Restore a locally trusted checkpoint after its identity and checksum were checked.
    /// The raw frontend and the kernel must resume with the same expression arena.
    pub fn restore_environment(bytes: &[u8]) -> Option<Self> {
        if bytes.len() > crate::MAX_ENVIRONMENT_BYTES {
            return None;
        }
        let inflate = crate::profiling::Phase::start("environment.inflate");
        let bytes =
            miniz_oxide::inflate::decompress_to_vec_with_limit(bytes, crate::MAX_ENVIRONMENT_BYTES)
                .ok()?;
        drop(inflate);
        let decode = crate::profiling::Phase::start("environment.deserialize");
        let mut workspace: GlobalEnvironment = postcard::from_bytes(&bytes).ok()?;
        drop(decode);
        let _phase = crate::profiling::Phase::start("environment.reconnect");
        workspace.crate_env.restore_shared_arena();
        Some(Self { workspace })
    }

    /// Continue the resolved order using a matching prefix checkpoint.
    /// Checkpoints are provisional until this call succeeds.
    pub fn check_range(
        &mut self,
        project: &resolve::Project,
        start: usize,
        end: usize,
        selected: &std::collections::BTreeSet<usize>,
        checkpoints: &std::collections::BTreeSet<usize>,
        save: impl FnMut(usize, postcard::Result<Vec<u8>>),
    ) -> Result<(), Diagnostic> {
        self.check_range_with_progress(project, start, end, selected, checkpoints, save, |_, _| {})
    }

    pub fn check_range_with_progress(
        &mut self,
        project: &resolve::Project,
        start: usize,
        end: usize,
        selected: &std::collections::BTreeSet<usize>,
        checkpoints: &std::collections::BTreeSet<usize>,
        mut save: impl FnMut(usize, postcard::Result<Vec<u8>>),
        mut progress: impl FnMut(usize, std::time::Duration),
    ) -> Result<(), Diagnostic> {
        // Prefix keys are valid only up to the first omitted checking step.
        let first_gap = (start..end)
            .find(|position| !selected.contains(position))
            .unwrap_or(end);
        self.workspace
            .add_project_range(
                project,
                start,
                end,
                selected,
                &mut |position, workspace| {
                    if position <= first_gap && checkpoints.contains(&position) {
                        let _time = timing::Scope::shared();
                        save(position, crate::checkpoint::serialize(workspace));
                    }
                },
                &mut progress,
            )
            .map_err(|error| self.diagnostic(&error))
    }
}
