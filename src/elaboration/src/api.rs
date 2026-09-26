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
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub message: String,
    pub location: Option<SourceLocation>,
    pub goals: Vec<Goal>,
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for Diagnostic {}

/// Inspection data detached from the inference and kernel arenas.
#[derive(Debug, Clone)]
pub struct Statistics {
    pub raw_nodes: Vec<(&'static str, usize)>,
    pub raw_caches: Vec<(&'static str, usize)>,
    pub kernel_nodes: Vec<(kernel::syntax::Family, usize)>,
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
    pub fn kernel_environment(&self) -> &kernel::environment::Environment {
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
        let (location, error) = match error {
            ElaborationError::Located { location, error } => {
                (Some(location.clone()), error.as_ref())
            }
            error => (None, error),
        };
        let env = self.workspace.crate_env();
        let goals = match error {
            ElaborationError::UnsolvedGoals(goals) | ElaborationError::AmbiguousImplicit(goals) => {
                goals
                    .iter()
                    .map(|goal| Goal {
                        name: goal.display_name(),
                        dependencies: goal.dependencies.iter().map(|id| id.0).collect(),
                        location: location.as_ref().map(|location| SourceLocation {
                            source: location.source.clone(),
                            span: goal.span,
                        }),
                        context: crate::raw::printing::format_ctx(env, &goal.context),
                        judgement: goal
                            .principal
                            .as_ref()
                            .map(|constraint| metavariables::format_constraint(env, constraint)),
                        constraints: goal
                            .constraints
                            .iter()
                            .map(|constraint| {
                                metavariables::format_constraint_record(env, constraint)
                            })
                            .collect(),
                    })
                    .collect()
            }
            _ => Vec::new(),
        };
        Diagnostic {
            message: format!(
                "Elaboration Error: {}",
                metavariables::format_elaboration_error(env, error)
            ),
            location,
            goals,
        }
    }
}
