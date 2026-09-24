use super::*;
use crate::metavariables::{ConstraintStatus, GoalConstraint, MetaFlavor, MetaGoal};
use elab::{environment::CrateEnv, printing::format_exp};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GoalId {
    pub revision: RevisionId,
    pub owner: ItemId,
    pub local: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DisplayJudgement {
    HasType { term: String, expected: String },
    Equal { left: String, right: String },
    IsSort { term: String },
}

#[derive(Debug, Clone)]
pub struct GoalSnapshot {
    pub id: GoalId,
    pub flavor: MetaFlavor,
    pub occurrences: Vec<Location>,
    pub editable: bool,
    pub context: Vec<(String, String)>,
    pub target: Option<DisplayJudgement>,
    pub constraints: Vec<(ConstraintStatus, DisplayJudgement)>,
    pub dependencies: Vec<GoalId>,
    pub provenance: Vec<crate::diagnostics::SourceOrigin>,
}

impl AnalysisSnapshot {
    pub fn goals(&self, file: FileId) -> Vec<GoalSnapshot> {
        self.check()
            .goals
            .iter()
            .filter(|goal| {
                goal.occurrences
                    .iter()
                    .any(|location| location.file == file)
                    || self
                        .outline()
                        .iter()
                        .any(|item| item.id == goal.id.owner && item.location.file == file)
            })
            .cloned()
            .collect()
    }

    pub(super) fn capture_goals(
        &self,
        env: &CrateEnv,
        goals: &[MetaGoal],
        location: Option<Location>,
    ) -> Vec<GoalSnapshot> {
        let Some(location) = location else {
            return Vec::new();
        };
        let Some(owner) = self
            .outline()
            .iter()
            .filter(|item| {
                item.location.file == location.file
                    && tree::contains(item.location.range, location.range)
            })
            .min_by_key(|item| item.location.range.end - item.location.range.start)
        else {
            return Vec::new();
        };
        let id = |local| GoalId {
            revision: self.revision(),
            owner: owner.id,
            local,
        };
        goals
            .iter()
            .map(|goal| GoalSnapshot {
                id: id(goal.metavariable.0),
                flavor: goal.flavor,
                provenance: {
                    let mut seen = std::collections::HashSet::new();
                    goal.origin
                        .into_iter()
                        .chain(goal.occurrences.iter().flatten().copied())
                        .chain(goal.related_origins.iter().copied())
                        .flat_map(|id| self.source_trace(&env.sources, Some(id)))
                        .filter(|entry| seen.insert(entry.id))
                        .collect()
                },
                editable: goal.editable,
                occurrences: goal
                    .occurrences
                    .iter()
                    .filter(|_| goal.editable)
                    .filter_map(|origin| origin.and_then(|id| env.sources.location(id)))
                    .filter_map(|location| {
                        self.sources()
                            .file_id(&location.source.id.0)
                            .and_then(|id| self.sources().file(id))
                            .map(|file| file.location(location.span))
                    })
                    .collect(),
                context: goal
                    .context
                    .iter()
                    .map(|binding| {
                        (
                            env.symbol(binding.var).to_owned(),
                            format_exp(env, binding.ty),
                        )
                    })
                    .collect(),
                target: goal
                    .principal
                    .as_ref()
                    .map(|constraint| display(env, constraint)),
                constraints: goal
                    .constraints
                    .iter()
                    .map(|record| (record.status, display(env, &record.normalized)))
                    .collect(),
                dependencies: goal
                    .dependencies
                    .iter()
                    .map(|dependency| id(dependency.0))
                    .collect(),
            })
            .collect()
    }
}

fn display(env: &CrateEnv, constraint: &GoalConstraint) -> DisplayJudgement {
    match constraint {
        GoalConstraint::HasType { term, expected } => DisplayJudgement::HasType {
            term: format_exp(env, *term),
            expected: format_exp(env, *expected),
        },
        GoalConstraint::Equal { left, right } => DisplayJudgement::Equal {
            left: format_exp(env, *left),
            right: format_exp(env, *right),
        },
        GoalConstraint::IsSort { term } => DisplayJudgement::IsSort {
            term: format_exp(env, *term),
        },
    }
}
