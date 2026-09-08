//! Structured elaboration errors and goal rendering.
use crate::raw::{
    environment::CrateEnv,
    exp::{Exp, ExpContext},
    ids::MetaVarId,
};
use crate::syntax::{SourceLocation, SourceSpan, SurfaceMeta};
use std::{error::Error, fmt};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaFlavor {
    Implicit,
    Goal,
    Named(u32),
    Synthetic,
}

impl From<SurfaceMeta> for MetaFlavor {
    fn from(value: SurfaceMeta) -> Self {
        match value {
            SurfaceMeta::Implicit => Self::Implicit,
            SurfaceMeta::Goal => Self::Goal,
            SurfaceMeta::Named(number) => Self::Named(number),
        }
    }
}

#[derive(Debug, Clone)]
pub enum GoalConstraint {
    HasType { term: Exp, expected: Exp },
    Equal { left: Exp, right: Exp },
    IsSort { term: Exp },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintStatus {
    Discharged,
    Residual,
    Failed,
}

#[derive(Debug, Clone)]
pub struct ConstraintRecord {
    pub original: GoalConstraint,
    pub normalized: GoalConstraint,
    pub status: ConstraintStatus,
}

#[derive(Debug, Clone)]
pub struct MetaGoal {
    pub metavariable: MetaVarId,
    pub flavor: MetaFlavor,
    pub span: SourceSpan,
    pub context: ExpContext,
    pub principal: Option<GoalConstraint>,
    pub constraints: Vec<ConstraintRecord>,
    pub dependencies: Vec<MetaVarId>,
}

impl MetaGoal {
    pub fn display_name(&self) -> String {
        match self.flavor {
            MetaFlavor::Implicit => "_".into(),
            MetaFlavor::Goal => format!("?#{}", self.metavariable.0),
            MetaFlavor::Named(number) => format!("?{number}"),
            MetaFlavor::Synthetic => format!("?m{}", self.metavariable.0),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ElaborationError {
    Located {
        location: SourceLocation,
        error: Box<ElaborationError>,
    },
    Message(String),
    ConstraintFailure {
        message: String,
        constraints: Vec<ConstraintRecord>,
    },
    AmbiguousImplicit(Vec<MetaGoal>),
    UnsolvedGoals(Vec<MetaGoal>),
}

impl fmt::Display for ElaborationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Located { location, error } => {
                write!(formatter, "{error}\n{}", location.render())
            }
            Self::Message(message) => formatter.write_str(message),
            Self::ConstraintFailure { message, .. } => write!(formatter, "{message}"),
            Self::AmbiguousImplicit(goals) => write!(
                formatter,
                "{} implicit metavariable(s) are not uniquely determined",
                goals.len()
            ),
            Self::UnsolvedGoals(goals) => {
                write!(
                    formatter,
                    "{} metavariable goal(s) remain unsolved",
                    goals.len()
                )
            }
        }
    }
}

impl Error for ElaborationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Located { error, .. } => Some(error.as_ref()),
            _ => None,
        }
    }
}

pub fn format_elaboration_error(env: &CrateEnv, error: &ElaborationError) -> String {
    match error {
        ElaborationError::Located { location, error } => format!(
            "{}\n{}",
            format_elaboration_error(env, error),
            location.render()
        ),
        ElaborationError::Message(message) => message.clone(),
        ElaborationError::ConstraintFailure {
            message,
            constraints,
        } => {
            let details = constraints
                .iter()
                .map(|constraint| format_constraint_record(env, constraint))
                .collect::<Vec<_>>()
                .join("\n");
            format!("{message}\n{details}")
        }
        ElaborationError::AmbiguousImplicit(goals) => format_goals(
            env,
            "implicit metavariable is not uniquely determined",
            goals,
        ),
        ElaborationError::UnsolvedGoals(goals) => {
            format_goals(env, "unsolved metavariable goal", goals)
        }
    }
}

fn format_goals(env: &CrateEnv, heading: &str, goals: &[MetaGoal]) -> String {
    goals
        .iter()
        .map(|goal| {
            let context = crate::raw::printing::format_ctx(env, &goal.context);
            let principal = goal
                .principal
                .as_ref()
                .map(|constraint| format_constraint(env, constraint))
                .unwrap_or_else(|| "<no principal judgement>".into());
            let constraints = goal
                .constraints
                .iter()
                .map(|constraint| format!("  {}", format_constraint_record(env, constraint)))
                .collect::<Vec<_>>()
                .join("\n");
            format!(
                "{heading} {} at {}..{}\ncontext: [{}]\ngoal: {}\nconstraints:\n{}",
                goal.display_name(),
                goal.span.start,
                goal.span.end,
                context,
                principal,
                constraints
            )
        })
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn format_constraint_record(env: &CrateEnv, record: &ConstraintRecord) -> String {
    format!(
        "[{:?}] {}",
        record.status,
        format_constraint(env, &record.normalized)
    )
}

fn format_constraint(env: &CrateEnv, constraint: &GoalConstraint) -> String {
    let exp = |term| crate::raw::printing::format_exp(env, term);
    match constraint {
        GoalConstraint::HasType { term, expected } => {
            format!("{} : {}", exp(*term), exp(*expected))
        }
        GoalConstraint::Equal { left, right } => format!("{} ≡ {}", exp(*left), exp(*right)),
        GoalConstraint::IsSort { term } => format!("{} has a sort", exp(*term)),
    }
}

impl From<String> for ElaborationError {
    fn from(value: String) -> Self {
        Self::Message(value)
    }
}

impl From<&str> for ElaborationError {
    fn from(value: &str) -> Self {
        Self::Message(value.into())
    }
}
