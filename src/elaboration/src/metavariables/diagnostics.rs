//! Structured diagnostics shared by logical and Program elaboration.
use crate::hir::{SourceLocation, SourceSpan, SurfaceMeta};
use crate::raw::{environment::CrateEnv, exp::Exp, ids::MetaVarId, printing::Printer};
use std::{error::Error, fmt};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaFlavor {
    Implicit,
    Goal,
    Named(u32),
    Synthetic,
}
impl MetaFlavor {
    pub fn display_name(self, id: MetaVarId) -> String {
        match self {
            Self::Implicit => format!("_#{}", id.0),
            Self::Goal => format!("?#{}", id.0),
            Self::Named(number) => format!("_{number}"),
            Self::Synthetic => format!("<inferred {}>", id.0),
        }
    }
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
    Blocked,
    Failed,
}
#[derive(Debug, Clone)]
pub struct ConstraintRecord {
    pub original: GoalConstraint,
    pub status: ConstraintStatus,
    pub origins: Vec<SourceSpan>,
}

/// A solver outcome, independent of whether the user requested inspection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaState {
    Solved,
    InsufficientInformation,
    Waiting,
    Unsupported,
    Contradiction,
}
impl fmt::Display for MetaState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Solved => "solved (explicit inspection hole)",
            Self::InsufficientInformation => "insufficient information",
            Self::Waiting => "waiting for other metavariables",
            Self::Unsupported => "constraint is not supported by the solver",
            Self::Contradiction => "contradictory constraints",
        })
    }
}

#[derive(Debug, Clone)]
pub struct ConstraintDiagnostic {
    pub original: String,
    pub normalized: String,
    pub status: ConstraintStatus,
    pub origins: Vec<SourceSpan>,
}
impl fmt::Display for ConstraintDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:?}] {}", self.status, self.original)?;
        if self.normalized != self.original {
            write!(f, " => {}", self.normalized)?;
        }
        if !self.origins.is_empty() {
            write!(f, " (from")?;
            for span in &self.origins {
                write!(f, " {}..{}", span.start, span.end)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

/// Render before the declaration's inference arena and name table are released.
#[derive(Debug, Clone)]
pub struct MetaGoal {
    pub metavariable: MetaVarId,
    pub flavor: MetaFlavor,
    pub span: SourceSpan,
    pub occurrences: Vec<SourceSpan>,
    pub context: String,
    pub principal: Option<String>,
    pub solution: Option<String>,
    pub state: MetaState,
    pub constraints: Vec<ConstraintDiagnostic>,
    pub dependencies: Vec<MetaVarId>,
}
impl MetaGoal {
    pub fn display_name(&self) -> String {
        self.flavor.display_name(self.metavariable)
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
        constraints: Vec<ConstraintDiagnostic>,
        goals: Vec<MetaGoal>,
    },
    Metavariables(Vec<MetaGoal>),
}
impl ElaborationError {
    pub fn alternatives(errors: Vec<Self>) -> Self {
        if let Some(index) = errors.iter().position(|error| !error.goals().is_empty()) {
            return errors.into_iter().nth(index).expect("existing error");
        }
        Self::Message(
            errors
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }
    pub fn goals(&self) -> &[MetaGoal] {
        match self {
            Self::Located { error, .. } => error.goals(),
            Self::Metavariables(goals) | Self::ConstraintFailure { goals, .. } => goals,
            Self::Message(_) => &[],
        }
    }
}
impl fmt::Display for ElaborationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Located { location, error } => write!(f, "{error}\n{}", location.render()),
            Self::Message(message) => f.write_str(message),
            Self::ConstraintFailure {
                message,
                constraints,
                goals,
            } => {
                writeln!(f, "{message}")?;
                for constraint in constraints {
                    writeln!(f, "{constraint}")?;
                }
                format_goals(f, goals)
            }
            Self::Metavariables(goals) => format_goals(f, goals),
        }
    }
}
fn format_goals(f: &mut fmt::Formatter<'_>, goals: &[MetaGoal]) -> fmt::Result {
    for (index, goal) in goals.iter().enumerate() {
        if index > 0 {
            writeln!(f)?;
        }
        let kind = match goal.flavor {
            MetaFlavor::Goal => "inspection hole",
            MetaFlavor::Implicit => "implicit metavariable",
            _ => "metavariable",
        };
        writeln!(
            f,
            "{kind} {} at {}..{}: {}",
            goal.display_name(),
            goal.span.start,
            goal.span.end,
            goal.state
        )?;
        writeln!(f, "context: [{}]", goal.context)?;
        writeln!(
            f,
            "goal: {}",
            goal.principal
                .as_deref()
                .unwrap_or("<expected type is unknown>")
        )?;
        if let Some(solution) = &goal.solution {
            writeln!(f, "solution: {solution}")?;
        }
        writeln!(f, "constraints:")?;
        for constraint in &goal.constraints {
            writeln!(f, "  {constraint}")?;
        }
    }
    Ok(())
}
impl Error for ElaborationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Located { error, .. } => Some(error.as_ref()),
            _ => None,
        }
    }
}
pub fn format_elaboration_error(_env: &CrateEnv, error: &ElaborationError) -> String {
    error.to_string()
}
pub fn format_constraint(printer: &Printer<'_>, constraint: &GoalConstraint) -> String {
    let exp = |term| printer.format_exp(term);
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
