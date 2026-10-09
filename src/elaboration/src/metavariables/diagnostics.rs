//! Structured diagnostics shared by logical and Program elaboration.
use crate::hir::{SourceLocation, SourceSpan, SurfaceMeta};
use crate::raw::{environment::CrateEnv, exp::Exp, ids::MetaVarId, printing::Printer};
use std::fmt;

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
    pub core: Option<kernel::metavariables::Constraint>,
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
    pub omitted_origins: usize,
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
        if self.omitted_origins > 0 {
            write!(f, " ({} origins omitted)", self.omitted_origins)?;
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
    pub omitted_constraints: usize,
    pub omitted_goals: usize,
    pub dependencies: Vec<MetaVarId>,
}
impl MetaGoal {
    pub fn display_name(&self) -> String {
        self.flavor.display_name(self.metavariable)
    }
}

#[derive(Debug, Clone)]
pub enum ElaborationError {
    Alternatives(Vec<ElaborationError>),
    Deferred {
        summary: Box<ElaborationError>,
        details: std::rc::Rc<DeferredDetails>,
    },
    Located {
        location: SourceLocation,
        error: Box<ElaborationError>,
    },
    Failure(crate::error::Error),
    ConstraintFailure {
        cause: Box<crate::error::Error>,
        constraints: Vec<ConstraintDiagnostic>,
        goals: Vec<MetaGoal>,
        omitted_constraints: usize,
    },
    Metavariables(Vec<MetaGoal>),
}
#[derive(Debug)]
pub struct DeferredDetails {
    state: DeferredState,
}
#[derive(Debug)]
enum DeferredState {
    Logical(super::MetaStore, Option<crate::error::Error>),
    Program(
        crate::elaborator::program_term_elaborator::ProgramScope,
        Option<crate::error::Error>,
    ),
}

impl ElaborationError {
    pub(crate) fn materialize(&self, env: &crate::elaborator::GlobalEnvironment) -> Self {
        let _profile = crate::diagnostics::DiagnosticProfile::start("details");
        match self {
            Self::Located { location, error } => Self::Located {
                location: location.clone(),
                error: Box::new(error.materialize(env)),
            },
            Self::Deferred { summary, details } => {
                if crate::diagnostics::compact() {
                    return *summary.clone();
                }
                match &details.state {
                    DeferredState::Logical(store, Some(message)) => {
                        store.detailed_error(&env.crate_env, message.clone())
                    }
                    DeferredState::Logical(store, None) => {
                        Self::Metavariables(store.goals(&env.crate_env))
                    }
                    DeferredState::Program(scope, Some(message)) => {
                        scope.detailed_error(env, message.clone())
                    }
                    DeferredState::Program(scope, None) => Self::Metavariables(scope.goals(env)),
                }
            }
            Self::Alternatives(errors) => {
                Self::Alternatives(errors.iter().map(|error| error.materialize(env)).collect())
            }
            Self::Failure(error) => Self::Failure(error.materialize(env)),
            other => other.clone(),
        }
    }

    pub fn alternatives(errors: Vec<Self>) -> Self {
        if let Some(index) = errors.iter().position(|error| !error.goals().is_empty()) {
            return errors.into_iter().nth(index).expect("existing error");
        }
        Self::Alternatives(errors)
    }
    pub fn goals(&self) -> &[MetaGoal] {
        match self {
            Self::Located { error, .. } | Self::Deferred { summary: error, .. } => error.goals(),
            Self::Metavariables(goals) | Self::ConstraintFailure { goals, .. } => goals,
            Self::Failure(error) => error.goals(),
            Self::Alternatives(_) => &[],
        }
    }
}
impl fmt::Display for ElaborationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Alternatives(errors) => {
                for (index, error) in errors.iter().enumerate() {
                    if index > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "{error}")?;
                }
                Ok(())
            }
            Self::Deferred { summary, .. } => summary.fmt(f),
            Self::Located { location, error } => write!(f, "{error}\n{}", location.render()),
            Self::Failure(error) => error.fmt(f),
            Self::ConstraintFailure {
                cause,
                constraints,
                goals,
                omitted_constraints,
            } => {
                writeln!(f, "{cause}")?;
                for constraint in constraints {
                    writeln!(f, "{constraint}")?;
                }
                if *omitted_constraints > 0 {
                    writeln!(f, "… {omitted_constraints} constraints omitted")?;
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
        if !goal.constraints.is_empty() {
            writeln!(f, "constraints:")?;
        }
        for constraint in &goal.constraints {
            writeln!(f, "  {constraint}")?;
        }
        if goal.omitted_constraints > 0 {
            writeln!(
                f,
                "  … {} constraints omitted or not searched",
                goal.omitted_constraints
            )?;
        }
        if goal.omitted_goals > 0 {
            writeln!(f, "… {} goals omitted", goal.omitted_goals)?;
        }
    }
    Ok(())
}
pub fn format_elaboration_error(env: &CrateEnv, error: &ElaborationError) -> String {
    struct Rendered<'a> {
        env: &'a CrateEnv,
        error: &'a ElaborationError,
    }
    impl fmt::Display for Rendered<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let nested = |error| Rendered {
                env: self.env,
                error,
            };
            match self.error {
                ElaborationError::Alternatives(errors) => {
                    for (index, error) in errors.iter().enumerate() {
                        if index > 0 {
                            writeln!(f)?;
                        }
                        write!(f, "{}", nested(error))?;
                    }
                    Ok(())
                }
                ElaborationError::Deferred { summary, .. } => nested(summary).fmt(f),
                ElaborationError::Located { location, error } => {
                    write!(f, "{}\n{}", nested(error), location.render())
                }
                ElaborationError::Failure(error) => f.write_str(&error.render(self.env)),
                ElaborationError::ConstraintFailure {
                    cause,
                    constraints,
                    goals,
                    omitted_constraints,
                } => {
                    writeln!(f, "{}", cause.render(self.env))?;
                    for constraint in constraints {
                        writeln!(f, "{constraint}")?;
                    }
                    if *omitted_constraints > 0 {
                        writeln!(f, "… {omitted_constraints} constraints omitted")?;
                    }
                    format_goals(f, goals)
                }
                ElaborationError::Metavariables(goals) => format_goals(f, goals),
            }
        }
    }
    Rendered { env, error }.to_string()
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

impl From<crate::error::Error> for ElaborationError {
    fn from(error: crate::error::Error) -> Self {
        Self::Failure(error)
    }
}
impl From<kernel::error::Error> for ElaborationError {
    fn from(error: kernel::error::Error) -> Self {
        Self::Failure(error.into())
    }
}
impl From<syntax::error::ConversionError> for ElaborationError {
    fn from(error: syntax::error::ConversionError) -> Self {
        Self::Failure(error.into())
    }
}

impl std::error::Error for ElaborationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Failure(error) => Some(error),
            Self::ConstraintFailure { cause, .. } => Some(cause.as_ref()),
            Self::Located { error, .. } | Self::Deferred { summary: error, .. } => {
                Some(error.as_ref())
            }
            _ => None,
        }
    }
}
impl From<Box<crate::error::Error>> for ElaborationError {
    fn from(error: Box<crate::error::Error>) -> Self {
        Self::Failure(*error)
    }
}
impl From<crate::raw::reflection::ReflectionError> for ElaborationError {
    fn from(error: crate::raw::reflection::ReflectionError) -> Self {
        Self::Failure(error.into())
    }
}

impl diagnostics::DiagnosticError for ElaborationError {
    fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        use diagnostics::DiagnosticData as Data;
        match self {
            Self::Failure(error) => error.diagnostic_data(),
            Self::ConstraintFailure {
                cause,
                constraints,
                goals,
                omitted_constraints,
            } => Data::new("elaboration.ConstraintFailure")
                .caused_by(cause.diagnostic_data())
                .with("constraints", constraint_data(constraints))
                .with("goals", goal_data(goals))
                .with("omitted_constraints", *omitted_constraints),
            Self::Located { location, error } => error
                .diagnostic_data()
                .with("file", location.source.id.0.to_string_lossy().into_owned())
                .with("start", location.span.start)
                .with("end", location.span.end),
            Self::Deferred { summary, .. } => summary.diagnostic_data(),
            Self::Alternatives(errors) => {
                let mut data = Data::new("elaboration.Alternatives");
                data.causes = errors.iter().map(|error| error.diagnostic_data()).collect();
                data
            }
            Self::Metavariables(goals) => {
                Data::new("elaboration.Metavariables").with("goals", goal_data(goals))
            }
        }
    }
}

fn span_data(span: SourceSpan) -> diagnostics::DiagnosticData {
    diagnostics::DiagnosticData::new("syntax.SourceSpan")
        .with("start", span.start)
        .with("end", span.end)
}

fn constraint_data(constraints: &[ConstraintDiagnostic]) -> diagnostics::Value {
    diagnostics::Value::List(
        constraints
            .iter()
            .map(|constraint| {
                diagnostics::DiagnosticData::new("elaboration.Constraint")
                    .with("original", constraint.original.clone())
                    .with("normalized", constraint.normalized.clone())
                    .with("status", format!("{:?}", constraint.status))
                    .with(
                        "origins",
                        diagnostics::Value::List(
                            constraint
                                .origins
                                .iter()
                                .map(|span| span_data(*span).into())
                                .collect(),
                        ),
                    )
                    .with("omitted_origins", constraint.omitted_origins)
                    .into()
            })
            .collect(),
    )
}

fn goal_data(goals: &[MetaGoal]) -> diagnostics::Value {
    diagnostics::Value::List(
        goals
            .iter()
            .map(|goal| {
                let mut data = diagnostics::DiagnosticData::new("elaboration.Goal")
                    .with("name", goal.display_name())
                    .with("metavariable", goal.metavariable.0)
                    .with("flavor", format!("{:?}", goal.flavor))
                    .with("state", format!("{:?}", goal.state))
                    .with("span", span_data(goal.span))
                    .with(
                        "occurrences",
                        diagnostics::Value::List(
                            goal.occurrences
                                .iter()
                                .map(|span| span_data(*span).into())
                                .collect(),
                        ),
                    )
                    .with("context", goal.context.clone())
                    .with("constraints", constraint_data(&goal.constraints))
                    .with("omitted_constraints", goal.omitted_constraints)
                    .with("omitted_goals", goal.omitted_goals)
                    .with(
                        "dependencies",
                        diagnostics::Value::List(
                            goal.dependencies.iter().map(|id| id.0.into()).collect(),
                        ),
                    );
                if let Some(principal) = &goal.principal {
                    data = data.with("principal", principal.clone());
                }
                if let Some(solution) = &goal.solution {
                    data = data.with("solution", solution.clone());
                }
                data.into()
            })
            .collect(),
    )
}

impl DeferredDetails {
    pub(crate) fn logical(store: super::MetaStore, error: Option<crate::error::Error>) -> Self {
        Self {
            state: DeferredState::Logical(store, error),
        }
    }
    pub(crate) fn program(
        scope: crate::elaborator::program_term_elaborator::ProgramScope,
        error: Option<crate::error::Error>,
    ) -> Self {
        Self {
            state: DeferredState::Program(scope, error),
        }
    }
}
