//! Structured failures retained across checking, reduction, and unification.
use crate::{
    sort::{BaseSort, ProductRule, Sort},
    syntax::{Arena, Context, Expression, MetaId, Node},
};

#[derive(Debug, Clone)]
pub enum Error {
    InvalidMeta(MetaId),
    TypeMismatch(Box<TypeMismatch>),
    Unresolved {
        metas: Vec<MetaId>,
        constraints: usize,
    },
    Context {
        frame: Frame,
        source: Box<Error>,
    },
    External(std::rc::Rc<dyn diagnostics::DiagnosticError>),
    NoProductRule {
        domain: Sort,
        body: Sort,
    },
    InvalidProductRule {
        rule: ProductRule,
    },
    InvalidReflection {
        node: Box<Node>,
        ty: Option<Box<Node>>,
        sort: Option<BaseSort>,
    },
    BoxPayloadMustBeClosed,
    BoxRequiresAClosedComputationType,
    BoxTypeBinderRequiresProgramKind,
    ProgramDatatypeMirrorDoesNotMatchItsDeclaration,
    ProgramTypeDependsOnAValueParameter,
    ProgramTypeDependsOnAValueVariable,
    ApplicationEvaluationModeMismatch,
    BinderDepthOverflow,
    BoundIndexOverflow,
    BoundVariableOutsideContext,
    BoxedApplicationRequiresBoxAB,
    BoxedFunctionTypeMustBeProduct,
    BoxedTypeApplicationRequiresABoxedTypeAbstraction,
    BoxedTypeArgumentMustBeClosed,
    CaseBranchBinderCountMismatch,
    CaseBranchCountMismatch,
    CaseResultTypeDependsOnFields,
    CaseScrutineeDatatypeMismatch,
    ChoiceFamilyDomainMismatch,
    ChoiceFamilyMustReturnSet,
    ConstructorAppliedToExcessArguments,
    ConstructorDoesNotReturnItsDeclaredInductive,
    ConstructorFieldCountMismatch,
    ConstructorUniverseDoesNotMatchInductive,
    CyclicDefinitionDuringReflection,
    CyclicMetavariableAssignment,
    CyclicMetavariableType,
    DatatypeFieldLevelExceedsResultLevel,
    DatatypeMirrorIdentityIsAlreadyOwned,
    DatatypeParameterKindLevelExceedsResultLevel,
    DefinitionArenaExhausted,
    DefinitionBelongsToADifferentArena,
    DefinitionParameterCountMismatch,
    DifferentEqualityCarriers,
    DuplicateProgramDatatype,
    DuplicateInductive,
    EliminatorCaseCountMismatch,
    EliminatorScrutineeDatatypeMismatch,
    EmptyCaseNeedsAnExpectedType,
    ExpectedSetI,
    ExpectedSetOrProp,
    ExpectedADefinitionHead,
    ExpectedADefinitionRedex,
    ExpectedAProduct,
    ExpectedASort,
    ExpectedATypeOfBaseKind,
    ExpectedDeclaredConstructorProduct,
    ExpectedInduction,
    ExpectedProposition,
    ExpressionDependsOnRemovedBinder,
    ForbiddenLargeElimination,
    ForceRequiresUB,
    HeadNormalizationFuelExhausted,
    IncompatibleBinderStructure,
    RigidMismatch,
    IncorrectProgramTypeSort,
    IndexOverflow,
    InductiveArityDoesNotEndInItsDeclaredSort,
    InductiveOccursInANonStrictlyPositivePosition,
    InductiveOccursInItsParameterTelescopeOrArity,
    InvalidCaseBranchSlot,
    InvalidMetavariableScopeRestriction,
    InvalidMotiveBinderSlot,
    InvalidStepMatchMotiveSort,
    LambdaEvaluationModeMismatch,
    MetavariableArgumentCountMismatch,
    EscapingSharedVariable,
    EscapingVariable,
    MissingBranch,
    MissingCaseBinders,
    MissingEliminationBranch,
    MissingMetaAssignment,
    MissingReflectedDefinition,
    MissingReflectedParameterModes,
    ModuleParameterAnnotationMustBeAType,
    ModuleParametersMustBeCapturedInTheDeclarationTelescope,
    MotiveArgumentCountMismatch,
    MotiveDomainMismatch,
    MotiveTelescopeLengthMismatch,
    NormalizationFuelExhausted,
    OccursCheck,
    ParameterCountMismatch,
    ParameterIdentityAlreadyRegistered,
    RecursionTypesMustInhabitTheSameSetIOrValueUniverse,
    ReflectionRequiresAProgramDefinition,
    SetextRequiresPowersetElements,
    SnapshotBelongsToADifferentMetavariableSession,
    SourceDefinitionWasNotResolved,
    StepMatchMotiveDomainMismatch,
    StepMatchMotiveMustReturnAClassifier,
    UnknownBinderStructure,
    UnknownCaseBranch,
    UnknownConstructor,
    UnknownDatatype,
    UnknownDefinition,
    UnknownInductive,
    UnknownModuleParameter,
    UnresolvedReflectionMetavariable,
    UpperSortHasNoClassifier,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Frame {
    Rule(&'static str),
    Check(&'static str),
}
impl std::fmt::Display for Frame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Rule(rule) => write!(f, "rule: {rule:?}"),
            Self::Check(check) => f.write_str(check),
        }
    }
}
impl Error {
    pub fn root(&self) -> &Self {
        match self {
            Self::Context { source, .. } => source.root(),
            other => other,
        }
    }
    pub fn is_rigid_failure(&self) -> bool {
        matches!(
            self.root(),
            Self::TypeMismatch(_)
                | Self::RigidMismatch
                | Self::EscapingVariable
                | Self::EscapingSharedVariable
                | Self::OccursCheck
        )
    }
    pub(crate) fn at(mut self, frame: Frame) -> Self {
        if let Self::TypeMismatch(error) = &mut self {
            error.frames.push(frame);
            self
        } else {
            Self::Context {
                frame,
                source: Box::new(self),
            }
        }
    }
    pub fn external(error: impl diagnostics::DiagnosticError + 'static) -> Self {
        Self::External(std::rc::Rc::new(error))
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidMeta(id) => write!(f, "invalid metavariable {id:?}"),
            Self::TypeMismatch(_) => f.write_str("types are not convertible"),
            Self::Unresolved { metas, constraints } => write!(
                f,
                "unresolved metavariables {metas:?}; {constraints} pending constraints"
            ),
            Self::Context { frame, source } => write!(f, "{source}\n{frame}"),
            Self::External(source) => source.fmt(f),
            Self::NoProductRule { domain, body } => {
                write!(f, "no product rule for domain {domain} and body {body}")
            }
            Self::InvalidProductRule { .. } => f.write_str("invalid product rule label"),
            Self::InvalidReflection { node, ty, sort } => {
                write!(f, "reflection requires a Program expression: {node:?}")?;
                if let Some(ty) = ty {
                    write!(f, " : {ty:?}")?;
                }
                if let Some(sort) = sort {
                    write!(f, " ({sort:?})")?;
                }
                Ok(())
            }
            Self::BoxPayloadMustBeClosed => f.write_str("Box payload must be closed"),
            Self::BoxRequiresAClosedComputationType => {
                f.write_str("Box requires a closed computation type")
            }
            Self::BoxTypeBinderRequiresProgramKind => {
                f.write_str("Box type binder requires Program kind")
            }
            Self::ProgramDatatypeMirrorDoesNotMatchItsDeclaration => {
                f.write_str("Program datatype mirror does not match its declaration")
            }
            Self::ProgramTypeDependsOnAValueParameter => {
                f.write_str("Program type depends on a value parameter")
            }
            Self::ProgramTypeDependsOnAValueVariable => {
                f.write_str("Program type depends on a value variable")
            }
            Self::ApplicationEvaluationModeMismatch => {
                f.write_str("application evaluation mode mismatch")
            }
            Self::BinderDepthOverflow => f.write_str("binder depth overflow"),
            Self::BoundIndexOverflow => f.write_str("bound index overflow"),
            Self::BoundVariableOutsideContext => f.write_str("bound variable outside context"),
            Self::BoxedApplicationRequiresBoxAB => {
                f.write_str("boxed application requires Box(A -> B)")
            }
            Self::BoxedFunctionTypeMustBeProduct => {
                f.write_str("boxed function type must be product")
            }
            Self::BoxedTypeApplicationRequiresABoxedTypeAbstraction => {
                f.write_str("boxed type application requires a boxed type abstraction")
            }
            Self::BoxedTypeArgumentMustBeClosed => {
                f.write_str("boxed type argument must be closed")
            }
            Self::CaseBranchBinderCountMismatch => f.write_str("case branch binder count mismatch"),
            Self::CaseBranchCountMismatch => f.write_str("case branch count mismatch"),
            Self::CaseResultTypeDependsOnFields => {
                f.write_str("case result type depends on fields")
            }
            Self::CaseScrutineeDatatypeMismatch => f.write_str("case scrutinee datatype mismatch"),
            Self::ChoiceFamilyDomainMismatch => f.write_str("choice family domain mismatch"),
            Self::ChoiceFamilyMustReturnSet => f.write_str("choice family must return Set"),
            Self::ConstructorAppliedToExcessArguments => {
                f.write_str("constructor applied to excess arguments")
            }
            Self::ConstructorDoesNotReturnItsDeclaredInductive => {
                f.write_str("constructor does not return its declared inductive")
            }
            Self::ConstructorFieldCountMismatch => f.write_str("constructor field count mismatch"),
            Self::ConstructorUniverseDoesNotMatchInductive => {
                f.write_str("constructor universe does not match inductive")
            }
            Self::CyclicDefinitionDuringReflection => {
                f.write_str("cyclic definition during reflection")
            }
            Self::CyclicMetavariableAssignment => f.write_str("cyclic metavariable assignment"),
            Self::CyclicMetavariableType => f.write_str("cyclic metavariable type"),
            Self::DatatypeFieldLevelExceedsResultLevel => {
                f.write_str("datatype field level exceeds result level")
            }
            Self::DatatypeMirrorIdentityIsAlreadyOwned => {
                f.write_str("datatype mirror identity is already owned")
            }
            Self::DatatypeParameterKindLevelExceedsResultLevel => {
                f.write_str("datatype parameter kind level exceeds result level")
            }
            Self::DefinitionArenaExhausted => f.write_str("definition arena exhausted"),
            Self::DefinitionBelongsToADifferentArena => {
                f.write_str("definition belongs to a different arena")
            }
            Self::DefinitionParameterCountMismatch => {
                f.write_str("definition parameter count mismatch")
            }
            Self::DifferentEqualityCarriers => f.write_str("different equality carriers"),
            Self::DuplicateProgramDatatype => f.write_str("duplicate Program datatype"),
            Self::DuplicateInductive => f.write_str("duplicate inductive"),
            Self::EliminatorCaseCountMismatch => f.write_str("eliminator case count mismatch"),
            Self::EliminatorScrutineeDatatypeMismatch => {
                f.write_str("eliminator scrutinee datatype mismatch")
            }
            Self::EmptyCaseNeedsAnExpectedType => f.write_str("empty case needs an expected type"),
            Self::ExpectedSetOrProp => f.write_str("expected a Set(i) or Prop equality family"),
            Self::ExpectedSetI => f.write_str("expected Set(i)"),
            Self::ExpectedADefinitionHead => f.write_str("expected a definition head"),
            Self::ExpectedADefinitionRedex => f.write_str("expected a definition redex"),
            Self::ExpectedAProduct => f.write_str("expected a product"),
            Self::ExpectedASort => f.write_str("expected a sort"),
            Self::ExpectedATypeOfBaseKind => f.write_str("expected a type of base kind"),
            Self::ExpectedDeclaredConstructorProduct => {
                f.write_str("expected declared constructor product")
            }
            Self::ExpectedInduction => f.write_str("expected induction"),
            Self::ExpectedProposition => f.write_str("expected proposition"),
            Self::ExpressionDependsOnRemovedBinder => {
                f.write_str("expression depends on removed binder")
            }
            Self::ForbiddenLargeElimination => f.write_str("forbidden large elimination"),
            Self::ForceRequiresUB => f.write_str("force requires U(B)"),
            Self::HeadNormalizationFuelExhausted => {
                f.write_str("head normalization fuel exhausted")
            }
            Self::IncompatibleBinderStructure => f.write_str("incompatible binder structure"),
            Self::RigidMismatch => {
                f.write_str("incompatible rigid expressions in metavariable constraint")
            }
            Self::IncorrectProgramTypeSort => f.write_str("incorrect Program type sort"),
            Self::IndexOverflow => f.write_str("index overflow"),
            Self::InductiveArityDoesNotEndInItsDeclaredSort => {
                f.write_str("inductive arity does not end in its declared sort")
            }
            Self::InductiveOccursInANonStrictlyPositivePosition => {
                f.write_str("inductive occurs in a non-strictly-positive position")
            }
            Self::InductiveOccursInItsParameterTelescopeOrArity => {
                f.write_str("inductive occurs in its parameter telescope or arity")
            }
            Self::InvalidCaseBranchSlot => f.write_str("invalid case branch slot"),
            Self::InvalidMetavariableScopeRestriction => {
                f.write_str("invalid metavariable scope restriction")
            }
            Self::InvalidMotiveBinderSlot => f.write_str("invalid motive binder slot"),
            Self::InvalidStepMatchMotiveSort => f.write_str("invalid step match motive sort"),
            Self::LambdaEvaluationModeMismatch => f.write_str("lambda evaluation mode mismatch"),
            Self::MetavariableArgumentCountMismatch => {
                f.write_str("metavariable argument count mismatch")
            }
            Self::EscapingSharedVariable => {
                f.write_str("metavariable captures a variable outside its shared context")
            }
            Self::EscapingVariable => {
                f.write_str("metavariable solution captures a variable outside its context")
            }
            Self::MissingBranch => f.write_str("missing branch"),
            Self::MissingCaseBinders => f.write_str("missing case binders"),
            Self::MissingEliminationBranch => f.write_str("missing elimination branch"),
            Self::MissingMetaAssignment => f.write_str("missing meta assignment"),
            Self::MissingReflectedDefinition => f.write_str("missing reflected definition"),
            Self::MissingReflectedParameterModes => {
                f.write_str("missing reflected parameter modes")
            }
            Self::ModuleParameterAnnotationMustBeAType => {
                f.write_str("module parameter annotation must be a type")
            }
            Self::ModuleParametersMustBeCapturedInTheDeclarationTelescope => {
                f.write_str("module parameters must be captured in the declaration telescope")
            }
            Self::MotiveArgumentCountMismatch => f.write_str("motive argument count mismatch"),
            Self::MotiveDomainMismatch => f.write_str("motive domain mismatch"),
            Self::MotiveTelescopeLengthMismatch => f.write_str("motive telescope length mismatch"),
            Self::NormalizationFuelExhausted => f.write_str("normalization fuel exhausted"),
            Self::OccursCheck => f.write_str("occurs check failed"),
            Self::ParameterCountMismatch => f.write_str("parameter count mismatch"),
            Self::ParameterIdentityAlreadyRegistered => {
                f.write_str("parameter identity already registered")
            }
            Self::RecursionTypesMustInhabitTheSameSetIOrValueUniverse => {
                f.write_str("recursion types must inhabit the same Set(i) or value universe")
            }
            Self::ReflectionRequiresAProgramDefinition => {
                f.write_str("reflection requires a Program definition")
            }
            Self::SetextRequiresPowersetElements => {
                f.write_str("setext requires powerset elements")
            }
            Self::SnapshotBelongsToADifferentMetavariableSession => {
                f.write_str("snapshot belongs to a different metavariable session")
            }
            Self::SourceDefinitionWasNotResolved => {
                f.write_str("source definition was not resolved")
            }
            Self::StepMatchMotiveDomainMismatch => f.write_str("step match motive domain mismatch"),
            Self::StepMatchMotiveMustReturnAClassifier => {
                f.write_str("step match motive must return a classifier")
            }
            Self::UnknownBinderStructure => f.write_str("unknown binder structure"),
            Self::UnknownCaseBranch => f.write_str("unknown case branch"),
            Self::UnknownConstructor => f.write_str("unknown constructor"),
            Self::UnknownDatatype => f.write_str("unknown datatype"),
            Self::UnknownDefinition => f.write_str("unknown definition"),
            Self::UnknownInductive => f.write_str("unknown inductive"),
            Self::UnknownModuleParameter => f.write_str("unknown module parameter"),
            Self::UnresolvedReflectionMetavariable => {
                f.write_str("unresolved reflection metavariable")
            }
            Self::UpperSortHasNoClassifier => f.write_str("upper sort has no classifier"),
        }
    }
}
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Context { source, .. } => Some(source.as_ref()),
            Self::External(source) => Some(source.as_ref()),
            _ => None,
        }
    }
}
#[derive(Debug, Clone)]
pub struct TypeMismatch {
    pub arena: Arena,
    pub context: Context,
    pub term: Expression,
    pub inferred: Expression,
    pub expected: Expression,
    pub frames: Vec<Frame>,
}

impl diagnostics::DiagnosticError for Error {
    fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        use diagnostics::{DiagnosticData as Data, Value};
        match self {
            Self::Context { frame, source } => Data::new("kernel.Context")
                .with("frame", frame.diagnostic_data())
                .caused_by(source.diagnostic_data()),
            Self::External(source) => source.diagnostic_data(),
            Self::InvalidMeta(id) => Data::new("kernel.InvalidMeta").with("id", format!("{id:?}")),
            Self::Unresolved { metas, constraints } => Data::new("kernel.Unresolved")
                .with(
                    "metas",
                    Value::List(metas.iter().map(|id| format!("{id:?}").into()).collect()),
                )
                .with("constraints", *constraints),
            Self::NoProductRule { domain, body } => Data::new("kernel.NoProductRule")
                .with("domain", domain.to_string())
                .with("body", body.to_string()),
            Self::InvalidProductRule { rule } => Data::new("kernel.InvalidProductRule")
                .with("domain", rule.domain.to_string())
                .with("body", rule.body.to_string())
                .with("result", rule.result.to_string()),
            Self::InvalidReflection { node, ty, sort } => {
                let mut data =
                    Data::new("kernel.InvalidReflection").with("node", format!("{node:?}"));
                if let Some(ty) = ty {
                    data = data.with("type", format!("{ty:?}"));
                }
                if let Some(sort) = sort {
                    data = data.with("sort", format!("{sort:?}"));
                }
                data
            }
            Self::TypeMismatch(error) => Data::new("kernel.TypeMismatch")
                .with("term", format!("{:?}", error.arena.get(error.term)))
                .with("inferred", format!("{:?}", error.arena.get(error.inferred)))
                .with("expected", format!("{:?}", error.arena.get(error.expected)))
                .with(
                    "context",
                    Value::List(
                        error
                            .context
                            .iter()
                            .map(|binding| {
                                Data::new("kernel.Binding")
                                    .with("name", format!("{:?}", binding.var))
                                    .with("type", format!("{:?}", error.arena.get(binding.ty)))
                                    .into()
                            })
                            .collect(),
                    ),
                )
                .with(
                    "frames",
                    Value::List(
                        error
                            .frames
                            .iter()
                            .map(|frame| frame.diagnostic_data().into())
                            .collect(),
                    ),
                ),
            other => Data::new(format!("kernel.{other:?}")),
        }
    }
}

impl Frame {
    fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        match self {
            Self::Rule(rule) => diagnostics::DiagnosticData::new("kernel.Rule").with("rule", *rule),
            Self::Check(operation) => {
                diagnostics::DiagnosticData::new("kernel.Check").with("operation", *operation)
            }
        }
    }
}
