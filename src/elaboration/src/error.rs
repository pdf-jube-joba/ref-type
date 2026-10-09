//! Errors retained by elaboration until a diagnostic is rendered.
use crate::raw::environment::CrateEnv;

mod context;
mod data;
mod invalid;
pub use context::{Context, ParameterRequirement};
pub use invalid::Invalid;

#[derive(Debug, Clone)]
pub enum Error {
    Kernel(kernel::error::Error),
    Elaboration(Box<crate::metavariables::ElaborationError>),
    Conversion(syntax::error::ConversionError),
    Resolution(Box<resolve::Diagnostic>),
    Reflection(Box<crate::raw::reflection::ReflectionError>),
    Invalid(Invalid),
    Context {
        context: Context,
        source: Box<Error>,
    },
    DuplicateMaterialization {
        id: crate::raw::ids::DefId,
    },
    UncapturedParameter {
        id: crate::raw::ids::ModuleParamId,
        module: String,
        captures: Vec<crate::raw::ids::ModuleParamId>,
    },
    UnknownAccess {
        access_path: resolve::hir::LocalAccess,
    },
    ProjectionFromStructureType {
        field: String,
        name: String,
    },
    UnknownRecordField {
        field: String,
    },
    ReflectedTypeArgumentCountMismatch {
        actual: usize,
        expected: usize,
    },
    UnresolvedExternalModule {
        name: String,
    },
    ReservedDefinitionUsed {
        id: crate::raw::ids::DefId,
    },
    CyclicDefinition {
        id: crate::raw::ids::DefId,
    },
    DuplicateModuleItem {
        name: String,
    },
    UnknownAssociatedOwner {
        owner: String,
    },
    AssociatedOwnerNotAType {
        owner: String,
    },
    DuplicateAssociatedItem {
        owner: String,
        name: String,
    },
    DuplicateModuleImport {
        name: String,
    },
    UnknownModuleImport {
        name: String,
    },
    UnknownChildModule {
        name: String,
    },
    ModuleArgumentCountMismatch {
        name: String,
    },
    ModuleArgumentNameMismatch {
        name: String,
    },
    InvalidAssociatedOwner {
        name: String,
    },
    AssociatedDefinitionArgumentCountMismatch {
        owner: String,
        name: String,
        expected: usize,
        actual: usize,
    },
    ProgramOwnerArgumentCountMismatch {
        actual: usize,
        expected: usize,
    },
    DuplicateRecordField {
        name: String,
    },
    DuplicateProgramConstructor {
        name: String,
    },
    ProgramConstructorResultMismatch {
        constructor: String,
        datatype: String,
    },
    ProgramConstructorParameterMismatch {
        constructor: String,
        datatype: String,
    },
    UnknownChildInModule {
        name: String,
        module: String,
    },
    ModuleArgumentArityMismatch {
        module: String,
        expected: usize,
        actual: usize,
    },
    ModuleArgumentLabelMismatch {
        module: String,
        expected: String,
        actual: String,
    },
    ModuleArgumentCategoryMismatch {
        module: String,
        argument: String,
    },
    ProgramTypeArgumentCountMismatch {
        actual: usize,
        expected: usize,
    },
    UnknownProgramName {
        access: resolve::hir::LocalAccess,
    },
    NotProgramValueType {
        access: resolve::hir::LocalAccess,
    },
    DuplicateStructureField {
        name: String,
    },
    UnknownStructureField {
        name: String,
    },
    MissingStructureField {
        name: String,
    },
    NotProgramValue {
        access: resolve::hir::LocalAccess,
    },
    UnknownProgramAssociatedItem {
        name: String,
    },
    UnknownProgramConstructor {
        name: String,
    },
    UnknownProgramRecordField {
        field: String,
        record: String,
    },
    ProgramBranchBinderCountMismatch {
        constructor: String,
    },
    DefinitionArgumentCountMismatch {
        expected: usize,
        actual: usize,
    },
    TypeArgumentCountMismatch {
        actual: usize,
        expected: usize,
    },
    InductiveBranchCountMismatch {
        expected: usize,
        actual: usize,
    },
    UnknownInductiveConstructor {
        name: String,
    },
    DuplicateInductiveBranch {
        name: String,
    },
    MissingInductiveBranch {
        name: String,
    },
    BranchBinderCountMismatch {
        constructor: String,
        actual: usize,
        field_count: usize,
    },
    ExcessBranchBinders {
        constructor: String,
    },
    DefinitionNeedsReflection {
        access: resolve::hir::LocalAccess,
    },
    NameNeedsReflection {
        access: resolve::hir::LocalAccess,
    },
    AssociatedReflectionNeedsDatatype {
        field: String,
    },
    UnknownInductiveAssociatedItem {
        name: String,
        datatype: String,
    },
    UnknownStructureAssociatedItem {
        name: String,
        structure: String,
    },
    InvalidAssociatedBase {
        base: Box<resolve::hir::SExp>,
    },
    EscapedMacroCapture {
        name: String,
    },
    InvalidCasePath {
        path: resolve::hir::LocalAccess,
    },
    IncompatibleMetaUses {
        number: u32,
    },
}

impl Error {
    pub fn context(self, context: Context) -> Self {
        Self::Context {
            context,
            source: Box::new(self),
        }
    }
    pub(crate) fn goals(&self) -> &[crate::metavariables::MetaGoal] {
        match self {
            Self::Elaboration(error) => error.goals(),
            Self::Context { source, .. } => source.goals(),
            _ => &[],
        }
    }
    pub(crate) fn materialize(&self, env: &crate::elaborator::GlobalEnvironment) -> Self {
        match self {
            Self::Elaboration(error) => Self::Elaboration(Box::new(error.materialize(env))),
            Self::Context { context, source } => Self::Context {
                context: context.clone(),
                source: Box::new(source.materialize(env)),
            },
            other => other.clone(),
        }
    }
    pub(crate) fn render(&self, env: &CrateEnv) -> String {
        match self {
            Self::Kernel(error) => crate::lowering::format_kernel_error(env, error),
            Self::Context { context, source } => format!("{context}: {}", source.render(env)),
            Self::Elaboration(error) => crate::metavariables::format_elaboration_error(env, error),
            other => other.to_string(),
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateMaterialization { id } => {
                write!(f, "definition {id:?} was materialized twice")
            }
            Self::UncapturedParameter {
                id,
                module,
                captures,
            } => write!(
                f,
                "uncaptured parameter {id:?} from {module}; captured parameters: {captures:?}"
            ),

            Self::Kernel(error) => error.fmt(f),
            Self::Elaboration(error) => error.fmt(f),
            Self::Conversion(error) => error.fmt(f),
            Self::Resolution(error) => error.fmt(f),
            Self::Reflection(error) => error.fmt(f),
            Self::Invalid(error) => error.fmt(f),
            Self::Context { context, source } => write!(f, "{context}: {source}"),
            Self::UnknownAccess { access_path } => {
                write!(f, "Failed to access item at path {access_path:?}")
            }
            Self::ProjectionFromStructureType { field, name } => write!(
                f,
                "Cannot project field '{field}' from structure type '{name}'; use a structure value (e.g. data.{field}) or {name}::{field} for the projection function"
            ),
            Self::UnknownRecordField { field } => {
                write!(f, "Field {} not found in record or its laws", field)
            }
            Self::ReflectedTypeArgumentCountMismatch { actual, expected } => write!(
                f,
                "reflected Program item expects {expected} type parameter(s), found {}",
                actual
            ),
            Self::UnresolvedExternalModule { name } => {
                write!(f, "External module '{}' was not resolved", name)
            }
            Self::ReservedDefinitionUsed { id } => {
                write!(f, "reserved definition {id:?} was used before definition")
            }
            Self::CyclicDefinition { id } => {
                write!(f, "cyclic lazy definition dependency at {id:?}")
            }
            Self::DuplicateModuleItem { name } => {
                write!(f, "Module item '{name}' is already defined")
            }
            Self::UnknownAssociatedOwner { owner } => {
                write!(f, "Associated item owner '{owner}' was not found")
            }
            Self::AssociatedOwnerNotAType { owner } => {
                write!(f, "Module item '{owner}' is not a type")
            }
            Self::DuplicateAssociatedItem { owner, name } => {
                write!(f, "Associated item '{owner}::{name}' is already defined")
            }
            Self::DuplicateModuleImport { name } => {
                write!(f, "Module import '{name}' is already defined")
            }
            Self::UnknownModuleImport { name } => {
                write!(f, "Module import '{}' was not found", name)
            }
            Self::UnknownChildModule { name } => write!(f, "child module '{}' was not found", name),
            Self::ModuleArgumentCountMismatch { name } => {
                write!(f, "module '{}' argument count mismatch", name)
            }
            Self::ModuleArgumentNameMismatch { name } => {
                write!(f, "module '{}' argument name mismatch", name)
            }
            Self::InvalidAssociatedOwner { name } => write!(
                f,
                "Associated item owner '{}' is not a type in this module",
                name
            ),
            Self::AssociatedDefinitionArgumentCountMismatch {
                owner,
                name,
                expected,
                actual,
            } => write!(
                f,
                "Associated definition {}::{} expects {} owner parameter(s), found {}",
                owner, name, expected, actual
            ),
            Self::ProgramOwnerArgumentCountMismatch { actual, expected } => write!(
                f,
                "Program associated item expects {expected} owner parameter(s), found {}",
                actual
            ),
            Self::DuplicateRecordField { name } => {
                write!(f, "duplicate record field name: {}", name)
            }
            Self::DuplicateProgramConstructor { name } => {
                write!(f, "duplicate Program constructor name: {}", name)
            }
            Self::ProgramConstructorResultMismatch {
                constructor,
                datatype,
            } => write!(
                f,
                "Program constructor {} must return {}",
                constructor, datatype
            ),
            Self::ProgramConstructorParameterMismatch {
                constructor,
                datatype,
            } => write!(
                f,
                "Program constructor {} must return {} with all datatype parameters",
                constructor, datatype
            ),
            Self::UnknownChildInModule { name, module } => write!(
                f,
                "Child module '{}' not found in module '{}'",
                name, module
            ),
            Self::ModuleArgumentArityMismatch {
                module,
                expected,
                actual,
            } => write!(
                f,
                "Argument length mismatch for module '{}': expected {}, got {}",
                module, expected, actual
            ),
            Self::ModuleArgumentLabelMismatch {
                module,
                expected,
                actual,
            } => write!(
                f,
                "Argument name mismatch for module '{}': expected '{}', got '{}'",
                module, expected, actual
            ),
            Self::ModuleArgumentCategoryMismatch { module, argument } => write!(
                f,
                "Module '{}' argument '{}' uses the wrong syntactic category",
                module, argument
            ),
            Self::ProgramTypeArgumentCountMismatch { actual, expected } => write!(
                f,
                "Program associated item expects {expected} type parameter(s), found {}",
                actual
            ),
            Self::UnknownProgramName { access } => {
                write!(f, "Program name was not found: {access}")
            }
            Self::NotProgramValueType { access } => {
                write!(f, "name does not denote a Program value type: '{access}'")
            }
            Self::DuplicateStructureField { name } => {
                write!(f, "Structure field {} was supplied more than once", name)
            }
            Self::UnknownStructureField { name } => write!(f, "Unknown structure field {}", name),
            Self::MissingStructureField { name } => write!(f, "Missing structure field {}", name),
            Self::NotProgramValue { access } => {
                write!(f, "name does not denote a Program value: '{access}'")
            }
            Self::UnknownProgramAssociatedItem { name } => {
                write!(f, "Program associated item {} was not found", name)
            }
            Self::UnknownProgramConstructor { name } => {
                write!(f, "Program constructor {} was not found", name)
            }
            Self::UnknownProgramRecordField { field, record } => {
                write!(f, "Field {} not found in Program record {}", field, record)
            }
            Self::ProgramBranchBinderCountMismatch { constructor } => write!(
                f,
                "Program case branch {} has the wrong binder count",
                constructor
            ),
            Self::DefinitionArgumentCountMismatch { expected, actual } => write!(
                f,
                "Definition expects at most {} argument(s), found {}",
                expected, actual
            ),
            Self::TypeArgumentCountMismatch { actual, expected } => write!(
                f,
                "associated item expects {expected} type parameter(s), found {}",
                actual
            ),
            Self::InductiveBranchCountMismatch { expected, actual } => write!(
                f,
                "Expected {} inductive branches, found {}",
                expected, actual
            ),
            Self::UnknownInductiveConstructor { name } => {
                write!(f, "Unknown inductive constructor {}", name)
            }
            Self::DuplicateInductiveBranch { name } => {
                write!(f, "Duplicate inductive branch for constructor {}", name)
            }
            Self::MissingInductiveBranch { name } => {
                write!(f, "Missing inductive branch for constructor {}", name)
            }
            Self::BranchBinderCountMismatch {
                constructor,
                actual,
                field_count,
            } => write!(
                f,
                "Branch {} expects {field_count} field binder(s), found {}",
                constructor, actual
            ),
            Self::ExcessBranchBinders { constructor } => {
                write!(f, "Too many field binders in branch {}", constructor)
            }
            Self::DefinitionNeedsReflection { access } => write!(
                f,
                "Program definitions require explicit Set reflection (^): '{access}'"
            ),
            Self::NameNeedsReflection { access } => write!(
                f,
                "Program names require explicit Set reflection (^): '{access}'"
            ),
            Self::AssociatedReflectionNeedsDatatype { field } => write!(
                f,
                "reflection of associated item '{field}' requires a Program datatype"
            ),
            Self::UnknownInductiveAssociatedItem { name, datatype } => write!(
                f,
                "Associated item {} not found in inductive type {}",
                name, datatype
            ),
            Self::UnknownStructureAssociatedItem { name, structure } => write!(
                f,
                "Associated item {} not found in structure {}",
                name, structure
            ),
            Self::InvalidAssociatedBase { base } => write!(
                f,
                "Expected inductive constructor or record type in base of associated access {:?}",
                base
            ),
            Self::EscapedMacroCapture { name } => {
                write!(f, "Macro capture '${}' escaped template expansion", name)
            }
            Self::InvalidCasePath { path } => {
                write!(f, "Expected inductive type in case access path {:?}", path)
            }
            Self::IncompatibleMetaUses { number } => {
                write!(f, "metavariable _{number} has incompatible uses")
            }
        }
    }
}
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Kernel(error) => Some(error),
            Self::Elaboration(error) => Some(error.as_ref()),
            Self::Conversion(error) => Some(error),
            Self::Resolution(error) => Some(error.as_ref()),
            Self::Reflection(error) => Some(error.as_ref()),
            Self::Context { source, .. } => Some(source.as_ref()),
            _ => None,
        }
    }
}
impl From<kernel::error::Error> for Error {
    fn from(error: kernel::error::Error) -> Self {
        Self::Kernel(error)
    }
}
impl From<syntax::error::ConversionError> for Error {
    fn from(error: syntax::error::ConversionError) -> Self {
        Self::Conversion(error)
    }
}
impl From<resolve::Diagnostic> for Error {
    fn from(error: resolve::Diagnostic) -> Self {
        Self::Resolution(Box::new(error))
    }
}
impl From<crate::raw::reflection::ReflectionError> for Error {
    fn from(error: crate::raw::reflection::ReflectionError) -> Self {
        Self::Reflection(Box::new(error))
    }
}
impl From<Box<Error>> for Error {
    fn from(error: Box<Error>) -> Self {
        *error
    }
}

impl From<crate::metavariables::ElaborationError> for Error {
    fn from(error: crate::metavariables::ElaborationError) -> Self {
        Self::Elaboration(Box::new(error))
    }
}
