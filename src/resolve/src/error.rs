//! Resolution and macro expansion failures.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Error {
    Conversion(syntax::error::ConversionError),
    Invalid(Invalid),
    DuplicateStructureField {
        name: String,
    },
    MissingStructureField {
        name: String,
    },
    UnknownImport {
        name: String,
    },
    UnknownName {
        name: String,
    },
    UnknownImportedMacro {
        module: String,
        name: String,
    },
    DuplicateMacroDeclarations {
        name: String,
        first: syntax::syntax::SourceSpan,
        second: syntax::syntax::SourceSpan,
    },
    MacroDependencyCycle {
        path: Vec<String>,
    },
    DuplicateMacro {
        name: String,
    },
    MathMacroWithoutFixedToken {
        name: String,
    },
    MacroUnavailableInTemplate {
        name: String,
    },
    MacroExpansionLimit {
        limit: usize,
        name: String,
        module: String,
        definition: syntax::syntax::SourceSpan,
    },
    MacroDepthExceeded {
        limit: usize,
    },
    MacroPatternMismatch {
        name: String,
    },
    UnknownNamedMacro {
        name: String,
    },
    UnknownChildModule {
        name: String,
    },
    DuplicateCapture {
        name: String,
    },
    ReservedMacroToken {
        token: String,
    },
    CaptureKindMismatch {
        name: String,
        actual: CaptureKind,
        expected: CaptureKind,
    },
    UndeclaredCapture {
        name: String,
    },
    UndeclaredTokenMatchCapture {
        name: String,
    },
    UnmatchedSequenceCapture {
        name: String,
    },
    UnmatchedTokenCapture {
        name: String,
    },
    UnmatchedExpressionCapture {
        name: String,
    },
    UnmatchedTokenMatchCapture {
        name: String,
    },
    TokenMatchWithoutBranch {
        name: String,
    },
    DuplicateDeclaration {
        name: String,
    },
    MissingExport {
        name: String,
    },
    StructureArgumentCountMismatch {
        expected_count: usize,
        actual_count: usize,
    },
    UnknownStructureField {
        name: String,
    },
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Invalid {
    NoVisibleMathMacro,
    ExternalModuleWasNotLoaded,
    RestCaptureMustBeTheLastElementOfItsPatternSequence,
    TokenAndRestCapturesAreOnlyValidInNamedMacros,
    TokenMatchRequiresATokenOrSequenceCapture,
    TokenMatchingIsOnlyValidInNamedMacros,
    AlreadyAtRootModule,
    ArgumentDoesNotSatisfyDeclarationSignature,
    BundleProgramTypesRequireAnExplicitType,
    BundleTypeMembersDoNotTakeParameters,
    CyclicModuleImportDependency,
    DeclarationParameterCountMismatch,
    DefaultFieldsInASortedStructureRequireProp,
    DefinitionDoesNotSatisfyStructureResultSignature,
    ExistentialEliminationRequiresOneWitness,
    ExpectedProgramTypeInBundle,
    ExpectedAStructureResultSignature,
    ExpectedAStructureTypeBeforeALiteral,
    ExpectedNestedStructure,
    MacroTemplateSyntaxOutsideAMacroExpansion,
    ModuleArgumentsDoNotAllowInferenceHolesOr,
    NestedFieldDoesNotSatisfyStructureSignature,
    StructureDeclarationArgumentCountMismatch,
    StructureDeclarationNeedsItsRemainingArguments,
    StructureSignatureParameterMismatch,
    UnknownStructureField,
    UnresolvedModuleExpression,
}
impl std::fmt::Display for Invalid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoVisibleMathMacro => {
                f.write_str("No visible math macro matches the complete token sequence")
            }
            Self::ExternalModuleWasNotLoaded => f.write_str("External module was not loaded"),
            Self::RestCaptureMustBeTheLastElementOfItsPatternSequence => {
                f.write_str("Rest capture must be the last element of its pattern sequence")
            }
            Self::TokenAndRestCapturesAreOnlyValidInNamedMacros => {
                f.write_str("Token and rest captures are only valid in named macros")
            }
            Self::TokenMatchRequiresATokenOrSequenceCapture => {
                f.write_str("Token match requires a token or sequence capture")
            }
            Self::TokenMatchingIsOnlyValidInNamedMacros => {
                f.write_str("Token matching is only valid in named macros")
            }
            Self::AlreadyAtRootModule => f.write_str("already at root module"),
            Self::ArgumentDoesNotSatisfyDeclarationSignature => {
                f.write_str("argument does not satisfy declaration signature")
            }
            Self::BundleProgramTypesRequireAnExplicitType => {
                f.write_str("bundle Program types require an explicit type")
            }
            Self::BundleTypeMembersDoNotTakeParameters => {
                f.write_str("bundle type members do not take parameters")
            }
            Self::CyclicModuleImportDependency => f.write_str("cyclic module import dependency"),
            Self::DeclarationParameterCountMismatch => {
                f.write_str("declaration parameter count mismatch")
            }
            Self::DefaultFieldsInASortedStructureRequireProp => {
                f.write_str("default fields in a sorted structure require Prop")
            }
            Self::DefinitionDoesNotSatisfyStructureResultSignature => {
                f.write_str("definition does not satisfy structure result signature")
            }
            Self::ExistentialEliminationRequiresOneWitness => {
                f.write_str("existential elimination requires one witness")
            }
            Self::ExpectedProgramTypeInBundle => f.write_str("expected Program type in bundle"),
            Self::ExpectedAStructureResultSignature => {
                f.write_str("expected a structure result signature")
            }
            Self::ExpectedAStructureTypeBeforeALiteral => {
                f.write_str("expected a structure type before a literal")
            }
            Self::ExpectedNestedStructure => f.write_str("expected nested structure"),
            Self::MacroTemplateSyntaxOutsideAMacroExpansion => {
                f.write_str("macro template syntax outside a macro expansion")
            }
            Self::ModuleArgumentsDoNotAllowInferenceHolesOr => {
                f.write_str("module arguments do not allow inference holes (`_` or `?`)")
            }
            Self::NestedFieldDoesNotSatisfyStructureSignature => {
                f.write_str("nested field does not satisfy structure signature")
            }
            Self::StructureDeclarationArgumentCountMismatch => {
                f.write_str("structure declaration argument count mismatch")
            }
            Self::StructureDeclarationNeedsItsRemainingArguments => {
                f.write_str("structure declaration needs its remaining arguments")
            }
            Self::StructureSignatureParameterMismatch => {
                f.write_str("structure signature parameter mismatch")
            }
            Self::UnknownStructureField => f.write_str("unknown structure field"),
            Self::UnresolvedModuleExpression => f.write_str("unresolved module expression"),
        }
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Conversion(error) => error.fmt(f),
            Self::Invalid(error) => error.fmt(f),
            Self::DuplicateStructureField { name } => {
                write!(f, "duplicate structure field: {}", name)
            }
            Self::MissingStructureField { name } => write!(f, "missing structure field: {}", name),
            Self::UnknownImport { name } => write!(f, "Module import '{}' was not found", name),
            Self::UnknownName { name } => write!(f, "Name '{}' was not found in its scope", name),
            Self::UnknownImportedMacro { module, name } => {
                write!(f, "Macro '{}.{}' was not found", module, name)
            }
            Self::DuplicateMacroDeclarations {
                name,
                first,
                second,
            } => write!(
                f,
                "Duplicate macro '{name}' at {}..{} and {}..{}",
                first.start, first.end, second.start, second.end
            ),
            Self::MacroDependencyCycle { path } => write!(
                f,
                "Cyclic macro/module instantiation dependency: {}",
                path.join(" -> ")
            ),
            Self::DuplicateMacro { name } => write!(f, "Macro '{}' is already visible", name),
            Self::MathMacroWithoutFixedToken { name } => write!(
                f,
                "Math macro '{}' must contain at least one fixed token",
                name
            ),
            Self::MacroUnavailableInTemplate { name } => write!(
                f,
                "Named macro '{}' is not visible at template declaration",
                name
            ),
            Self::MacroExpansionLimit {
                limit,
                name,
                module,
                definition,
            } => write!(
                f,
                "Macro expansion exceeded depth {limit}: {module}::{name} defined at {}..{}",
                definition.start, definition.end
            ),
            Self::MacroDepthExceeded { limit } => {
                write!(f, "Macro expansion exceeded depth {}", limit)
            }
            Self::MacroPatternMismatch { name } => write!(
                f,
                "Input does not match the complete pattern of macro '{}'",
                name
            ),
            Self::UnknownNamedMacro { name } => write!(f, "Named macro '{}' is not visible", name),
            Self::UnknownChildModule { name } => write!(f, "child module '{}' was not found", name),
            Self::DuplicateCapture { name } => {
                write!(f, "Macro capture '${}' is declared more than once", name)
            }
            Self::ReservedMacroToken { token } => {
                write!(f, "Macro token '{}' conflicts with reserved syntax", token)
            }
            Self::CaptureKindMismatch {
                name,
                actual,
                expected,
            } => write!(
                f,
                "Macro capture '{}' has kind {actual:?}, expected {expected:?}",
                name
            ),
            Self::UndeclaredCapture { name } => write!(
                f,
                "Macro template references undeclared capture '${}'",
                name
            ),
            Self::UndeclaredTokenMatchCapture { name } => {
                write!(f, "Token match references undeclared capture '{}'", name)
            }
            Self::UnmatchedSequenceCapture { name } => {
                write!(f, "Rest capture '{}' has no matched sequence", name)
            }
            Self::UnmatchedTokenCapture { name } => {
                write!(f, "Token capture '{}' has no matched token", name)
            }
            Self::UnmatchedExpressionCapture { name } => {
                write!(f, "Capture '${}' has no matched expression", name)
            }
            Self::UnmatchedTokenMatchCapture { name } => {
                write!(f, "Token match capture '{}' has no matched value", name)
            }
            Self::TokenMatchWithoutBranch { name } => {
                write!(f, "No token match branch matches capture '{}'", name)
            }
            Self::DuplicateDeclaration { name } => write!(f, "duplicate declaration: {}", name),
            Self::MissingExport { name } => write!(f, "missing exported member: {}", name),
            Self::StructureArgumentCountMismatch {
                expected_count,
                actual_count,
            } => write!(
                f,
                "structure argument count mismatch: expected {}, got {}",
                expected_count, actual_count
            ),
            Self::UnknownStructureField { name } => write!(f, "unknown structure field: {}", name),
        }
    }
}
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Conversion(error) => Some(error),
            _ => None,
        }
    }
}
impl From<syntax::error::ConversionError> for Error {
    fn from(error: syntax::error::ConversionError) -> Self {
        Self::Conversion(error)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CaptureKind {
    Expression,
    Token,
    Sequence,
}

impl diagnostics::DiagnosticError for Error {
    fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        use diagnostics::DiagnosticData as Data;
        match self {
            Self::Invalid(error) => Data::new(format!("resolve.{error:?}")),
            Self::Conversion(error) => error.diagnostic_data(),
            Self::DuplicateStructureField { name } => {
                Data::new("resolve.DuplicateStructureField").with("name", name.clone())
            }
            Self::MissingStructureField { name } => {
                Data::new("resolve.MissingStructureField").with("name", name.clone())
            }
            Self::UnknownImport { name } => {
                Data::new("resolve.UnknownImport").with("name", name.clone())
            }
            Self::UnknownName { name } => {
                Data::new("resolve.UnknownName").with("name", name.clone())
            }
            Self::UnknownImportedMacro { module, name } => {
                Data::new("resolve.UnknownImportedMacro")
                    .with("module", module.clone())
                    .with("name", name.clone())
            }
            Self::DuplicateMacroDeclarations {
                name,
                first,
                second,
            } => Data::new("resolve.DuplicateMacroDeclarations")
                .with("name", name.clone())
                .with("first_start", first.start)
                .with("second_start", second.start),
            Self::MacroDependencyCycle { path } => {
                Data::new("resolve.MacroDependencyCycle").with("path", path.join(" -> "))
            }
            Self::DuplicateMacro { name } => {
                Data::new("resolve.DuplicateMacro").with("name", name.clone())
            }
            Self::MathMacroWithoutFixedToken { name } => {
                Data::new("resolve.MathMacroWithoutFixedToken").with("name", name.clone())
            }
            Self::MacroUnavailableInTemplate { name } => {
                Data::new("resolve.MacroUnavailableInTemplate").with("name", name.clone())
            }
            Self::MacroExpansionLimit {
                limit,
                name,
                module,
                definition,
            } => Data::new("resolve.MacroExpansionLimit")
                .with("limit", *limit)
                .with("name", name.clone())
                .with("module", module.clone())
                .with("definition_start", definition.start),
            Self::MacroDepthExceeded { limit } => {
                Data::new("resolve.MacroDepthExceeded").with("limit", *limit)
            }
            Self::MacroPatternMismatch { name } => {
                Data::new("resolve.MacroPatternMismatch").with("name", name.clone())
            }
            Self::UnknownNamedMacro { name } => {
                Data::new("resolve.UnknownNamedMacro").with("name", name.clone())
            }
            Self::UnknownChildModule { name } => {
                Data::new("resolve.UnknownChildModule").with("name", name.clone())
            }
            Self::DuplicateCapture { name } => {
                Data::new("resolve.DuplicateCapture").with("name", name.clone())
            }
            Self::ReservedMacroToken { token } => {
                Data::new("resolve.ReservedMacroToken").with("token", token.clone())
            }
            Self::CaptureKindMismatch {
                name,
                actual,
                expected,
            } => Data::new("resolve.CaptureKindMismatch")
                .with("name", name.clone())
                .with("actual", format!("{actual:?}"))
                .with("expected", format!("{expected:?}")),
            Self::UndeclaredCapture { name } => {
                Data::new("resolve.UndeclaredCapture").with("name", name.clone())
            }
            Self::UndeclaredTokenMatchCapture { name } => {
                Data::new("resolve.UndeclaredTokenMatchCapture").with("name", name.clone())
            }
            Self::UnmatchedSequenceCapture { name } => {
                Data::new("resolve.UnmatchedSequenceCapture").with("name", name.clone())
            }
            Self::UnmatchedTokenCapture { name } => {
                Data::new("resolve.UnmatchedTokenCapture").with("name", name.clone())
            }
            Self::UnmatchedExpressionCapture { name } => {
                Data::new("resolve.UnmatchedExpressionCapture").with("name", name.clone())
            }
            Self::UnmatchedTokenMatchCapture { name } => {
                Data::new("resolve.UnmatchedTokenMatchCapture").with("name", name.clone())
            }
            Self::TokenMatchWithoutBranch { name } => {
                Data::new("resolve.TokenMatchWithoutBranch").with("name", name.clone())
            }
            Self::DuplicateDeclaration { name } => {
                Data::new("resolve.DuplicateDeclaration").with("name", name.clone())
            }
            Self::MissingExport { name } => {
                Data::new("resolve.MissingExport").with("name", name.clone())
            }
            Self::StructureArgumentCountMismatch {
                expected_count,
                actual_count,
            } => Data::new("resolve.StructureArgumentCountMismatch")
                .with("expected_count", *expected_count)
                .with("actual_count", *actual_count),
            Self::UnknownStructureField { name } => {
                Data::new("resolve.UnknownStructureField").with("name", name.clone())
            }
        }
    }
}
