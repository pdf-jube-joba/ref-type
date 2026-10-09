#[derive(Debug, Clone)]
pub enum Context {
    FailedToInferElaboratedSetPropExpression,
    FailedToInferTypeOfExpressionForFieldProjection,
    IllFormedProgramDatatype,
    IllFormedInductiveTypeSpecification,
    IllFormedReflectedDatatype,
    IllFormedStructure,
    ModuleInstantiationFailed,
    ProgramComputationDefinitionCheckFailed,
    ProgramTypeModuleArgumentIsIllFormed,
    ProgramValueDefinitionCheckFailed,
    ProgramValueModuleArgumentIsIllTyped,
    CannotInferProgramCaseScrutinee,
    CannotInferProgramValue,
    CannotReflectProgramConstructorField,
    CannotReflectProgramContext,
    CannotReflectProgramTypeModuleArgument,
    CannotReflectProgramValueModuleArgument,
    CheckFailed,
    DefinitionBodyCheckFailed,
    DefinitionCheckFailed,
    DefinitionParameterCheckFailed,
    InferFailed,
    SpecializingDefinition {
        name: String,
    },
    ProgramValueDefinition {
        name: String,
    },
    ProgramComputationDefinition {
        name: String,
    },
    GeneratedProjection {
        name: String,
    },
    ModuleArgument {
        module: String,
        argument: String,
    },
    LocalDefinition {
        name: String,
    },
    Definition {
        name: String,
    },
    Inductive {
        name: String,
    },
    Parameter {
        subject: resolve::hir::ParameterSubject,
        requirement: ParameterRequirement,
    },
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParameterRequirement {
    TypeOrProposition,
    ProgramValueType,
}
impl std::fmt::Display for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FailedToInferElaboratedSetPropExpression => {
                f.write_str("Failed to infer elaborated Set/Prop expression")
            }
            Self::FailedToInferTypeOfExpressionForFieldProjection => {
                f.write_str("Failed to infer type of expression for field projection")
            }
            Self::IllFormedProgramDatatype => f.write_str("Ill-formed Program datatype"),
            Self::IllFormedInductiveTypeSpecification => {
                f.write_str("Ill-formed inductive type specification")
            }
            Self::IllFormedReflectedDatatype => f.write_str("Ill-formed reflected datatype"),
            Self::IllFormedStructure => f.write_str("Ill-formed structure"),
            Self::ModuleInstantiationFailed => f.write_str("Module instantiation failed"),
            Self::ProgramComputationDefinitionCheckFailed => {
                f.write_str("Program computation definition check failed")
            }
            Self::ProgramTypeModuleArgumentIsIllFormed => {
                f.write_str("Program type module argument is ill-formed")
            }
            Self::ProgramValueDefinitionCheckFailed => {
                f.write_str("Program value definition check failed")
            }
            Self::ProgramValueModuleArgumentIsIllTyped => {
                f.write_str("Program value module argument is ill-typed")
            }
            Self::CannotInferProgramCaseScrutinee => {
                f.write_str("cannot infer Program case scrutinee")
            }
            Self::CannotInferProgramValue => f.write_str("cannot infer Program value"),
            Self::CannotReflectProgramConstructorField => {
                f.write_str("cannot reflect Program constructor field")
            }
            Self::CannotReflectProgramContext => f.write_str("cannot reflect Program context"),
            Self::CannotReflectProgramTypeModuleArgument => {
                f.write_str("cannot reflect Program type module argument")
            }
            Self::CannotReflectProgramValueModuleArgument => {
                f.write_str("cannot reflect Program value module argument")
            }
            Self::CheckFailed => f.write_str("check failed"),
            Self::DefinitionBodyCheckFailed => f.write_str("definition body check failed"),
            Self::DefinitionCheckFailed => f.write_str("definition check failed"),
            Self::DefinitionParameterCheckFailed => {
                f.write_str("definition parameter check failed")
            }
            Self::InferFailed => f.write_str("infer failed"),
            Self::SpecializingDefinition { name } => write!(f, "specializing {}", name),
            Self::ProgramValueDefinition { name } => {
                write!(f, "Program value definition {} is ill-typed", name)
            }
            Self::ProgramComputationDefinition { name } => {
                write!(f, "Program computation definition {} is ill-typed", name)
            }
            Self::GeneratedProjection { name } => {
                write!(f, "Generated projection {} does not typecheck", name)
            }
            Self::ModuleArgument { module, argument } => write!(
                f,
                "Module '{}' argument '{}' failed type checking",
                module, argument
            ),
            Self::LocalDefinition { name } => write!(f, "Local definition '{}'", name),
            Self::Definition { name } => write!(f, "definition {name}"),
            Self::Inductive { name } => write!(f, "inductive {name}"),
            Self::Parameter {
                subject,
                requirement,
            } => {
                write!(f, "{subject} ")?;
                f.write_str(match requirement {
                    ParameterRequirement::TypeOrProposition => "must have a type or proposition",
                    ParameterRequirement::ProgramValueType => {
                        "has an ill-formed Program value type"
                    }
                })
            }
        }
    }
}

impl Context {
    pub(super) fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        use diagnostics::DiagnosticData as Data;
        match self {
            Self::Parameter {
                subject,
                requirement,
            } => Data::new("elaboration.Parameter")
                .with("subject", subject.diagnostic_data())
                .with("requirement", format!("{requirement:?}")),
            Self::SpecializingDefinition { name } => {
                Data::new("elaboration.SpecializingDefinition").with("name", name.clone())
            }
            Self::ProgramValueDefinition { name } => {
                Data::new("elaboration.ProgramValueDefinition").with("name", name.clone())
            }
            Self::ProgramComputationDefinition { name } => {
                Data::new("elaboration.ProgramComputationDefinition").with("name", name.clone())
            }
            Self::GeneratedProjection { name } => {
                Data::new("elaboration.GeneratedProjection").with("name", name.clone())
            }
            Self::ModuleArgument { module, argument } => Data::new("elaboration.ModuleArgument")
                .with("module", module.clone())
                .with("argument", argument.clone()),
            Self::LocalDefinition { name } => {
                Data::new("elaboration.LocalDefinition").with("name", name.clone())
            }
            Self::Definition { name } => {
                Data::new("elaboration.Definition").with("name", name.clone())
            }
            Self::Inductive { name } => {
                Data::new("elaboration.Inductive").with("name", name.clone())
            }
            other => Data::new(format!("elaboration.{other:?}")),
        }
    }
}
