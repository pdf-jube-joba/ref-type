use super::*;

impl diagnostics::DiagnosticError for Error {
    fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        use diagnostics::DiagnosticData as Data;
        match self {
            Self::DuplicateMaterialization { id } => {
                Data::new("elaboration.DuplicateMaterialization").with("id", format!("{id:?}"))
            }
            Self::UncapturedParameter {
                id,
                module,
                captures,
            } => Data::new("elaboration.UncapturedParameter")
                .with("id", format!("{id:?}"))
                .with("module", module.clone())
                .with(
                    "captures",
                    diagnostics::Value::List(
                        captures.iter().map(|id| format!("{id:?}").into()).collect(),
                    ),
                ),

            Self::Kernel(error) => error.diagnostic_data(),
            Self::Elaboration(error) => error.diagnostic_data(),
            Self::Conversion(error) => error.diagnostic_data(),
            Self::Resolution(error) => error.diagnostic_data(),
            Self::Reflection(error) => error.diagnostic_data(),
            Self::Invalid(error) => Data::new(format!("elaboration.{error:?}")),
            Self::Context { context, source } => context
                .diagnostic_data()
                .caused_by(source.diagnostic_data()),
            Self::UnknownAccess { access_path } => Data::new("elaboration.UnknownAccess")
                .with("access_path", format!("{access_path:?}")),
            Self::ProjectionFromStructureType { field, name } => {
                Data::new("elaboration.ProjectionFromStructureType")
                    .with("field", field.clone())
                    .with("name", name.clone())
            }
            Self::UnknownRecordField { field } => {
                Data::new("elaboration.UnknownRecordField").with("field", field.clone())
            }
            Self::ReflectedTypeArgumentCountMismatch { actual, expected } => {
                Data::new("elaboration.ReflectedTypeArgumentCountMismatch")
                    .with("actual", *actual)
                    .with("expected", *expected)
            }
            Self::UnresolvedExternalModule { name } => {
                Data::new("elaboration.UnresolvedExternalModule").with("name", name.clone())
            }
            Self::ReservedDefinitionUsed { id } => {
                Data::new("elaboration.ReservedDefinitionUsed").with("id", format!("{id:?}"))
            }
            Self::CyclicDefinition { id } => {
                Data::new("elaboration.CyclicDefinition").with("id", format!("{id:?}"))
            }
            Self::DuplicateModuleItem { name } => {
                Data::new("elaboration.DuplicateModuleItem").with("name", name.clone())
            }
            Self::UnknownAssociatedOwner { owner } => {
                Data::new("elaboration.UnknownAssociatedOwner").with("owner", owner.clone())
            }
            Self::AssociatedOwnerNotAType { owner } => {
                Data::new("elaboration.AssociatedOwnerNotAType").with("owner", owner.clone())
            }
            Self::DuplicateAssociatedItem { owner, name } => {
                Data::new("elaboration.DuplicateAssociatedItem")
                    .with("owner", owner.clone())
                    .with("name", name.clone())
            }
            Self::DuplicateModuleImport { name } => {
                Data::new("elaboration.DuplicateModuleImport").with("name", name.clone())
            }
            Self::UnknownModuleImport { name } => {
                Data::new("elaboration.UnknownModuleImport").with("name", name.clone())
            }
            Self::UnknownChildModule { name } => {
                Data::new("elaboration.UnknownChildModule").with("name", name.clone())
            }
            Self::ModuleArgumentCountMismatch { name } => {
                Data::new("elaboration.ModuleArgumentCountMismatch").with("name", name.clone())
            }
            Self::ModuleArgumentNameMismatch { name } => {
                Data::new("elaboration.ModuleArgumentNameMismatch").with("name", name.clone())
            }
            Self::InvalidAssociatedOwner { name } => {
                Data::new("elaboration.InvalidAssociatedOwner").with("name", name.clone())
            }
            Self::AssociatedDefinitionArgumentCountMismatch {
                owner,
                name,
                expected,
                actual,
            } => Data::new("elaboration.AssociatedDefinitionArgumentCountMismatch")
                .with("owner", owner.clone())
                .with("name", name.clone())
                .with("expected", *expected)
                .with("actual", *actual),
            Self::ProgramOwnerArgumentCountMismatch { actual, expected } => {
                Data::new("elaboration.ProgramOwnerArgumentCountMismatch")
                    .with("actual", *actual)
                    .with("expected", *expected)
            }
            Self::DuplicateRecordField { name } => {
                Data::new("elaboration.DuplicateRecordField").with("name", name.clone())
            }
            Self::DuplicateProgramConstructor { name } => {
                Data::new("elaboration.DuplicateProgramConstructor").with("name", name.clone())
            }
            Self::ProgramConstructorResultMismatch {
                constructor,
                datatype,
            } => Data::new("elaboration.ProgramConstructorResultMismatch")
                .with("constructor", constructor.clone())
                .with("datatype", datatype.clone()),
            Self::ProgramConstructorParameterMismatch {
                constructor,
                datatype,
            } => Data::new("elaboration.ProgramConstructorParameterMismatch")
                .with("constructor", constructor.clone())
                .with("datatype", datatype.clone()),
            Self::UnknownChildInModule { name, module } => {
                Data::new("elaboration.UnknownChildInModule")
                    .with("name", name.clone())
                    .with("module", module.clone())
            }
            Self::ModuleArgumentArityMismatch {
                module,
                expected,
                actual,
            } => Data::new("elaboration.ModuleArgumentArityMismatch")
                .with("module", module.clone())
                .with("expected", *expected)
                .with("actual", *actual),
            Self::ModuleArgumentLabelMismatch {
                module,
                expected,
                actual,
            } => Data::new("elaboration.ModuleArgumentLabelMismatch")
                .with("module", module.clone())
                .with("expected", expected.clone())
                .with("actual", actual.clone()),
            Self::ModuleArgumentCategoryMismatch { module, argument } => {
                Data::new("elaboration.ModuleArgumentCategoryMismatch")
                    .with("module", module.clone())
                    .with("argument", argument.clone())
            }
            Self::ProgramTypeArgumentCountMismatch { actual, expected } => {
                Data::new("elaboration.ProgramTypeArgumentCountMismatch")
                    .with("actual", *actual)
                    .with("expected", *expected)
            }
            Self::UnknownProgramName { access } => {
                Data::new("elaboration.UnknownProgramName").with("access", format!("{access:?}"))
            }
            Self::NotProgramValueType { access } => {
                Data::new("elaboration.NotProgramValueType").with("access", format!("{access:?}"))
            }
            Self::DuplicateStructureField { name } => {
                Data::new("elaboration.DuplicateStructureField").with("name", name.clone())
            }
            Self::UnknownStructureField { name } => {
                Data::new("elaboration.UnknownStructureField").with("name", name.clone())
            }
            Self::MissingStructureField { name } => {
                Data::new("elaboration.MissingStructureField").with("name", name.clone())
            }
            Self::NotProgramValue { access } => {
                Data::new("elaboration.NotProgramValue").with("access", format!("{access:?}"))
            }
            Self::UnknownProgramAssociatedItem { name } => {
                Data::new("elaboration.UnknownProgramAssociatedItem").with("name", name.clone())
            }
            Self::UnknownProgramConstructor { name } => {
                Data::new("elaboration.UnknownProgramConstructor").with("name", name.clone())
            }
            Self::UnknownProgramRecordField { field, record } => {
                Data::new("elaboration.UnknownProgramRecordField")
                    .with("field", field.clone())
                    .with("record", record.clone())
            }
            Self::ProgramBranchBinderCountMismatch { constructor } => {
                Data::new("elaboration.ProgramBranchBinderCountMismatch")
                    .with("constructor", constructor.clone())
            }
            Self::DefinitionArgumentCountMismatch { expected, actual } => {
                Data::new("elaboration.DefinitionArgumentCountMismatch")
                    .with("expected", *expected)
                    .with("actual", *actual)
            }
            Self::TypeArgumentCountMismatch { actual, expected } => {
                Data::new("elaboration.TypeArgumentCountMismatch")
                    .with("actual", *actual)
                    .with("expected", *expected)
            }
            Self::InductiveBranchCountMismatch { expected, actual } => {
                Data::new("elaboration.InductiveBranchCountMismatch")
                    .with("expected", *expected)
                    .with("actual", *actual)
            }
            Self::UnknownInductiveConstructor { name } => {
                Data::new("elaboration.UnknownInductiveConstructor").with("name", name.clone())
            }
            Self::DuplicateInductiveBranch { name } => {
                Data::new("elaboration.DuplicateInductiveBranch").with("name", name.clone())
            }
            Self::MissingInductiveBranch { name } => {
                Data::new("elaboration.MissingInductiveBranch").with("name", name.clone())
            }
            Self::BranchBinderCountMismatch {
                constructor,
                actual,
                field_count,
            } => Data::new("elaboration.BranchBinderCountMismatch")
                .with("constructor", constructor.clone())
                .with("actual", *actual)
                .with("field_count", *field_count),
            Self::ExcessBranchBinders { constructor } => {
                Data::new("elaboration.ExcessBranchBinders")
                    .with("constructor", constructor.clone())
            }
            Self::DefinitionNeedsReflection { access } => {
                Data::new("elaboration.DefinitionNeedsReflection")
                    .with("access", format!("{access:?}"))
            }
            Self::NameNeedsReflection { access } => {
                Data::new("elaboration.NameNeedsReflection").with("access", format!("{access:?}"))
            }
            Self::AssociatedReflectionNeedsDatatype { field } => {
                Data::new("elaboration.AssociatedReflectionNeedsDatatype")
                    .with("field", field.clone())
            }
            Self::UnknownInductiveAssociatedItem { name, datatype } => {
                Data::new("elaboration.UnknownInductiveAssociatedItem")
                    .with("name", name.clone())
                    .with("datatype", datatype.clone())
            }
            Self::UnknownStructureAssociatedItem { name, structure } => {
                Data::new("elaboration.UnknownStructureAssociatedItem")
                    .with("name", name.clone())
                    .with("structure", structure.clone())
            }
            Self::InvalidAssociatedBase { base } => {
                Data::new("elaboration.InvalidAssociatedBase").with("base", format!("{base:?}"))
            }
            Self::EscapedMacroCapture { name } => {
                Data::new("elaboration.EscapedMacroCapture").with("name", name.clone())
            }
            Self::InvalidCasePath { path } => {
                Data::new("elaboration.InvalidCasePath").with("path", format!("{path:?}"))
            }
            Self::IncompatibleMetaUses { number } => {
                Data::new("elaboration.IncompatibleMetaUses").with("number", *number)
            }
        }
    }
}
