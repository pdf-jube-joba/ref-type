//! Failures to interpret surface expressions as Program syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ConversionError {
    ProgramBlocksOnlySupportLetAndBindStatements,
    ProgramLambdaRequiresAPlainValueBinder,
    ProgramLambdaRequiresAtLeastOneValueBinder,
    ProgramValuesAreNotAppliedOnlyConstructorsTakeFieldArguments,
    BindStatementsAreOnlyAvailableInProgramBlocks,
    ExpectedProgramComputationSyntax,
    ExpectedProgramComputationTypeSyntax,
    ExpectedProgramValueSyntax,
    ExpectedProgramValueTypeSyntax,
    ExpectedAProgramDatatypeBeforeAssociatedAccess,
    ExpectedAProgramDatatypeBeforeConstructorAccess,
}
impl std::fmt::Display for ConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ProgramBlocksOnlySupportLetAndBindStatements => {
                f.write_str("Program blocks only support \\let and \\bind statements")
            }
            Self::ProgramLambdaRequiresAPlainValueBinder => {
                f.write_str("Program lambda requires a plain value binder")
            }
            Self::ProgramLambdaRequiresAtLeastOneValueBinder => {
                f.write_str("Program lambda requires at least one value binder")
            }
            Self::ProgramValuesAreNotAppliedOnlyConstructorsTakeFieldArguments => f.write_str(
                "Program values are not applied; only constructors take field arguments",
            ),
            Self::BindStatementsAreOnlyAvailableInProgramBlocks => {
                f.write_str("\\bind statements are only available in Program blocks")
            }
            Self::ExpectedProgramComputationSyntax => {
                f.write_str("expected Program computation syntax")
            }
            Self::ExpectedProgramComputationTypeSyntax => {
                f.write_str("expected Program computation-type syntax")
            }
            Self::ExpectedProgramValueSyntax => f.write_str("expected Program value syntax"),
            Self::ExpectedProgramValueTypeSyntax => {
                f.write_str("expected Program value-type syntax")
            }
            Self::ExpectedAProgramDatatypeBeforeAssociatedAccess => {
                f.write_str("expected a Program datatype before associated access")
            }
            Self::ExpectedAProgramDatatypeBeforeConstructorAccess => {
                f.write_str("expected a Program datatype before constructor access")
            }
        }
    }
}
impl std::error::Error for ConversionError {}

impl diagnostics::DiagnosticError for ConversionError {
    fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        diagnostics::DiagnosticData::new(format!("syntax.{self:?}"))
    }
}
