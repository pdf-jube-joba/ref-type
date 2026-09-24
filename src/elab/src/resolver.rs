use crate::ids::{DefId, InductiveId};
use crate::{exp::Exp, ids::ModuleParamId};
use hir::Identifier;

#[derive(Debug, Clone)]
pub enum ItemAccessResult {
    Definition(ModItemDefinition),
    ReflectedDefinition(ModItemDefinition),
    Inductive(ModItemInductive),
    Record(ModItemRecord),
    ProgramInductive(ModItemProgramInductive),
    Expression(Exp),
    ProgramTypeParameter(ModuleParamId),
    ProgramValueParameter(ModuleParamId),
}

#[derive(Debug, Clone)]
pub struct ModItemDefinition {
    pub def_name: Identifier,
    pub definition: DefId,
}

#[derive(Debug, Clone)]
pub struct ModItemInductive {
    pub type_name: Identifier,
    pub ctor_names: Vec<Identifier>,
    pub inductive: InductiveId,
    pub associated_definitions: Vec<(Identifier, DefId)>,
}

#[derive(Debug, Clone)]
pub struct ModItemProgramInductive {
    pub record_fields: Option<Vec<Identifier>>,
    pub type_name: Identifier,
    pub ctor_names: Vec<Identifier>,
    pub inductive: crate::ids::ProgramInductiveId,
    pub reflected: InductiveId,
    pub associated_definitions: Vec<(Identifier, DefId)>,
}

#[derive(Debug, Clone)]
pub struct ModItemRecord {
    pub type_name: Identifier,
    pub inductive: InductiveId,
    pub associated_definitions: Vec<(Identifier, DefId)>,
}

impl ModItemRecord {
    // Apply the projection definition generated for a record field.
    pub fn field_projection(
        &self,
        env: &crate::environment::CrateEnv,
        e: Exp,
        field_name: &hir::Identifier,
        parameters: &[Exp],
    ) -> Option<Exp> {
        let arena = env.arena();
        let (_, definition) = self
            .associated_definitions
            .iter()
            .find(|(name, _)| name == field_name)?;
        let projection = arena.alloc(crate::exp::ExpNode::DefinedConstant(*definition));
        Some(crate::utils::assoc_apply(
            arena,
            projection,
            parameters.iter().copied().chain([e]).collect(),
        ))
    }
}
