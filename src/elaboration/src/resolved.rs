use crate::raw::exp::{Exp, ExpNode};
use crate::raw::ids::{DefId, InductiveId};
use ::syntax::syntax::Identifier;

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
    pub inductive: crate::raw::ids::ProgramInductiveId,
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
        env: &crate::raw::environment::CrateEnv,
        e: Exp,
        field_name: &Identifier,
        parameters: &[Exp],
    ) -> Option<Exp> {
        let arena = env.arena();
        let (_, definition) = self
            .associated_definitions
            .iter()
            .find(|(name, _)| name == field_name)?;
        let projection = arena.alloc(ExpNode::DefinedConstant(*definition));
        Some(crate::raw::utils::assoc_apply(
            arena,
            projection,
            parameters.iter().copied().chain([e]).collect(),
        ))
    }
}
