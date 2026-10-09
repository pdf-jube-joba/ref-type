use crate::hir::Identifier;
use crate::raw::exp::{Exp, ExpNode};
use crate::raw::ids::{DefId, InductiveId};

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
    ) -> Result<Option<Exp>, crate::error::Error> {
        let arena = env.arena();
        let Some((_, definition)) = self
            .associated_definitions
            .iter()
            .find(|(name, _)| name == field_name)
        else {
            return Ok(None);
        };
        let (substitutions, parameters) =
            arena.split_inductive_arguments(self.inductive, parameters);
        let projection = if substitutions.is_empty() {
            arena.alloc(ExpNode::DefinedConstant(*definition))
        } else {
            crate::kernel_bridge::captured_definition(env, *definition, &substitutions, &[])?
        };
        Ok(Some(crate::raw::utils::assoc_apply(
            arena,
            projection,
            parameters.iter().copied().chain([e]).collect(),
        )))
    }
}
