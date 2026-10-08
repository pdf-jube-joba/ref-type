//! CBPV value datatypes and their generated Set reflections.
use crate::{
    kernel_bridge::instantiate_type_telescope,
    raw::{
        derivation::JudgementError,
        environment::ModuleArgument,
        exp::Arena,
        ids::{DefId, InductiveId, ModuleParamId, ProgramInductiveId, SymbolId},
        program::{ValueType, ValueTypeNode},
        program_derivation::ProgramCheckSession,
        remapping::{remap_value_type_global_ids, subst_value_type_module_params},
    },
};
use std::collections::HashMap;

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct ProgramConstructorSpec {
    fields: Vec<(SymbolId, ValueType)>,
}

impl ProgramConstructorSpec {
    pub fn new(fields: Vec<(SymbolId, ValueType)>) -> Self {
        Self { fields }
    }

    pub fn fields(&self) -> &[(SymbolId, ValueType)] {
        &self.fields
    }

    pub fn instantiated_fields(
        &self,
        arena: &Arena,
        parameters: &[ValueType],
    ) -> Vec<(SymbolId, ValueType)> {
        self.fields
            .iter()
            .map(|(name, ty)| (*name, instantiate_type_telescope(arena, *ty, parameters)))
            .collect()
    }
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct ProgramInductiveTypeSpecs {
    parameters: Vec<SymbolId>,
    constructors: Vec<ProgramConstructorSpec>,
    reflected: InductiveId,
}

impl ProgramInductiveTypeSpecs {
    pub fn unchecked(
        parameters: Vec<SymbolId>,
        constructors: Vec<ProgramConstructorSpec>,
        reflected: InductiveId,
    ) -> Self {
        Self {
            parameters,
            constructors,
            reflected,
        }
    }

    pub fn parameters(&self) -> &[SymbolId] {
        &self.parameters
    }

    pub fn constructors(&self) -> &[ProgramConstructorSpec] {
        &self.constructors
    }

    pub fn reflected(&self) -> InductiveId {
        self.reflected
    }

    pub fn validate(
        &self,
        session: &mut ProgramCheckSession<'_, '_>,
        inductive: ProgramInductiveId,
    ) -> Result<(), Box<JudgementError>> {
        let term = session.arena().alloc(ValueTypeNode::Inductive {
            indspec: inductive,
            parameters: vec![],
        });
        crate::kernel_bridge::program(
            session.env(),
            session.context(),
            &[super::traversal::Term::ValueType(term)],
            |_, _, _| Ok(()),
        )
        .map_err(|e| Box::new(JudgementError::caused(e)))
    }

    pub fn instantiate(
        &self,
        arena: &Arena,
        substitutions: &[(ModuleParamId, ModuleArgument)],
    ) -> Self {
        let substitutions = substitutions
            .iter()
            .map(|(p, a)| {
                let a = match *a {
                    ModuleArgument::ProgramType(t) => {
                        ModuleArgument::ProgramType(crate::kernel_bridge::shift_value_type_indices(
                            arena,
                            t,
                            self.parameters.len(),
                            0,
                        ))
                    }
                    other => other,
                };
                (*p, a)
            })
            .collect::<Vec<_>>();
        Self {
            parameters: self.parameters.clone(),
            constructors: self
                .constructors
                .iter()
                .map(|constructor| {
                    ProgramConstructorSpec::new(
                        constructor
                            .fields
                            .iter()
                            .map(|(name, ty)| {
                                (
                                    *name,
                                    subst_value_type_module_params(arena, *ty, &substitutions),
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
            reflected: self.reflected,
        }
    }

    pub fn remap_global_ids(
        &self,
        arena: &Arena,
        definitions: &HashMap<DefId, DefId>,
        inductives: &HashMap<InductiveId, InductiveId>,
        program_inductives: &HashMap<ProgramInductiveId, ProgramInductiveId>,
    ) -> Self {
        Self {
            parameters: self.parameters.clone(),
            constructors: self
                .constructors
                .iter()
                .map(|constructor| {
                    ProgramConstructorSpec::new(
                        constructor
                            .fields
                            .iter()
                            .map(|(name, ty)| {
                                (
                                    *name,
                                    remap_value_type_global_ids(
                                        arena,
                                        *ty,
                                        definitions,
                                        program_inductives,
                                    ),
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
            reflected: inductives
                .get(&self.reflected)
                .copied()
                .unwrap_or(self.reflected),
        }
    }
}
