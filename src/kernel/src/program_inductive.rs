//! CBPV value datatypes and their generated Set reflections.

use serde::Serialize;

use crate::{
    derivation::JudgementError,
    environment::ModuleArgument,
    exp::Arena,
    ids::{DefId, InductiveId, ModuleParamId, ProgramInductiveId, SymbolId},
    program::{ComputationType, ComputationTypeNode, ValueType, ValueTypeNode},
    program_calculus::{
        instantiate_type_telescope, remap_value_type_global_ids, subst_value_type_module_params,
    },
    program_derivation::ProgramCheckSession,
};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize)]
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

#[derive(Debug, Clone, Serialize)]
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
        let mark = session.context().len();
        for parameter in &self.parameters {
            session.push_type(*parameter);
        }
        let result = (|| {
            for (constructor_index, constructor) in self.constructors.iter().enumerate() {
                let constructor_mark = session.context().len();
                for (field_index, (name, ty)) in constructor.fields.iter().enumerate() {
                    session.check_value_type(*ty).map_err(|error| {
                        Box::new(error.with_frame(
                            "ProgramInductiveTypeSpecs::validate",
                            format!("constructor {constructor_index}, field {field_index}"),
                            "field is a value type",
                        ))
                    })?;
                    if !strictly_positive_value(session.arena(), *ty, inductive, true) {
                        return Err(Box::new(
                            JudgementError::caused(format!(
                                "program datatype occurs in a non-strictly-positive position: constructor {constructor_index}, field {field_index}"
                            ))
                            .with_frame(
                                "ProgramInductiveTypeSpecs::validate",
                                "strict positivity",
                                "recursive occurrences are strictly positive",
                            ),
                        ));
                    }
                    session.push_value(*name, *ty);
                }
                while session.context().len() > constructor_mark {
                    session.pop();
                }
            }
            Ok(())
        })();
        while session.context().len() > mark {
            session.pop();
        }
        result
    }

    pub fn instantiate(
        &self,
        arena: &Arena,
        substitutions: &[(ModuleParamId, ModuleArgument)],
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
                                    subst_value_type_module_params(arena, *ty, substitutions),
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

fn strictly_positive_value(
    arena: &Arena,
    ty: ValueType,
    inductive: ProgramInductiveId,
    positive: bool,
) -> bool {
    match arena.get(ty) {
        ValueTypeNode::Bound(_) | ValueTypeNode::ModuleParam(_) | ValueTypeNode::Meta { .. } => {
            true
        }
        ValueTypeNode::Thunk { computation_ty } => {
            strictly_positive_computation(arena, computation_ty, inductive, positive)
        }
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => {
            strictly_positive_value(arena, state_ty, inductive, positive)
                && strictly_positive_value(arena, result_ty, inductive, positive)
        }
        ValueTypeNode::Inductive {
            indspec,
            parameters,
        } => {
            if indspec == inductive && !positive {
                return false;
            }
            // Parameters of an unrelated nominal datatype have unknown
            // variance, so recursive occurrences there are conservatively
            // rejected.
            parameters.into_iter().all(|parameter| {
                if contains_program_inductive(arena, parameter, inductive) {
                    indspec == inductive
                        && strictly_positive_value(arena, parameter, inductive, positive)
                } else {
                    true
                }
            })
        }
    }
}

fn strictly_positive_computation(
    arena: &Arena,
    ty: ComputationType,
    inductive: ProgramInductiveId,
    positive: bool,
) -> bool {
    match arena.get(ty) {
        ComputationTypeNode::Meta { .. } => true,
        ComputationTypeNode::Return { value_ty } => {
            strictly_positive_value(arena, value_ty, inductive, positive)
        }
        ComputationTypeNode::Function { domain, codomain } => {
            strictly_positive_value(arena, domain, inductive, !positive)
                && strictly_positive_computation(arena, codomain, inductive, positive)
        }
    }
}

pub fn contains_program_inductive(
    arena: &Arena,
    ty: ValueType,
    inductive: ProgramInductiveId,
) -> bool {
    match arena.get(ty) {
        ValueTypeNode::Inductive {
            indspec,
            parameters,
        } => {
            indspec == inductive
                || parameters
                    .into_iter()
                    .any(|parameter| contains_program_inductive(arena, parameter, inductive))
        }
        ValueTypeNode::Thunk { computation_ty } => {
            contains_program_inductive_computation(arena, computation_ty, inductive)
        }
        ValueTypeNode::RunStep {
            state_ty,
            result_ty,
        } => {
            contains_program_inductive(arena, state_ty, inductive)
                || contains_program_inductive(arena, result_ty, inductive)
        }
        ValueTypeNode::Bound(_) | ValueTypeNode::ModuleParam(_) | ValueTypeNode::Meta { .. } => {
            false
        }
    }
}

fn contains_program_inductive_computation(
    arena: &Arena,
    ty: ComputationType,
    inductive: ProgramInductiveId,
) -> bool {
    match arena.get(ty) {
        ComputationTypeNode::Meta { .. } => false,
        ComputationTypeNode::Return { value_ty } => {
            contains_program_inductive(arena, value_ty, inductive)
        }
        ComputationTypeNode::Function { domain, codomain } => {
            contains_program_inductive(arena, domain, inductive)
                || contains_program_inductive_computation(arena, codomain, inductive)
        }
    }
}
