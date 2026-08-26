//! CBPV value datatypes and their generated Set reflections.

use serde::Serialize;

use crate::{
    calculus::{exp_subst_map, remap_all_global_ids},
    derivation::{CheckSession, JudgementError},
    exp::{Arena, Exp, Node},
    ids::{DefId, InductiveId, ModuleParamId, ProgramInductiveId, SymbolId},
};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize)]
pub struct ProgramConstructorSpec {
    fields: Vec<(SymbolId, Exp)>,
}

impl ProgramConstructorSpec {
    pub fn new(fields: Vec<(SymbolId, Exp)>) -> Self {
        Self { fields }
    }

    pub fn fields(&self) -> &[(SymbolId, Exp)] {
        &self.fields
    }

    pub fn instantiated_fields(&self, arena: &Arena, parameters: &[Exp]) -> Vec<(SymbolId, Exp)> {
        self.fields
            .iter()
            .enumerate()
            .map(|(inner, (name, ty))| {
                (
                    *name,
                    crate::calculus::instantiate_outer_telescope(arena, *ty, parameters, inner),
                )
            })
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
        session: &mut CheckSession<'_, '_>,
        inductive: ProgramInductiveId,
    ) -> Result<(), Box<JudgementError>> {
        let mark = session.context().len();
        for parameter in &self.parameters {
            session.push_program_type(*parameter);
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
                    if !strictly_positive(session.arena(), *ty, inductive, true) {
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
                    session.push_program_value(*name, *ty);
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

    pub fn instantiate(&self, arena: &Arena, substitutions: &[(ModuleParamId, Exp)]) -> Self {
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
                            .map(|(name, ty)| (*name, exp_subst_map(arena, *ty, substitutions)))
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
                                    remap_all_global_ids(
                                        arena,
                                        *ty,
                                        definitions,
                                        inductives,
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

fn strictly_positive(
    arena: &Arena,
    ty: Exp,
    inductive: ProgramInductiveId,
    positive: bool,
) -> bool {
    match arena.get(ty) {
        Node::Bound(_) | Node::ModuleParam(_) => true,
        Node::ThunkType { computation_ty } => {
            strictly_positive(arena, computation_ty, inductive, positive)
        }
        Node::ReturnType { value_ty } => strictly_positive(arena, value_ty, inductive, positive),
        Node::ComputationFunction { domain, codomain } => {
            strictly_positive(arena, domain, inductive, !positive)
                && strictly_positive(arena, codomain, inductive, positive)
        }
        Node::RunStep {
            state_ty,
            result_ty,
        } => {
            strictly_positive(arena, state_ty, inductive, positive)
                && strictly_positive(arena, result_ty, inductive, positive)
        }
        Node::ProgramIndType {
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
                    indspec == inductive && strictly_positive(arena, parameter, inductive, positive)
                } else {
                    true
                }
            })
        }
        _ => false,
    }
}

pub fn contains_program_inductive(arena: &Arena, ty: Exp, inductive: ProgramInductiveId) -> bool {
    match arena.get(ty) {
        Node::ProgramIndType {
            indspec,
            parameters,
        } => {
            indspec == inductive
                || parameters
                    .into_iter()
                    .any(|parameter| contains_program_inductive(arena, parameter, inductive))
        }
        Node::ThunkType { computation_ty } => {
            contains_program_inductive(arena, computation_ty, inductive)
        }
        Node::ReturnType { value_ty } => contains_program_inductive(arena, value_ty, inductive),
        Node::ComputationFunction { domain, codomain } => {
            contains_program_inductive(arena, domain, inductive)
                || contains_program_inductive(arena, codomain, inductive)
        }
        Node::RunStep {
            state_ty,
            result_ty,
        } => {
            contains_program_inductive(arena, state_ty, inductive)
                || contains_program_inductive(arena, result_ty, inductive)
        }
        _ => false,
    }
}
