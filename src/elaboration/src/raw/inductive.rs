use super::exp::*;
use crate::{
    kernel_bridge::{instantiate_outer_telescope, remap_ambient_indices, shift_bound_indices},
    raw::{
        derivation::{CheckSession, JudgementError},
        ids::{DefId, InductiveId, ModuleParamId, SymbolId},
        remapping::exp_subst_map,
        sort::Sort,
        utils,
    },
};
use std::collections::HashMap;

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct InductiveTypeSpecs {
    parameters: Vec<(SymbolId, Exp)>,
    indices: Vec<(SymbolId, Exp)>,
    sort: Sort,
    constructors: Vec<CtorType>,
}

impl InductiveTypeSpecs {
    pub fn remap_global_ids(
        &self,
        arena: &Arena,
        definitions: &HashMap<DefId, DefId>,
        inductives: &HashMap<InductiveId, InductiveId>,
    ) -> Self {
        let remap =
            |exp| crate::raw::remapping::remap_global_ids(arena, exp, definitions, inductives);
        Self {
            parameters: self
                .parameters
                .iter()
                .map(|(var, ty)| (*var, remap(*ty)))
                .collect(),
            indices: self
                .indices
                .iter()
                .map(|(var, ty)| (*var, remap(*ty)))
                .collect(),
            sort: self.sort,
            constructors: self
                .constructors
                .iter()
                .map(|constructor| constructor.remap_global_ids(arena, definitions, inductives))
                .collect(),
        }
    }

    pub fn unchecked(
        parameters: Vec<(SymbolId, Exp)>,
        indices: Vec<(SymbolId, Exp)>,
        sort: Sort,
        constructors: Vec<CtorType>,
    ) -> Self {
        Self {
            parameters,
            indices,
            sort,
            constructors,
        }
    }

    pub fn parameters(&self) -> &[(SymbolId, Exp)] {
        &self.parameters
    }

    pub fn sort(&self) -> Sort {
        self.sort
    }

    pub fn constructors(&self) -> &[CtorType] {
        &self.constructors
    }

    pub fn arity(&self, arena: &Arena) -> Exp {
        let sort = arena.sort(self.sort);
        utils::assoc_prod(arena, self.indices.clone(), sort)
    }

    pub fn type_of_constructor(
        arena: &Arena,
        inductive: InductiveId,
        indspec: &Self,
        idx: usize,
        parameters: Vec<Exp>,
    ) -> Exp {
        let constructor = indspec.constructors[idx].instantiate_parameters(arena, &parameters);
        let this = arena.alloc(ExpNode::IndType {
            indspec: inductive,
            parameters,
        });
        constructor.as_exp_with_type(arena, this)
    }

    pub fn validate(
        &self,
        session: &mut CheckSession<'_, '_>,
        inductive: InductiveId,
    ) -> Result<(), Box<JudgementError>> {
        let term = session.arena().alloc(ExpNode::IndType {
            indspec: inductive,
            parameters: vec![],
        });
        crate::kernel_bridge::logical(session.env(), session.context(), &[term], |_, _, _| Ok(()))
            .map_err(|e| Box::new(JudgementError::caused(e)))
    }

    pub fn instantiate(&self, arena: &Arena, substitutions: &[(ModuleParamId, Exp)]) -> Self {
        let subst = |e, depth| substitute_under(arena, e, substitutions, depth);
        let parameters = self
            .parameters
            .iter()
            .enumerate()
            .map(|(i, (v, t))| (*v, subst(*t, i)))
            .collect();
        let indices = self
            .indices
            .iter()
            .enumerate()
            .map(|(i, (v, t))| (*v, subst(*t, self.parameters.len() + i)))
            .collect();
        let constructors = self
            .constructors
            .iter()
            .map(|ctor| ctor.subst_module_params(arena, substitutions, self.parameters.len()))
            .collect();
        Self::unchecked(parameters, indices, self.sort, constructors)
    }
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct CtorType {
    pub telescope: Vec<CtorBinder>,
    pub indices: Vec<Exp>,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub enum CtorBinder {
    StrictPositive {
        binders: Vec<(SymbolId, Exp)>,
        self_indices: Vec<Exp>,
    },
    Simple((SymbolId, Exp)),
}

impl CtorType {
    fn remap_global_ids(
        &self,
        arena: &Arena,
        definitions: &HashMap<DefId, DefId>,
        inductives: &HashMap<InductiveId, InductiveId>,
    ) -> Self {
        let remap =
            |exp| crate::raw::remapping::remap_global_ids(arena, exp, definitions, inductives);
        Self {
            telescope: self
                .telescope
                .iter()
                .map(|binder| match binder {
                    CtorBinder::StrictPositive {
                        binders,
                        self_indices,
                    } => CtorBinder::StrictPositive {
                        binders: binders.iter().map(|(var, ty)| (*var, remap(*ty))).collect(),
                        self_indices: self_indices.iter().map(|index| remap(*index)).collect(),
                    },
                    CtorBinder::Simple((var, ty)) => CtorBinder::Simple((*var, remap(*ty))),
                })
                .collect(),
            indices: self.indices.iter().map(|index| remap(*index)).collect(),
        }
    }

    pub fn as_exp_with_type(&self, arena: &Arena, this: Exp) -> Exp {
        let mut telescope = vec![];
        for binder in &self.telescope {
            let outer = telescope.len();
            match binder {
                CtorBinder::StrictPositive {
                    binders,
                    self_indices,
                } => {
                    let shifted_this = shift_bound_indices(arena, this, outer + binders.len(), 0);
                    let applied = utils::assoc_apply(arena, shifted_this, self_indices.clone());
                    let ty = utils::assoc_prod(arena, binders.clone(), applied);
                    telescope.push((SymbolId::ANONYMOUS, ty));
                }
                CtorBinder::Simple((var, ty)) => telescope.push((*var, *ty)),
            }
        }
        let shifted_this = shift_bound_indices(arena, this, telescope.len(), 0);
        let result = utils::assoc_apply(arena, shifted_this, self.indices.clone());
        utils::assoc_prod(arena, telescope, result)
    }

    pub fn subst_module_params(
        &self,
        arena: &Arena,
        substitutions: &[(ModuleParamId, Exp)],
        parameter_count: usize,
    ) -> Self {
        let subst = |e, depth| substitute_under(arena, e, substitutions, depth);
        Self {
            telescope: self
                .telescope
                .iter()
                .enumerate()
                .map(|(i, binder)| {
                    let depth = parameter_count + i;
                    match binder {
                        CtorBinder::Simple((v, t)) => CtorBinder::Simple((*v, subst(*t, depth))),
                        CtorBinder::StrictPositive {
                            binders,
                            self_indices,
                        } => CtorBinder::StrictPositive {
                            binders: binders
                                .iter()
                                .enumerate()
                                .map(|(j, (v, t))| (*v, subst(*t, depth + j)))
                                .collect(),
                            self_indices: self_indices
                                .iter()
                                .map(|e| subst(*e, depth + binders.len()))
                                .collect(),
                        },
                    }
                })
                .collect(),
            indices: self
                .indices
                .iter()
                .map(|e| subst(*e, parameter_count + self.telescope.len()))
                .collect(),
        }
    }

    pub fn instantiate_parameters(&self, arena: &Arena, parameters: &[Exp]) -> Self {
        let mut outer = 0;
        let telescope = self
            .telescope
            .iter()
            .map(|binder| {
                let result = match binder {
                    CtorBinder::Simple((name, ty)) => CtorBinder::Simple((
                        *name,
                        instantiate_outer_telescope(arena, *ty, parameters, outer),
                    )),
                    CtorBinder::StrictPositive {
                        binders,
                        self_indices,
                    } => CtorBinder::StrictPositive {
                        binders: binders
                            .iter()
                            .enumerate()
                            .map(|(inner, (name, ty))| {
                                (
                                    *name,
                                    instantiate_outer_telescope(
                                        arena,
                                        *ty,
                                        parameters,
                                        outer + inner,
                                    ),
                                )
                            })
                            .collect(),
                        self_indices: self_indices
                            .iter()
                            .map(|index| {
                                instantiate_outer_telescope(
                                    arena,
                                    *index,
                                    parameters,
                                    outer + binders.len(),
                                )
                            })
                            .collect(),
                    },
                };
                outer += 1;
                result
            })
            .collect();
        let indices = self
            .indices
            .iter()
            .map(|index| instantiate_outer_telescope(arena, *index, parameters, outer))
            .collect();
        Self { telescope, indices }
    }
}

pub fn case_type(
    arena: &Arena,
    constructor: &CtorType,
    q: Exp,
    constructor_term: Exp,
    this: Exp,
) -> Exp {
    let mut telescope = vec![];
    let mut applied_constructor = constructor_term;
    let mut constructor_positions = Vec::new();
    for binder in &constructor.telescope {
        let original_outer = constructor_positions.len();
        match binder {
            CtorBinder::Simple((var, ty)) => {
                let ty = rebase_from_constructor(
                    arena,
                    *ty,
                    0,
                    original_outer,
                    &constructor_positions,
                    telescope.len(),
                );
                applied_constructor = shift_bound_indices(arena, applied_constructor, 1, 0);
                applied_constructor = arena.alloc(ExpNode::App {
                    func: applied_constructor,
                    arg: arena.exp_bound(0),
                });
                telescope.push((*var, ty));
                constructor_positions.push(telescope.len() - 1);
            }
            CtorBinder::StrictPositive {
                binders,
                self_indices,
            } => {
                let recursive_binders = rebase_nested_telescope(
                    arena,
                    binders,
                    original_outer,
                    &constructor_positions,
                    telescope.len(),
                );
                let nested_mapping = constructor_mapping(
                    binders.len(),
                    original_outer,
                    &constructor_positions,
                    telescope.len(),
                );
                let recursive_indices = self_indices
                    .iter()
                    .map(|index| remap_ambient_indices(arena, *index, &nested_mapping))
                    .collect::<Vec<_>>();
                let shifted_this =
                    shift_bound_indices(arena, this, telescope.len() + binders.len(), 0);
                let recursive_result =
                    utils::assoc_apply(arena, shifted_this, recursive_indices.clone());
                let recursive_ty =
                    utils::assoc_prod(arena, recursive_binders.clone(), recursive_result);

                applied_constructor = shift_bound_indices(arena, applied_constructor, 1, 0);
                applied_constructor = arena.alloc(ExpNode::App {
                    func: applied_constructor,
                    arg: arena.exp_bound(0),
                });
                telescope.push((SymbolId::ANONYMOUS, recursive_ty));
                constructor_positions.push(telescope.len() - 1);
            }
        }
    }
    let mapping = constructor_mapping(
        0,
        constructor_positions.len(),
        &constructor_positions,
        telescope.len(),
    );
    let indices = constructor
        .indices
        .iter()
        .map(|index| remap_ambient_indices(arena, *index, &mapping))
        .collect();
    let shifted_q = shift_bound_indices(arena, q, telescope.len(), 0);
    let motive = utils::assoc_apply(arena, shifted_q, indices);
    let result = match arena.get(motive) {
        ExpNode::Lam { body, .. } => {
            crate::kernel_bridge::instantiate(arena, body, applied_constructor)
        }
        _ => arena.alloc(ExpNode::App {
            func: motive,
            arg: applied_constructor,
        }),
    };
    utils::assoc_prod(arena, telescope, result)
}

fn constructor_mapping(
    inner: usize,
    original_outer: usize,
    positions: &[usize],
    generated_len: usize,
) -> Vec<usize> {
    let mut mapping = (0..inner).collect::<Vec<_>>();
    mapping.extend((0..original_outer).map(|old_index| {
        let declaration = original_outer - 1 - old_index;
        inner + generated_len - 1 - positions[declaration]
    }));
    mapping
}

fn rebase_from_constructor(
    arena: &Arena,
    exp: Exp,
    inner: usize,
    original_outer: usize,
    positions: &[usize],
    generated_len: usize,
) -> Exp {
    let mapping = constructor_mapping(inner, original_outer, positions, generated_len);
    remap_ambient_indices(arena, exp, &mapping)
}

fn rebase_nested_telescope(
    arena: &Arena,
    binders: &[(SymbolId, Exp)],
    original_outer: usize,
    positions: &[usize],
    generated_len: usize,
) -> Vec<(SymbolId, Exp)> {
    binders
        .iter()
        .enumerate()
        .map(|(inner, (name, ty))| {
            (
                *name,
                rebase_from_constructor(
                    arena,
                    *ty,
                    inner,
                    original_outer,
                    positions,
                    generated_len,
                ),
            )
        })
        .collect()
}

fn substitute_under(
    arena: &Arena,
    e: Exp,
    substitutions: &[(ModuleParamId, Exp)],
    depth: usize,
) -> Exp {
    let substitutions = substitutions
        .iter()
        .map(|(p, a)| (*p, shift_bound_indices(arena, *a, depth, 0)))
        .collect::<Vec<_>>();
    exp_subst_map(arena, e, &substitutions)
}
