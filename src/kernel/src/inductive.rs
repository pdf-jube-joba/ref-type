use serde::Serialize;
use std::collections::HashMap;

use crate::{
    calculus::{
        exp_contains_inductive, exp_subst_map, instantiate_outer_telescope, remap_ambient_indices,
        shift_bound_indices,
    },
    derivation::{CheckSession, JudgementError},
    environment::CrateEnv,
    utils,
};

use super::exp::*;

#[derive(Debug, Clone, Serialize)]
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
        let remap = |exp| crate::calculus::remap_global_ids(arena, exp, definitions, inductives);
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

    pub fn indices(&self) -> &[(SymbolId, Exp)] {
        &self.indices
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

    pub fn constructor_len(&self) -> usize {
        self.constructors.len()
    }

    pub fn param_args_len(&self) -> usize {
        self.parameters.len()
    }

    pub fn arg_len_cst(&self, idx: usize) -> usize {
        self.constructors[idx].telescope.len()
    }

    pub fn type_of_constructor(
        arena: &Arena,
        inductive: InductiveId,
        indspec: &Self,
        idx: usize,
        parameters: Vec<Exp>,
    ) -> Exp {
        let constructor = indspec.constructors[idx].instantiate_parameters(arena, &parameters);
        let this = arena.alloc(Node::IndType {
            indspec: inductive,
            parameters,
        });
        constructor.as_exp_with_type(arena, this)
    }

    pub fn return_type_kind(
        arena: &Arena,
        inductive: InductiveId,
        indspec: &Self,
        parameters: Vec<Exp>,
        sort: Sort,
    ) -> Exp {
        let indices = indspec.instantiate_indices(arena, &parameters);
        let this = arena.alloc(Node::IndType {
            indspec: inductive,
            parameters,
        });
        let index_arguments = bound_arguments(arena, indices.len());
        let shifted_this = shift_bound_indices(arena, this, indices.len(), 0);
        let applied = utils::assoc_apply(arena, shifted_this, index_arguments);
        let result = arena.alloc(Node::Prod {
            var: SymbolId::ANONYMOUS,
            ty: applied,
            body: arena.sort(sort),
        });
        utils::assoc_prod(arena, indices, result)
    }

    pub fn validate(
        &self,
        session: &mut CheckSession<'_, '_>,
        inductive: InductiveId,
    ) -> Result<(), Box<JudgementError>> {
        let context_mark = session.context().len();
        let result = self.validate_inner(session, inductive);
        while session.context().len() > context_mark {
            session.pop();
        }
        result
    }

    fn validate_inner(
        &self,
        session: &mut CheckSession<'_, '_>,
        inductive: InductiveId,
    ) -> Result<(), Box<JudgementError>> {
        let span = tracing::debug_span!(
            target: "ref_type::typing",
            "construct_inductive_type_specs",
            ctx_len = session.context().len(),
        );
        let _entered = span.enter();

        self.validate_strict_positivity(session.arena(), inductive)?;

        for (var, parameter_ty) in &self.parameters {
            session.infer_sort(*parameter_ty).map_err(|error| {
                Box::new(error.with_frame(
                    "InductiveTypeSpecs::new",
                    format!("parameter '{var:?}' type check"),
                    "parameter is well-sorted",
                ))
            })?;
            session.push(*var, *parameter_ty);
        }

        let arity = self.arity(session.arena());
        session.infer_sort(arity).map_err(|error| {
            Box::new(error.with_frame(
                "InductiveTypeSpecs::new",
                "arity type check",
                "arity is well-sorted",
            ))
        })?;

        let parameter_arguments = bound_arguments(session.arena(), self.parameters.len());
        let this_exp = session.arena().alloc(Node::IndType {
            indspec: inductive,
            parameters: parameter_arguments,
        });
        let expected_sort = session.arena().sort(self.sort);
        for (index, constructor) in self.constructors.iter().enumerate() {
            let constructor_ty = constructor.as_exp_with_type(session.arena(), this_exp);
            session
                .check(constructor_ty, expected_sort)
                .map_err(|error| {
                    Box::new(error.with_frame(
                        "InductiveTypeSpecs::new",
                        format!("constructor '{index}' type check"),
                        "constructor is well-sorted",
                    ))
                })?;
        }

        tracing::debug!(target: "ref_type::typing", outcome = "success");
        Ok(())
    }

    fn validate_strict_positivity(
        &self,
        arena: &Arena,
        inductive: InductiveId,
    ) -> Result<(), Box<JudgementError>> {
        let reject = |location: String| {
            Box::new(JudgementError::caused(format!(
                "inductive type occurs outside a declared strictly-positive position: {location}"
            ))
            .with_frame(
                "InductiveTypeSpecs::validate",
                "strict positivity",
                "recursive occurrences use CtorBinder::StrictPositive",
            ))
        };

        for (index, (_, ty)) in self.parameters.iter().enumerate() {
            if exp_contains_inductive(arena, *ty, inductive) {
                return Err(reject(format!("parameter {index}")));
            }
        }
        for (index, (_, ty)) in self.indices.iter().enumerate() {
            if exp_contains_inductive(arena, *ty, inductive) {
                return Err(reject(format!("index {index}")));
            }
        }
        for (constructor_index, constructor) in self.constructors.iter().enumerate() {
            for (binder_index, binder) in constructor.telescope.iter().enumerate() {
                match binder {
                    CtorBinder::Simple((_, ty)) => {
                        if exp_contains_inductive(arena, *ty, inductive) {
                            return Err(reject(format!(
                                "constructor {constructor_index}, simple binder {binder_index}"
                            )));
                        }
                    }
                    CtorBinder::StrictPositive {
                        binders,
                        self_indices,
                    } => {
                        for (inner_index, (_, ty)) in binders.iter().enumerate() {
                            if exp_contains_inductive(arena, *ty, inductive) {
                                return Err(reject(format!(
                                    "constructor {constructor_index}, recursive binder {binder_index}, domain {inner_index}"
                                )));
                            }
                        }
                        for (index, self_index) in self_indices.iter().enumerate() {
                            if exp_contains_inductive(arena, *self_index, inductive) {
                                return Err(reject(format!(
                                    "constructor {constructor_index}, recursive binder {binder_index}, index {index}"
                                )));
                            }
                        }
                    }
                }
            }
            for (index, result_index) in constructor.indices.iter().enumerate() {
                if exp_contains_inductive(arena, *result_index, inductive) {
                    return Err(reject(format!(
                        "constructor {constructor_index}, result index {index}"
                    )));
                }
            }
        }
        Ok(())
    }

    pub fn instantiate(&self, arena: &Arena, substitutions: &[(ModuleParamId, Exp)]) -> Self {
        let parameters = self
            .parameters
            .iter()
            .map(|(var, ty)| (*var, exp_subst_map(arena, *ty, substitutions)))
            .collect();
        let indices = self
            .indices
            .iter()
            .map(|(var, ty)| (*var, exp_subst_map(arena, *ty, substitutions)))
            .collect();
        let constructors = self
            .constructors
            .iter()
            .map(|constructor| constructor.subst_module_params(arena, substitutions))
            .collect();
        Self::unchecked(parameters, indices, self.sort, constructors)
    }

    pub fn primitive_recursion(
        arena: &Arena,
        inductive: InductiveId,
        indspec: &Self,
        parameters: Vec<Exp>,
        sort: Sort,
    ) -> Exp {
        let this = arena.alloc(Node::IndType {
            indspec: inductive,
            parameters: parameters.clone(),
        });
        let mut telescope = vec![];
        let q = SymbolId::ANONYMOUS;
        let q_ty = Self::return_type_kind(arena, inductive, indspec, parameters.clone(), sort);
        telescope.push((q, q_ty));

        let mut cases = vec![];
        for index in 0..indspec.constructor_len() {
            let case_var = SymbolId::ANONYMOUS;
            let constructor =
                indspec.constructors[index].instantiate_parameters(arena, &parameters);
            let q_exp = arena.bound(telescope.len() - 1);
            let constructor_exp = arena.alloc(Node::IndCtor {
                indspec: inductive,
                parameters: parameters.clone(),
                idx: index,
            });
            let case_ty = eliminator_type(arena, &constructor, q_exp, constructor_exp, this);
            telescope.push((case_var, case_ty));
        }

        let c = SymbolId::ANONYMOUS;
        let indices = indspec.instantiate_indices(arena, &parameters);
        let case_count = indspec.constructor_len();
        let index_arguments = bound_arguments(arena, indices.len());
        let shifted_this = shift_bound_indices(arena, this, telescope.len() + indices.len(), 0);
        let c_ty = utils::assoc_apply(arena, shifted_this, index_arguments);
        telescope.extend(indices);
        telescope.push((c, c_ty));

        let final_len = telescope.len();
        cases.extend((0..case_count).map(|index| arena.bound(final_len - 1 - (1 + index))));
        let body = arena.alloc(Node::IndElim {
            indspec: inductive,
            elim: arena.bound(0),
            return_type: arena.bound(final_len - 1),
            cases,
        });
        utils::assoc_lam(arena, telescope, body)
    }

    fn instantiate_indices(&self, arena: &Arena, parameters: &[Exp]) -> Vec<(SymbolId, Exp)> {
        self.indices
            .iter()
            .enumerate()
            .map(|(inner, (name, ty))| {
                (
                    *name,
                    instantiate_outer_telescope(arena, *ty, parameters, inner),
                )
            })
            .collect()
    }
}

fn bound_arguments(arena: &Arena, len: usize) -> Vec<Exp> {
    (0..len).rev().map(|index| arena.bound(index)).collect()
}

#[derive(Debug, Clone, Serialize)]
pub struct CtorType {
    pub telescope: Vec<CtorBinder>,
    pub indices: Vec<Exp>,
}

#[derive(Debug, Clone, Serialize)]
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
        let remap = |exp| crate::calculus::remap_global_ids(arena, exp, definitions, inductives);
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
    ) -> Self {
        Self {
            telescope: self
                .telescope
                .iter()
                .map(|binder| match binder {
                    CtorBinder::StrictPositive {
                        binders,
                        self_indices,
                    } => CtorBinder::StrictPositive {
                        binders: binders
                            .iter()
                            .map(|(var, ty)| (*var, exp_subst_map(arena, *ty, substitutions)))
                            .collect(),
                        self_indices: self_indices
                            .iter()
                            .map(|index| exp_subst_map(arena, *index, substitutions))
                            .collect(),
                    },
                    CtorBinder::Simple((var, ty)) => {
                        CtorBinder::Simple((*var, exp_subst_map(arena, *ty, substitutions)))
                    }
                })
                .collect(),
            indices: self
                .indices
                .iter()
                .map(|index| exp_subst_map(arena, *index, substitutions))
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

pub fn eliminator_type(
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
                applied_constructor = arena.alloc(Node::App {
                    func: applied_constructor,
                    arg: arena.bound(0),
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
                applied_constructor = arena.alloc(Node::App {
                    func: applied_constructor,
                    arg: arena.bound(0),
                });
                telescope.push((SymbolId::ANONYMOUS, recursive_ty));
                constructor_positions.push(telescope.len() - 1);

                let recursive_arguments = bound_arguments(arena, binders.len());
                let recursive_call =
                    utils::assoc_apply(arena, arena.bound(binders.len()), recursive_arguments);
                let shifted_q = shift_bound_indices(arena, q, telescope.len() + binders.len(), 0);
                let motive = utils::assoc_apply(arena, shifted_q, recursive_indices);
                let hypothesis_result = arena.alloc(Node::App {
                    func: motive,
                    arg: recursive_call,
                });
                let hypothesis_ty = utils::assoc_prod(arena, recursive_binders, hypothesis_result);
                telescope.push((SymbolId::ANONYMOUS, hypothesis_ty));
                applied_constructor = shift_bound_indices(arena, applied_constructor, 1, 0);
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
    let result = arena.alloc(Node::App {
        func: motive,
        arg: applied_constructor,
    });
    utils::assoc_prod(arena, telescope, result)
}

pub fn recursor(arena: &Arena, constructor: &CtorType, q: Exp, case: Exp, this: Exp) -> Exp {
    let mut result = case;
    let mut telescope = vec![];
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
                result = shift_bound_indices(arena, result, 1, 0);
                result = arena.alloc(Node::App {
                    func: result,
                    arg: arena.bound(0),
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
                let recursive_arguments = bound_arguments(arena, binders.len());
                let recursive_call =
                    utils::assoc_apply(arena, arena.bound(binders.len()), recursive_arguments);
                let shifted_q =
                    shift_bound_indices(arena, q, telescope.len() + 1 + binders.len(), 0);
                let motive = utils::assoc_apply(arena, shifted_q, recursive_indices.clone());
                let hypothesis_body = arena.alloc(Node::App {
                    func: motive,
                    arg: recursive_call,
                });
                let hypothesis =
                    utils::assoc_lam(arena, recursive_binders.clone(), hypothesis_body);
                result = shift_bound_indices(arena, result, 1, 0);
                let with_argument = arena.alloc(Node::App {
                    func: result,
                    arg: arena.bound(0),
                });
                result = arena.alloc(Node::App {
                    func: with_argument,
                    arg: hypothesis,
                });
                let shifted_this =
                    shift_bound_indices(arena, this, telescope.len() + binders.len(), 0);
                let recursive_result = utils::assoc_apply(arena, shifted_this, recursive_indices);
                let recursive_ty = utils::assoc_prod(arena, recursive_binders, recursive_result);
                telescope.push((SymbolId::ANONYMOUS, recursive_ty));
                constructor_positions.push(telescope.len() - 1);
            }
        }
    }
    utils::assoc_lam(arena, telescope, result)
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

struct RedexShape {
    inductive: InductiveId,
    index: usize,
    parameters: Vec<Exp>,
    arguments: Vec<Exp>,
    return_type: Exp,
    cases: Vec<Exp>,
}

fn indelim_shapecheck(env: &CrateEnv, exp: Exp) -> Result<RedexShape, String> {
    let arena = env.arena();
    let Node::IndElim {
        indspec,
        elim,
        return_type,
        cases,
    } = arena.get(exp)
    else {
        return Err("Not an InductiveTypeElim".into());
    };
    let (head, arguments) = utils::decompose_app(arena, elim);
    let Node::IndCtor {
        indspec: constructor_spec,
        idx,
        parameters,
    } = arena.get(head)
    else {
        return Err("Elim is not an InductiveTypeCst".into());
    };
    if indspec != constructor_spec {
        return Err("Elim type mismatch".into());
    }
    let spec = env.inductive(indspec);
    if idx >= spec.constructor_len() {
        return Err("Constructor index out of bounds".into());
    }
    if parameters.len() != spec.param_args_len() {
        return Err("Constructor parameter arguments length mismatch".into());
    }
    if arguments.len() != spec.arg_len_cst(idx) {
        return Err("Constructor arguments length mismatch".into());
    }
    if cases.len() != spec.constructor_len() {
        return Err("Cases length mismatch".into());
    }
    Ok(RedexShape {
        inductive: indspec,
        index: idx,
        parameters,
        arguments,
        return_type,
        cases,
    })
}

pub fn inductive_type_elim_reduce(env: &CrateEnv, exp: Exp) -> Result<Exp, String> {
    let arena = env.arena();
    let RedexShape {
        inductive,
        index,
        parameters,
        arguments,
        return_type,
        cases,
    } = indelim_shapecheck(env, exp)?;
    let spec = env.inductive(inductive);
    let indices = spec.instantiate_indices(arena, &parameters);
    let this = arena.alloc(Node::IndType {
        indspec: inductive,
        parameters: parameters.clone(),
    });
    let index_arguments = bound_arguments(arena, indices.len());
    let shifted_this = shift_bound_indices(arena, this, indices.len(), 0);
    let c_ty = utils::assoc_apply(arena, shifted_this, index_arguments);
    let body_depth = indices.len() + 1;
    let body = arena.alloc(Node::IndElim {
        indspec: inductive,
        elim: arena.bound(0),
        return_type: shift_bound_indices(arena, return_type, body_depth, 0),
        cases: cases
            .iter()
            .map(|case| shift_bound_indices(arena, *case, body_depth, 0))
            .collect(),
    });
    let body = arena.alloc(Node::Lam {
        var: SymbolId::ANONYMOUS,
        ty: c_ty,
        body,
    });
    let motive = utils::assoc_lam(arena, indices, body);

    let constructor = spec.constructors[index].instantiate_parameters(arena, &parameters);
    let recursive = recursor(arena, &constructor, motive, cases[index], this);
    Ok(utils::assoc_apply(arena, recursive, arguments))
}
