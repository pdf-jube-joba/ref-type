use std::rc::Rc;

use serde::Serialize;

use crate::{
    calculus::exp_subst_map,
    derivation::{CheckSession, JudgementError},
    utils,
};

use super::exp::*;

#[derive(Debug, Clone, Serialize)]
pub struct InductiveTypeSpecs {
    parameters: Vec<(Var, Exp)>,
    indices: Vec<(Var, Exp)>,
    sort: Sort,
    constructors: Vec<CtorType>,
}

impl InductiveTypeSpecs {
    pub fn new(
        session: &mut CheckSession<'_, '_>,
        parameters: Vec<(Var, Exp)>,
        indices: Vec<(Var, Exp)>,
        sort: Sort,
        constructors: Vec<CtorType>,
    ) -> Result<Self, Box<JudgementError>> {
        let specs = Self {
            parameters,
            indices,
            sort,
            constructors,
        };
        specs.validate(session)?;
        Ok(specs)
    }

    pub fn parameters(&self) -> &[(Var, Exp)] {
        &self.parameters
    }

    pub fn indices(&self) -> &[(Var, Exp)] {
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
        indspec: &Rc<Self>,
        idx: usize,
        parameters: Vec<Exp>,
    ) -> Exp {
        let this = arena.alloc(Node::IndType {
            indspec: indspec.clone(),
            parameters,
        });
        indspec.constructors[idx].as_exp_with_type(arena, this)
    }

    pub fn return_type_kind(
        arena: &Arena,
        indspec: &Rc<Self>,
        parameters: Vec<Exp>,
        sort: Sort,
    ) -> Exp {
        let substitutions = indspec.parameter_subst_mapping(&parameters);
        let indices = indspec
            .indices
            .iter()
            .map(|(var, ty)| (var.clone(), exp_subst_map(arena, *ty, &substitutions)))
            .collect::<Vec<_>>();
        let this = arena.alloc(Node::IndType {
            indspec: indspec.clone(),
            parameters,
        });
        let index_arguments = indices
            .iter()
            .map(|(var, _)| arena.var(var.clone()))
            .collect();
        let applied = utils::assoc_apply(arena, this, index_arguments);
        let result = arena.alloc(Node::Prod {
            var: Var::dummy(),
            ty: applied,
            body: arena.sort(sort),
        });
        utils::assoc_prod(arena, indices, result)
    }

    fn validate(&self, session: &mut CheckSession<'_, '_>) -> Result<(), Box<JudgementError>> {
        let context_mark = session.context().len();
        let result = self.validate_inner(session);
        while session.context().len() > context_mark {
            session.pop();
        }
        result
    }

    fn validate_inner(
        &self,
        session: &mut CheckSession<'_, '_>,
    ) -> Result<(), Box<JudgementError>> {
        let span = tracing::debug_span!(
            target: "ref_type::typing",
            "construct_inductive_type_specs",
            ctx_len = session.context().len(),
        );
        let _entered = span.enter();

        for (var, parameter_ty) in &self.parameters {
            session.infer_sort(*parameter_ty).map_err(|error| {
                Box::new(error.with_frame(
                    "InductiveTypeSpecs::new",
                    format!("parameter '{var:?}' type check"),
                    "parameter is well-sorted",
                ))
            })?;
            session.push(var.clone(), *parameter_ty);
        }

        let arity = self.arity(session.arena());
        session.infer_sort(arity).map_err(|error| {
            Box::new(error.with_frame(
                "InductiveTypeSpecs::new",
                "arity type check",
                "arity is well-sorted",
            ))
        })?;

        let this = Var::new("THIS");
        session.push(this.clone(), arity);
        let this_exp = session.arena().var(this);
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

    pub(crate) fn parameter_subst_mapping(&self, parameters: &[Exp]) -> Vec<(Var, Exp)> {
        self.parameters
            .iter()
            .zip(parameters)
            .map(|((var, _), expression)| (var.clone(), *expression))
            .collect()
    }

    pub fn instantiate(
        &self,
        session: &mut CheckSession<'_, '_>,
        substitutions: &[(Var, Exp)],
    ) -> Result<Self, Box<JudgementError>> {
        let arena = session.arena();
        let parameters = self
            .parameters
            .iter()
            .map(|(var, ty)| (var.clone(), exp_subst_map(arena, *ty, substitutions)))
            .collect();
        let indices = self
            .indices
            .iter()
            .map(|(var, ty)| (var.clone(), exp_subst_map(arena, *ty, substitutions)))
            .collect();
        let constructors = self
            .constructors
            .iter()
            .map(|constructor| constructor.subst(arena, substitutions))
            .collect();
        Self::new(session, parameters, indices, self.sort, constructors)
    }

    pub fn primitive_recursion(
        arena: &Arena,
        indspec: &Rc<Self>,
        parameters: Vec<Exp>,
        sort: Sort,
    ) -> Exp {
        let this = arena.alloc(Node::IndType {
            indspec: indspec.clone(),
            parameters: parameters.clone(),
        });
        let mut telescope = vec![];
        let q = Var::new("q");
        let q_ty = Self::return_type_kind(arena, indspec, parameters.clone(), sort);
        telescope.push((q.clone(), q_ty));
        let substitutions = indspec.parameter_subst_mapping(&parameters);

        let mut cases = vec![];
        for index in 0..indspec.constructor_len() {
            let case_var = Var::new(&format!("f{index}"));
            let constructor = indspec.constructors[index].subst(arena, &substitutions);
            let q_exp = arena.var(q.clone());
            let constructor_exp = arena.alloc(Node::IndCtor {
                indspec: indspec.clone(),
                parameters: parameters.clone(),
                idx: index,
            });
            let case_ty = eliminator_type(arena, &constructor, q_exp, constructor_exp, this);
            telescope.push((case_var.clone(), case_ty));
            cases.push(arena.var(case_var));
        }

        let c = Var::new("c");
        let indices = indspec
            .indices
            .iter()
            .map(|(var, ty)| (var.clone(), exp_subst_map(arena, *ty, &substitutions)))
            .collect::<Vec<_>>();
        let index_arguments = indices
            .iter()
            .map(|(var, _)| arena.var(var.clone()))
            .collect();
        let c_ty = utils::assoc_apply(arena, this, index_arguments);
        telescope.extend(indices);
        telescope.push((c.clone(), c_ty));

        let body = arena.alloc(Node::IndElim {
            indspec: indspec.clone(),
            elim: arena.var(c),
            return_type: arena.var(q),
            cases,
        });
        utils::assoc_lam(arena, telescope, body)
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct CtorType {
    pub telescope: Vec<CtorBinder>,
    pub indices: Vec<Exp>,
}

#[derive(Debug, Clone, Serialize)]
pub enum CtorBinder {
    StrictPositive {
        binders: Vec<(Var, Exp)>,
        self_indices: Vec<Exp>,
    },
    Simple((Var, Exp)),
}

impl CtorType {
    pub fn as_exp_with_type(&self, arena: &Arena, this: Exp) -> Exp {
        let mut telescope = vec![];
        for binder in &self.telescope {
            match binder {
                CtorBinder::StrictPositive {
                    binders,
                    self_indices,
                } => {
                    let applied = utils::assoc_apply(arena, this, self_indices.clone());
                    let ty = utils::assoc_prod(arena, binders.clone(), applied);
                    telescope.push((Var::dummy(), ty));
                }
                CtorBinder::Simple((var, ty)) => telescope.push((var.clone(), *ty)),
            }
        }
        let result = utils::assoc_apply(arena, this, self.indices.clone());
        utils::assoc_prod(arena, telescope, result)
    }

    pub fn subst(&self, arena: &Arena, substitutions: &[(Var, Exp)]) -> Self {
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
                            .map(|(var, ty)| {
                                (var.clone(), exp_subst_map(arena, *ty, substitutions))
                            })
                            .collect(),
                        self_indices: self_indices
                            .iter()
                            .map(|index| exp_subst_map(arena, *index, substitutions))
                            .collect(),
                    },
                    CtorBinder::Simple((var, ty)) => {
                        CtorBinder::Simple((var.clone(), exp_subst_map(arena, *ty, substitutions)))
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
    for binder in &constructor.telescope {
        match binder {
            CtorBinder::Simple((var, ty)) => {
                applied_constructor = arena.alloc(Node::App {
                    func: applied_constructor,
                    arg: arena.var(var.clone()),
                });
                telescope.push((var.clone(), *ty));
            }
            CtorBinder::StrictPositive {
                binders,
                self_indices,
            } => {
                let recursive_var = Var::new("p");
                applied_constructor = arena.alloc(Node::App {
                    func: applied_constructor,
                    arg: arena.var(recursive_var.clone()),
                });
                let recursive_result = utils::assoc_apply(arena, this, self_indices.clone());
                let recursive_ty = utils::assoc_prod(arena, binders.clone(), recursive_result);
                telescope.push((recursive_var.clone(), recursive_ty));

                let recursive_arguments = binders
                    .iter()
                    .map(|(var, _)| arena.var(var.clone()))
                    .collect();
                let recursive_call =
                    utils::assoc_apply(arena, arena.var(recursive_var), recursive_arguments);
                let motive = utils::assoc_apply(arena, q, self_indices.clone());
                let hypothesis_result = arena.alloc(Node::App {
                    func: motive,
                    arg: recursive_call,
                });
                let hypothesis_ty = utils::assoc_prod(arena, binders.clone(), hypothesis_result);
                telescope.push((Var::dummy(), hypothesis_ty));
            }
        }
    }
    let motive = utils::assoc_apply(arena, q, constructor.indices.clone());
    let result = arena.alloc(Node::App {
        func: motive,
        arg: applied_constructor,
    });
    utils::assoc_prod(arena, telescope, result)
}

pub fn recursor(arena: &Arena, constructor: &CtorType, q: Exp, case: Exp, this: Exp) -> Exp {
    let mut result = case;
    let mut telescope = vec![];
    for binder in &constructor.telescope {
        match binder {
            CtorBinder::Simple((var, ty)) => {
                result = arena.alloc(Node::App {
                    func: result,
                    arg: arena.var(var.clone()),
                });
                telescope.push((var.clone(), *ty));
            }
            CtorBinder::StrictPositive {
                binders,
                self_indices,
            } => {
                let recursive_var = Var::new("p");
                let recursive_arguments = binders
                    .iter()
                    .map(|(var, _)| arena.var(var.clone()))
                    .collect();
                let recursive_call = utils::assoc_apply(
                    arena,
                    arena.var(recursive_var.clone()),
                    recursive_arguments,
                );
                let motive = utils::assoc_apply(arena, q, self_indices.clone());
                let hypothesis_body = arena.alloc(Node::App {
                    func: motive,
                    arg: recursive_call,
                });
                let hypothesis = utils::assoc_lam(arena, binders.clone(), hypothesis_body);
                let with_argument = arena.alloc(Node::App {
                    func: result,
                    arg: arena.var(recursive_var.clone()),
                });
                result = arena.alloc(Node::App {
                    func: with_argument,
                    arg: hypothesis,
                });
                let recursive_result = utils::assoc_apply(arena, this, self_indices.clone());
                let recursive_ty = utils::assoc_prod(arena, binders.clone(), recursive_result);
                telescope.push((recursive_var, recursive_ty));
            }
        }
    }
    utils::assoc_lam(arena, telescope, result)
}

struct RedexShape {
    spec: Rc<InductiveTypeSpecs>,
    index: usize,
    parameters: Vec<Exp>,
    arguments: Vec<Exp>,
    return_type: Exp,
    cases: Vec<Exp>,
}

fn indelim_shapecheck(arena: &Arena, exp: Exp) -> Result<RedexShape, String> {
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
    if !Rc::ptr_eq(&indspec, &constructor_spec) {
        return Err("Elim type mismatch".into());
    }
    if idx >= indspec.constructor_len() {
        return Err("Constructor index out of bounds".into());
    }
    if parameters.len() != indspec.param_args_len() {
        return Err("Constructor parameter arguments length mismatch".into());
    }
    if arguments.len() != indspec.arg_len_cst(idx) {
        return Err("Constructor arguments length mismatch".into());
    }
    if cases.len() != indspec.constructor_len() {
        return Err("Cases length mismatch".into());
    }
    Ok(RedexShape {
        spec: indspec,
        index: idx,
        parameters,
        arguments,
        return_type,
        cases,
    })
}

pub fn inductive_type_elim_reduce(arena: &Arena, exp: Exp) -> Result<Exp, String> {
    let RedexShape {
        spec,
        index,
        parameters,
        arguments,
        return_type,
        cases,
    } = indelim_shapecheck(arena, exp)?;
    let substitutions = spec.parameter_subst_mapping(&parameters);

    let c = Var::new("c");
    let body = arena.alloc(Node::IndElim {
        indspec: spec.clone(),
        elim: arena.var(c.clone()),
        return_type,
        cases: cases.clone(),
    });
    let indices = spec
        .indices
        .iter()
        .map(|(var, ty)| (var.clone(), exp_subst_map(arena, *ty, &substitutions)))
        .collect::<Vec<_>>();
    let this = arena.alloc(Node::IndType {
        indspec: spec.clone(),
        parameters: parameters.clone(),
    });
    let index_arguments = indices
        .iter()
        .map(|(var, _)| arena.var(var.clone()))
        .collect();
    let c_ty = utils::assoc_apply(arena, this, index_arguments);
    let body = arena.alloc(Node::Lam {
        var: c,
        ty: c_ty,
        body,
    });
    let motive = utils::assoc_lam(arena, indices, body);

    let constructor = spec.constructors[index].subst(arena, &substitutions);
    let recursive = recursor(arena, &constructor, motive, cases[index], this);
    Ok(utils::assoc_apply(arena, recursive, arguments))
}
