use std::rc::Rc;

use crate::elaborator::{ErrorKind, ItemAccessResult};
use crate::syntax::*;
use kernel::calculus::exp_subst_map;
use kernel::exp::*;
use kernel::inductive::InductiveTypeSpecs;

pub trait Handler {
    fn get_item_from_access_path(
        &self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, ErrorKind>;
    #[allow(dead_code)]
    fn get_definition_from_access_path(
        &self,
        access_path: &LocalAccess,
    ) -> Result<Rc<DefinedConstant>, ErrorKind> {
        let item = self.get_item_from_access_path(access_path)?;
        match item {
            ItemAccessResult::Definition { rc } => Ok(rc.clone()),
            _ => Err(ErrorKind::Msg(format!(
                "Expected definition in path {:?}",
                access_path
            ))),
        }
    }
    fn get_inductive_type_from_access_path(
        &self,
        access_path: &LocalAccess,
    ) -> Result<Rc<InductiveTypeSpecs>, ErrorKind> {
        let item = self.get_item_from_access_path(access_path)?;
        match item {
            ItemAccessResult::Inductive { ind_defs } => Ok(ind_defs.clone()),
            _ => Err(ErrorKind::Msg(format!(
                "Expected inductive type in path {:?}",
                access_path
            ))),
        }
    }
    fn field_projection(&self, e: &Exp, field_name: &Identifier) -> Result<Exp, ErrorKind>;

    #[allow(dead_code)]
    fn get_item_from_var(&self, var: &Identifier) -> Result<ItemAccessResult, ErrorKind>;
}

// local scope during elaboration
#[derive(Debug, Clone)]
pub struct LocalScope {
    // for find binded variables inside term
    // lambda abstraction variables, product, subset,
    // after any call of elab_exp outside the elab_exp, this should be cleared
    binded_vars: Vec<Var>,
    // for find decl levels
    decl_binds: Vec<Var>,
}

impl Default for LocalScope {
    fn default() -> Self {
        Self::new()
    }
}

impl LocalScope {
    pub fn new() -> Self {
        LocalScope {
            binded_vars: vec![],
            decl_binds: vec![],
        }
    }

    pub fn push_decl_var(&mut self, var: Var) {
        self.decl_binds.push(var);
    }

    // does not pop decl_binds
    pub fn elab_telescope_bind_in_decl(
        &mut self,
        binds: &[RightBind],
        handler: &impl Handler,
    ) -> Result<Vec<(Var, Exp)>, ErrorKind> {
        let mut result = vec![];
        for RightBind { vars, ty } in binds.iter() {
            let ty_elab = self.elab_exp(ty, handler)?;
            for var in vars {
                let var = Var::new(var.as_str());
                result.push((var.clone(), ty_elab.clone()));
                self.push_decl_var(var);
            }
        }
        Ok(result)
    }

    fn get_var(&self, name: &Identifier) -> Option<Var> {
        for v in self.binded_vars.iter().rev() {
            if v.as_str() == name.as_str() {
                return Some(v.clone());
            }
        }
        for v in self.decl_binds.iter().rev() {
            if v.as_str() == name.as_str() {
                return Some(v.clone());
            }
        }
        None
    }

    fn push_binded_var(&mut self, var: Var) {
        self.binded_vars.push(var);
    }
    fn pop_binded_var(&mut self) {
        self.binded_vars.pop();
    }

    pub fn elab_exp(&mut self, exp: &SExp, handler: &impl Handler) -> Result<Exp, ErrorKind> {
        assert!(self.binded_vars.is_empty());
        let e = self.elab_exp_rec(exp, handler);
        assert!(self.binded_vars.is_empty());
        e
    }

    pub fn elab_exp_rec(&mut self, exp: &SExp, handler: &impl Handler) -> Result<Exp, ErrorKind> {
        match exp {
            SExp::AccessPath { access, parameters } => {
                // this includes (term binding) access path

                // 1. find from binded vars first (if no parameters)
                if let LocalAccess::Current { access: name } = access
                    && let Some(var) = self.get_var(name)
                    && parameters.is_empty()
                {
                    return Ok(Exp::Var(var));
                }

                // 2. others via handler
                let item = handler.get_item_from_access_path(access)?;
                match item {
                    ItemAccessResult::Definition { rc } => {
                        if parameters.is_empty() {
                            Ok(Exp::DefinedConstant(rc.clone()))
                        } else {
                            Err(format!(
                                "Defined constant {} cannot be applied with parameters",
                                rc.name.as_str()
                            )
                            .into())
                        }
                    }
                    ItemAccessResult::Inductive { ind_defs } => {
                        let parameters: Vec<Exp> = parameters
                            .iter()
                            .map(|e| self.elab_exp_rec(e, handler))
                            .collect::<Result<_, _>>()?;
                        Ok(Exp::IndType {
                            indspec: ind_defs.clone(),
                            parameters,
                        })
                    }
                    ItemAccessResult::InductiveCtor {
                        ind_defs,
                        ctor_index,
                    } => {
                        let parameters: Vec<Exp> = parameters
                            .iter()
                            .map(|e| self.elab_exp_rec(e, handler))
                            .collect::<Result<_, _>>()?;
                        Ok(Exp::IndCtor {
                            indspec: ind_defs,
                            parameters: parameters,
                            idx: ctor_index,
                        })
                    }
                    ItemAccessResult::Record {
                        ind_defs,
                        field_names,
                    } => todo!(),
                    ItemAccessResult::Expression { exp } => {
                        if parameters.is_empty() {
                            Ok(exp.clone())
                        } else {
                            Err(format!(
                                "Module parameter {} cannot be applied with parameters",
                                exp
                            )
                            .into())
                        }
                    }
                }
            }
            SExp::MathMacro { .. } | SExp::NamedMacro { .. } => todo!(),
            SExp::Where { exp, clauses } => {
                // elaborate clauses, register name
                // then subst var to defconst in exp

                let mut where_def_rcs_substmap: Vec<(Var, Exp)> = vec![];
                for (name, ty, body) in clauses {
                    let ty = self.elab_exp_rec(ty, handler)?;
                    let body = self.elab_exp_rec(body, handler)?;
                    let def_cst = DefinedConstant {
                        name: format!("<where {}>", name.as_str()),
                        ty,
                        body,
                    };
                    let def_rc = Rc::new(def_cst);
                    let name: Var = Var::new(name.as_str());
                    where_def_rcs_substmap.push((name, Exp::DefinedConstant(def_rc)));
                }

                let exp_elab = self.elab_exp_rec(exp, handler)?;

                Ok(exp_subst_map(&exp_elab, &where_def_rcs_substmap))
            }
            SExp::WithProofs { exp, proofs } => {
                let exp_elab = self.elab_exp_rec(exp, handler)?;
                let mut proof_goals: Vec<ProveGoal> = vec![];
                for proof in proofs {
                    let GoalProof {
                        extended_ctx,
                        goal,
                        proofby: proof_term,
                    } = proof;

                    let extended_ctx_elab =
                        self.elab_telescope_bind_in_decl(extended_ctx, handler)?;

                    let goal_elab = self.elab_exp_rec(goal, handler)?;
                    let proof_term_elab = self.elab_proof_by_rec(proof_term, handler)?;

                    for _ in 0..extended_ctx_elab.len() {
                        self.decl_binds.pop();
                    }

                    proof_goals.push(ProveGoal {
                        extended_ctx: extended_ctx_elab,
                        goal_prop: goal_elab,
                        command: proof_term_elab,
                    });
                }
                Ok(Exp::ProveHere {
                    exp: exp_elab.into(),
                    goals: proof_goals,
                })
            }
            SExp::Sort(sort) => Ok(Exp::Sort(*sort)),
            SExp::Prod { bind, body } | SExp::Lam { bind, body } => {
                let is_prod = matches!(exp, SExp::Prod { .. });
                match bind {
                    Bind::Anonymous { ty } => {
                        let ty_elab = self.elab_exp_rec(ty, handler)?;
                        let body_elab = self.elab_exp_rec(body, handler)?;
                        Ok(if is_prod {
                            Exp::Prod {
                                var: Var::dummy(),
                                ty: Box::new(ty_elab),
                                body: Box::new(body_elab),
                            }
                        } else {
                            Exp::Lam {
                                var: Var::dummy(),
                                ty: Box::new(ty_elab),
                                body: Box::new(body_elab),
                            }
                        })
                    }
                    Bind::Named(right_bind) => {
                        let ty_elab = self.elab_exp_rec(&right_bind.ty, handler)?;

                        let mut telescope: Vec<(Var, Exp)> = vec![];
                        for var in &right_bind.vars {
                            let var: Var = Var::new(var.as_str());
                            telescope.push((var.clone(), ty_elab.clone()));
                            self.push_binded_var(var);
                        }

                        let body_elab = self.elab_exp_rec(body, handler)?;

                        for _ in &right_bind.vars {
                            self.pop_binded_var();
                        }

                        Ok(if is_prod {
                            kernel::utils::assoc_prod(telescope, body_elab)
                        } else {
                            kernel::utils::assoc_lam(telescope, body_elab)
                        })
                    }
                    Bind::Subset { var, ty, predicate } => {
                        let ty_elab = self.elab_exp_rec(ty, handler)?;
                        let var: Var = Var::new(var.as_str());
                        self.push_binded_var(var.clone());
                        let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                        let body_elab = self.elab_exp_rec(body, handler)?;
                        self.pop_binded_var();

                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        let ty_elab = Box::new(Exp::TypeLift {
                            superset: Box::new(ty_elab.clone()),
                            subset: Box::new(subset),
                        });

                        Ok(if is_prod {
                            Exp::Prod {
                                var: var.clone(),
                                ty: ty_elab,
                                body: Box::new(body_elab),
                            }
                        } else {
                            Exp::Lam {
                                var: var.clone(),
                                ty: ty_elab,
                                body: Box::new(body_elab),
                            }
                        })
                    }
                    Bind::SubsetWithProof {
                        var,
                        ty,
                        predicate,
                        proof_var,
                    } => {
                        let ty_elab = self.elab_exp_rec(ty, handler)?;
                        let var: Var = Var::new(var.as_str());
                        self.push_binded_var(var.clone());
                        let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                        let proof: Var = Var::new(proof_var.as_str());
                        self.push_binded_var(proof.clone());
                        let body_elab = self.elab_exp_rec(body, handler)?;
                        self.pop_binded_var();
                        self.pop_binded_var();

                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        let ty_elab = Box::new(Exp::TypeLift {
                            superset: Box::new(ty_elab.clone()),
                            subset: Box::new(subset),
                        });
                        let body_elab = Box::new(Exp::Prod {
                            var: proof,
                            ty: Box::new(predicate_elab),
                            body: Box::new(body_elab),
                        });

                        Ok(if is_prod {
                            Exp::Prod {
                                var: var.clone(),
                                ty: ty_elab,
                                body: body_elab,
                            }
                        } else {
                            Exp::Lam {
                                var: var.clone(),
                                ty: ty_elab,
                                body: body_elab,
                            }
                        })
                    }
                }
            }
            SExp::App {
                func,
                arg,
                piped: _,
            } => {
                let func_elab = self.elab_exp_rec(func, handler)?;
                let arg_elab = self.elab_exp_rec(arg, handler)?;
                Ok(Exp::App {
                    func: Box::new(func_elab),
                    arg: Box::new(arg_elab),
                })
            }
            SExp::Cast { exp, to } => {
                let exp_elab = self.elab_exp_rec(exp, handler)?;
                let to_elab = self.elab_exp_rec(to, handler)?;
                Ok(Exp::Cast {
                    exp: Box::new(exp_elab),
                    to: Box::new(to_elab),
                })
            }
            SExp::IndElim {
                path,
                elim,
                return_type,
                cases,
            } => {
                let indspec_rc = handler.get_inductive_type_from_access_path(path)?;

                let elim_elab = self.elab_exp_rec(elim, handler)?;
                let return_type_elab = self.elab_exp_rec(return_type, handler)?;
                let mut cases_elab: Vec<Exp> = vec![];
                for (ctor_name, case) in cases {
                    let case_elab = self.elab_exp_rec(case, handler)?;
                    let ctor_idx = indspec_rc
                        .ctor_idx_from_name(ctor_name.as_str())
                        .ok_or_else(|| {
                            format!(
                                "Constructor {} not found in inductive type {}",
                                ctor_name.as_str(),
                                indspec_rc.names.0
                            )
                        })?;
                    if ctor_idx != cases_elab.len() {
                        return Err(format!(
                            "Constructor cases are not in order in ind elim for inductive type {}",
                            indspec_rc.names.0
                        )
                        .into());
                    }
                    cases_elab.push(case_elab);
                }

                Ok(Exp::IndElim {
                    indspec: indspec_rc,
                    elim: Box::new(elim_elab),
                    return_type: Box::new(return_type_elab),
                    cases: cases_elab,
                })
            }
            SExp::IndElimPrim {
                path,
                parameters,
                sort,
            } => {
                let indspec_rc = handler.get_inductive_type_from_access_path(path)?;

                let parameters: Vec<Exp> = parameters
                    .iter()
                    .map(|e| self.elab_exp_rec(e, handler))
                    .collect::<Result<_, _>>()?;
                Ok(InductiveTypeSpecs::primitive_recursion(
                    &indspec_rc,
                    parameters,
                    *sort,
                ))
            }

            SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => {
                todo!()
            }

            SExp::RecordFieldAccess { record, field } => {
                let record_elab = self.elab_exp_rec(record, handler)?;
                handler.field_projection(&record_elab, field)
            }

            SExp::ProveLater { prop } => {
                let prop_elab = self.elab_exp_rec(prop, handler)?;
                Ok(Exp::ProveLater {
                    prop: Box::new(prop_elab),
                })
            }
            SExp::PowerSet { set } => {
                let set_elab = self.elab_exp_rec(set, handler)?;
                Ok(Exp::PowerSet {
                    set: Box::new(set_elab),
                })
            }
            SExp::SubSet {
                var,
                set,
                predicate,
            } => {
                let set_elab = self.elab_exp_rec(set, handler)?;
                let var: Var = Var::new(var.as_str());
                self.push_binded_var(var.clone());
                let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                self.pop_binded_var();
                Ok(Exp::SubSet {
                    var: var.clone(),
                    set: Box::new(set_elab),
                    predicate: Box::new(predicate_elab),
                })
            }
            SExp::Pred {
                superset,
                subset,
                element,
            } => {
                let superset_elab = self.elab_exp_rec(superset, handler)?;
                let subset_elab = self.elab_exp_rec(subset, handler)?;
                let element_elab = self.elab_exp_rec(element, handler)?;
                Ok(Exp::Pred {
                    superset: Box::new(superset_elab),
                    subset: Box::new(subset_elab),
                    element: Box::new(element_elab),
                })
            }
            SExp::TypeLift { superset, subset } => {
                let superset_elab = self.elab_exp_rec(superset, handler)?;
                let subset_elab = self.elab_exp_rec(subset, handler)?;
                Ok(Exp::TypeLift {
                    superset: Box::new(superset_elab),
                    subset: Box::new(subset_elab),
                })
            }
            SExp::Equal { left, right } => {
                let left_elab = self.elab_exp_rec(left, handler)?;
                let right_elab = self.elab_exp_rec(right, handler)?;
                Ok(Exp::Equal {
                    left: Box::new(left_elab),
                    right: Box::new(right_elab),
                })
            }
            SExp::Exists { bind } => match bind {
                Bind::Named(_) | Bind::SubsetWithProof { .. } => Err(
                    "Elaboration of named bind or subset with proof in Exists is not implemented"
                        .to_string()
                        .into(),
                ),
                Bind::Anonymous { ty } => {
                    let ty_elab = self.elab_exp_rec(ty, handler)?;
                    Ok(Exp::Exists {
                        set: Box::new(ty_elab),
                    })
                }
                Bind::Subset { var, ty, predicate } => {
                    let subset_as_exp = {
                        let ty_elab = self.elab_exp_rec(ty, handler)?;
                        let var: Var = Var::new(var.as_str());
                        self.push_binded_var(var.clone());
                        let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                        self.pop_binded_var();

                        Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        }
                    };
                    Ok(Exp::Exists {
                        set: Box::new(subset_as_exp),
                    })
                }
            },
            SExp::Take { bind, body } => {
                // elab as SExp::Lam {bind, body}
                let map = SExp::Lam {
                    bind: bind.clone(),
                    body: Box::new(body.as_ref().clone()),
                };
                let map_elab = self.elab_exp_rec(&map, handler)?;
                Ok(Exp::Take {
                    map: Box::new(map_elab),
                })
            }
            SExp::ProofTermRaw(sprove_command_by) => {
                let proof_by_elab = self.elab_proof_by_rec(sprove_command_by, handler)?;
                Ok(Exp::ProofTermRaw {
                    command: Box::new(proof_by_elab),
                })
            }
            SExp::Block(block) => {
                let Block {
                    statements: declarations,
                    result: term,
                } = block;
                let mut term = term.as_ref().clone();
                for decl in declarations.iter().rev() {
                    match decl {
                        Statement::Fix(items) => {
                            for bind in items.iter().rev() {
                                term = SExp::Lam {
                                    bind: Bind::Named(bind.clone()),
                                    body: Box::new(term),
                                };
                            }
                        }
                        Statement::Let { var, ty, body } => {
                            term = SExp::App {
                                func: Box::new(SExp::Lam {
                                    bind: Bind::Named(RightBind {
                                        vars: vec![var.clone()],
                                        ty: Box::new(ty.clone()),
                                    }),
                                    body: Box::new(term),
                                }),
                                arg: Box::new(body.clone()),
                                piped: false,
                            };
                        }
                        Statement::Take { bind } => {
                            term = SExp::Take {
                                bind: bind.clone(),
                                body: Box::new(term),
                            };
                        }
                        Statement::Sufficient { map, map_ty } => {
                            term = SExp::App {
                                func: Box::new(SExp::Cast {
                                    exp: Box::new(map.clone()),
                                    to: Box::new(map_ty.clone()),
                                }),
                                arg: Box::new(term),
                                piped: false,
                            };
                        }
                    }
                }
                self.elab_exp_rec(&term, handler)
            }
        }
    }

    fn elab_proof_by_rec(
        &mut self,
        proof_by: &SProveCommandBy,
        handler: &impl Handler,
    ) -> Result<ProveCommandBy, ErrorKind> {
        let elab = match proof_by {
            SProveCommandBy::Construct { term } => {
                let term_elab = self.elab_exp_rec(term, handler)?;
                ProveCommandBy::Construct(term_elab)
            }
            SProveCommandBy::Exact { term, set } => {
                let term_elab = self.elab_exp_rec(term, handler)?;
                let set_elab = self.elab_exp_rec(set, handler)?;
                ProveCommandBy::ExactElem {
                    elem: term_elab,
                    ty: set_elab,
                }
            }
            SProveCommandBy::SubsetElim {
                superset,
                subset,
                elem,
            } => {
                let superset_elab = self.elab_exp_rec(superset, handler)?;
                let subset_elab = self.elab_exp_rec(subset, handler)?;
                let elem_elab = self.elab_exp_rec(elem, handler)?;
                ProveCommandBy::SubsetElim {
                    superset: superset_elab,
                    subset: subset_elab,
                    elem: elem_elab,
                }
            }
            SProveCommandBy::IdRefl { term } => {
                let term_elab = self.elab_exp_rec(term, handler)?;
                ProveCommandBy::IdRefl { elem: term_elab }
            }
            SProveCommandBy::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
            } => {
                let left_elab = self.elab_exp_rec(left, handler)?;
                let right_elab = self.elab_exp_rec(right, handler)?;
                let var: Var = var.into();
                let ty_elab = self.elab_exp_rec(ty, handler)?;
                let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                ProveCommandBy::IdElim {
                    left: left_elab,
                    right: right_elab,
                    var,
                    ty: ty_elab,
                    predicate: predicate_elab,
                }
            }
            SProveCommandBy::TakeEq {
                func,
                elem,
                domain,
                codomain,
            } => {
                let func_elab = self.elab_exp_rec(func, handler)?;

                let domain_elab = self.elab_exp_rec(domain, handler)?;
                let codomain_elab = self.elab_exp_rec(codomain, handler)?;
                let elem_elab = self.elab_exp_rec(elem, handler)?;
                ProveCommandBy::TakeEq {
                    func: func_elab,
                    domain: domain_elab,
                    codomain: codomain_elab,
                    elem: elem_elab,
                }
            }
            SProveCommandBy::Axiom(_) => {
                todo!("not yet implemented axiom")
            }
        };
        Ok(elab)
    }
}
