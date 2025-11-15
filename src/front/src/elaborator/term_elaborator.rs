use std::collections::HashMap;
use std::rc::Rc;

use crate::elaborator::module_manager::ModuleInstantiated;
use crate::elaborator::{ErrorKind, GlobalEnvironment, ItemAccessResult};
use crate::syntax::*;
use kernel::calculus::exp_subst_map;
use kernel::exp::*;
use kernel::inductive::InductiveTypeSpecs;

// local scope during elaboration
#[derive(Debug, Clone)]
pub struct LocalScope {
    // for find binded variables inside term
    // lambda abstraction variables, product, subset,
    // after any call of elab_exp outside the elab_exp, this should be cleared
    binded_vars: Vec<Var>,
    // for find decl levels
    decl_binds: Vec<Var>,
    imported_modules: HashMap<Identifier, ModuleInstantiated>,
}

// elaborations
impl GlobalEnvironment {
    pub fn elab_exp(&mut self, sexp: &SExp) -> Result<Exp, ErrorKind> {
        assert!(self.local_scope.binded_vars.is_empty());
        let e = self.elab_exp_rec(sexp);
        assert!(self.local_scope.binded_vars.is_empty());
        e
    }

    fn push_binded_var(&mut self, var: Var) {
        self.local_scope.binded_vars.push(var);
    }
    fn pop_binded_var(&mut self) {
        self.local_scope.binded_vars.pop();
    }
    // this modifies bind_vars (length += number of vars)
    // after call, caller should pop the binded vars
    fn elab_telescope_rec(&mut self, v: &[RightBind]) -> Result<Vec<(Var, Exp)>, ErrorKind> {
        let mut result = vec![];
        for RightBind { vars, ty } in v.iter() {
            let ty_elab = self.elab_exp(ty)?;
            for var in vars {
                let var = Var::new(var.as_str());
                result.push((var.clone(), ty_elab.clone()));
                self.push_binded_var(var);
            }
        }
        Ok(result)
    }

    fn elab_exp_rec(&mut self, sexp: &SExp) -> Result<Exp, ErrorKind> {
        match sexp {
            SExp::AccessPath(local_access) => {
                // 1. find from local_scope ... if LocalAccess::Current and has Some() get_var

                if let LocalAccess::Current { access, parameters } = local_access {
                    // 1. binded in local scope
                    if let Some(v) = self.local_scope.get_var(access) {
                        if parameters.is_empty() {
                            return Ok(Exp::Var(v));
                        } else {
                            return Err(ErrorKind::Msg(format!(
                                "Variable {} cannot be applied with parameters",
                                access.as_str()
                            )));
                        }
                    }
                }

                // 2. find from modules
                let item = self.convert_access_path_to_items(local_access)?;

                match item {
                    ItemAccessResult::Definition { rc } => {
                        if local_access.parameters().is_empty() {
                            return Ok(Exp::DefinedConstant(rc.clone()));
                        } else {
                            return Err(ErrorKind::Msg(format!(
                                "Defined constant {} cannot be applied with parameters",
                                rc.name.as_str()
                            )));
                        }
                    }
                    ItemAccessResult::Inductive { ind_defs } => {
                        let parameters: Vec<Exp> = local_access
                            .parameters()
                            .iter()
                            .map(|e| self.elab_exp_rec(e))
                            .collect::<Result<_, _>>()?;
                        return Ok(Exp::IndType {
                            indspec: ind_defs.clone(),
                            parameters,
                        });
                    }
                    ItemAccessResult::Parameter { exp } => {
                        if local_access.parameters().is_empty() {
                            return Ok(exp.clone());
                        } else {
                            return Err(ErrorKind::Msg(format!(
                                "Module parameter {} cannot be applied with parameters",
                                exp
                            )));
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
                    let ty = self.elab_exp_rec(ty)?;
                    let body = self.elab_exp_rec(body)?;
                    let def_cst = DefinedConstant {
                        name: format!("<where {}>", name.as_str()),
                        ty,
                        body,
                    };
                    let def_rc = Rc::new(def_cst);
                    let name: Var = Var::new(name.as_str());
                    where_def_rcs_substmap.push((name, Exp::DefinedConstant(def_rc)));
                }

                let exp_elab = self.elab_exp_rec(exp)?;

                Ok(exp_subst_map(&exp_elab, &where_def_rcs_substmap))
            }
            SExp::WithProofs { exp, proofs } => {
                let exp_elab = self.elab_exp_rec(exp)?;
                let mut proof_goals: Vec<ProveGoal> = vec![];
                for proof in proofs {
                    let GoalProof {
                        extended_ctx,
                        goal,
                        proofby: proof_term,
                    } = proof;
                    let extended_ctx_elab = self.elab_telescope_rec(extended_ctx)?;
                    //
                    let goal_elab = self.elab_exp_rec(goal)?;
                    let proof_term_elab = self.elab_proof_by_rec(proof_term)?;

                    for _ in 0..extended_ctx_elab.len() {
                        self.pop_binded_var();
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
                let is_prod = matches!(sexp, SExp::Prod { .. });
                match bind {
                    Bind::Anonymous { ty } => {
                        let ty_elab = self.elab_exp_rec(ty)?;
                        let body_elab = self.elab_exp_rec(body)?;
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
                        let ty_elab = self.elab_exp_rec(&right_bind.ty)?;

                        let mut telescope: Vec<(Var, Exp)> = vec![];
                        for var in &right_bind.vars {
                            let var: Var = Var::new(var.as_str());
                            telescope.push((var.clone(), ty_elab.clone()));
                            self.push_binded_var(var);
                        }

                        let body_elab = self.elab_exp_rec(body)?;

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
                        let ty_elab = self.elab_exp_rec(ty)?;
                        let var: Var = Var::new(var.as_str());
                        self.push_binded_var(var.clone());
                        let predicate_elab = self.elab_exp_rec(predicate)?;
                        let body_elab = self.elab_exp_rec(body)?;
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
                        let ty_elab = self.elab_exp_rec(ty)?;
                        let var: Var = Var::new(var.as_str());
                        self.push_binded_var(var.clone());
                        let predicate_elab = self.elab_exp_rec(predicate)?;
                        let proof: Var = Var::new(proof_var.as_str());
                        self.push_binded_var(proof.clone());
                        let body_elab = self.elab_exp_rec(body)?;
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
                let func_elab = self.elab_exp_rec(func)?;
                let arg_elab = self.elab_exp_rec(arg)?;
                Ok(Exp::App {
                    func: Box::new(func_elab),
                    arg: Box::new(arg_elab),
                })
            }
            SExp::Cast { exp, to } => {
                let exp_elab = self.elab_exp_rec(exp)?;
                let to_elab = self.elab_exp_rec(to)?;
                Ok(Exp::Cast {
                    exp: Box::new(exp_elab),
                    to: Box::new(to_elab),
                })
            }
            SExp::IndCtor { path, ctor_name } => {
                let item = self.convert_access_path_to_items(path)?;

                let ItemAccessResult::Inductive { ind_defs: indspec } = item else {
                    return Err(ErrorKind::Msg(format!(
                        "Expected inductive type in path {:?}",
                        path
                    )));
                };

                let parameters: Vec<Exp> = path
                    .parameters()
                    .iter()
                    .map(|e| self.elab_exp_rec(e))
                    .collect::<Result<_, _>>()?;

                let idx = indspec
                    .ctor_idx_from_name(ctor_name.as_str())
                    .ok_or_else(|| {
                        ErrorKind::Msg(format!(
                            "Constructor {} not found in inductive type {}",
                            ctor_name.as_str(),
                            indspec.names.0
                        ))
                    })?;

                Ok(Exp::IndCtor {
                    indspec,
                    parameters,
                    idx,
                })
            }
            SExp::IndElim {
                path,
                elim,
                return_type,
                cases,
            } => {
                let item = self.convert_access_path_to_items(path)?;
                let ItemAccessResult::Inductive { ind_defs: indspec } = item else {
                    return Err(ErrorKind::Msg(format!(
                        "Expected inductive type in path {:?}",
                        path
                    )));
                };
                let elim_elab = self.elab_exp_rec(elim)?;
                let return_type_elab = self.elab_exp_rec(return_type)?;
                let mut cases_elab: Vec<Exp> = vec![];
                for (ctor_name, case) in cases {
                    let case_elab = self.elab_exp_rec(case)?;
                    let ctor_idx =
                        indspec
                            .ctor_idx_from_name(ctor_name.as_str())
                            .ok_or_else(|| {
                                ErrorKind::Msg(format!(
                                    "Constructor {} not found in inductive type {}",
                                    ctor_name.as_str(),
                                    indspec.names.0
                                ))
                            })?;
                    if ctor_idx != cases_elab.len() {
                        return Err(ErrorKind::Msg(format!(
                            "Constructor cases are not in order in ind elim for inductive type {}",
                            indspec.names.0
                        )));
                    }
                    cases_elab.push(case_elab);
                }
                Ok(Exp::IndElim {
                    indspec,
                    elim: Box::new(elim_elab),
                    return_type: Box::new(return_type_elab),
                    cases: cases_elab,
                })
            }
            SExp::IndElimPrim { path, sort } => {
                let item = self.convert_access_path_to_items(path)?;
                let ItemAccessResult::Inductive { ind_defs: indspec } = item else {
                    return Err(ErrorKind::Msg(format!(
                        "Expected inductive type in path {:?}",
                        path
                    )));
                };
                let parameters: Vec<Exp> = path
                    .parameters()
                    .iter()
                    .map(|e| self.elab_exp_rec(e))
                    .collect::<Result<_, _>>()?;
                Ok(InductiveTypeSpecs::primitive_recursion(
                    &indspec, parameters, *sort,
                ))
            }
            SExp::ProveLater { prop: term } => {
                let term_elab = self.elab_exp_rec(term)?;
                Ok(Exp::ProveLater {
                    prop: Box::new(term_elab),
                })
            }
            SExp::PowerSet { set } => {
                let set_elab = self.elab_exp_rec(set)?;
                Ok(Exp::PowerSet {
                    set: Box::new(set_elab),
                })
            }
            SExp::SubSet {
                var,
                set,
                predicate,
            } => {
                let set_elab = self.elab_exp_rec(set)?;
                let var: Var = Var::new(var.as_str());
                self.push_binded_var(var.clone());
                let predicate_elab = self.elab_exp_rec(predicate)?;
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
                let superset_elab = self.elab_exp_rec(superset)?;
                let subset_elab = self.elab_exp_rec(subset)?;
                let element_elab = self.elab_exp_rec(element)?;
                Ok(Exp::Pred {
                    superset: Box::new(superset_elab),
                    subset: Box::new(subset_elab),
                    element: Box::new(element_elab),
                })
            }
            SExp::TypeLift { superset, subset } => {
                let superset_elab = self.elab_exp_rec(superset)?;
                let subset_elab = self.elab_exp_rec(subset)?;
                Ok(Exp::TypeLift {
                    superset: Box::new(superset_elab),
                    subset: Box::new(subset_elab),
                })
            }
            SExp::Equal { left, right } => {
                let left_elab = self.elab_exp_rec(left)?;
                let right_elab = self.elab_exp_rec(right)?;
                Ok(Exp::Equal {
                    left: Box::new(left_elab),
                    right: Box::new(right_elab),
                })
            }
            // this is non emptyness of type ... Exp::Exists { set: Box<Exp> }
            SExp::Exists { bind } => match bind {
                Bind::Named(_) | Bind::SubsetWithProof { .. } => Err(ErrorKind::Msg(
                    "Elaboration of named bind or subset with proof in Exists is not implemented"
                        .to_string(),
                )),
                Bind::Anonymous { ty } => {
                    let ty_elab = self.elab_exp_rec(ty)?;
                    Ok(Exp::Exists {
                        set: Box::new(ty_elab),
                    })
                }
                Bind::Subset { var, ty, predicate } => {
                    let subset_as_exp = {
                        let ty_elab = self.elab_exp_rec(ty)?;
                        let var: Var = Var::new(var.as_str());
                        self.push_binded_var(var.clone());
                        let predicate_elab = self.elab_exp_rec(predicate)?;
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
                    body: body.clone(),
                };
                let map_elab = self.elab_exp_rec(&map)?;
                Ok(Exp::Take {
                    map: Box::new(map_elab),
                })
            }
            SExp::ProofTermRaw(proof_by) => {
                let proof_by_elab = self.elab_proof_by_rec(proof_by)?;
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
                self.elab_exp_rec(&term)
            }
        }
    }
    fn elab_proof_by_rec(
        &mut self,
        proof_by: &SProveCommandBy,
    ) -> Result<ProveCommandBy, ErrorKind> {
        let elab = match proof_by {
            SProveCommandBy::Construct { term } => {
                let term_elab = self.elab_exp_rec(term)?;
                ProveCommandBy::Construct(term_elab)
            }
            SProveCommandBy::Exact { term, set } => {
                let term_elab = self.elab_exp_rec(term)?;
                let set_elab = self.elab_exp_rec(set)?;
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
                let superset_elab = self.elab_exp_rec(superset)?;
                let subset_elab = self.elab_exp_rec(subset)?;
                let elem_elab = self.elab_exp_rec(elem)?;
                ProveCommandBy::SubsetElim {
                    superset: superset_elab,
                    subset: subset_elab,
                    elem: elem_elab,
                }
            }
            SProveCommandBy::IdRefl { term } => {
                let term_elab = self.elab_exp_rec(term)?;
                ProveCommandBy::IdRefl { elem: term_elab }
            }
            SProveCommandBy::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
            } => {
                let left_elab = self.elab_exp_rec(left)?;
                let right_elab = self.elab_exp_rec(right)?;
                let var: Var = var.into();
                let mut bind_var = vec![];
                bind_var.push(var.clone());
                let ty_elab = self.elab_exp_rec(ty)?;
                let predicate_elab = self.elab_exp_rec(predicate)?;
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
                let func_elab = self.elab_exp_rec(func)?;
                let domain_elab = self.elab_exp_rec(domain)?;
                let codomain_elab = self.elab_exp_rec(codomain)?;
                let elem_elab = self.elab_exp_rec(elem)?;
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
