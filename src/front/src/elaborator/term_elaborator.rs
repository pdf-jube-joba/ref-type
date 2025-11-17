use std::rc::Rc;

use crate::elaborator::module_manager::ModItemRecord;
use crate::elaborator::{ErrorKind, ItemAccessResult};
use crate::syntax::*;
use kernel::calculus::exp_subst_map;
use kernel::exp::*;
use kernel::inductive::InductiveTypeSpecs;

pub trait Handler {
    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, ErrorKind>;
    fn field_projection(&mut self, e: &Exp, field_name: &Identifier) -> Result<Exp, ErrorKind>;
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
        handler: &mut impl Handler,
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

    pub fn elab_exp(&mut self, exp: &SExp, handler: &mut impl Handler) -> Result<Exp, ErrorKind> {
        assert!(self.binded_vars.is_empty());
        let e = self.elab_exp_rec(exp, handler);
        assert!(self.binded_vars.is_empty());
        e
    }

    pub fn elab_exp_rec(
        &mut self,
        exp: &SExp,
        handler: &mut impl Handler,
    ) -> Result<Exp, ErrorKind> {
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
                                "Defined constant {:?} cannot be applied with parameters",
                                access
                            )
                            .into())
                        }
                    }
                    ItemAccessResult::Inductive {
                        ind_defs,
                        type_name: _,
                        ctor_names: _,
                    } => {
                        let parameters: Vec<Exp> = parameters
                            .iter()
                            .map(|e| self.elab_exp_rec(e, handler))
                            .collect::<Result<_, _>>()?;

                        Ok(Exp::IndType {
                            indspec: ind_defs.clone(),
                            parameters,
                        })
                    }
                    ItemAccessResult::Record(ModItemRecord {
                        type_name: _,
                        fields: _,
                        rc_spec_as_indtype,
                    }) => {
                        let parameters: Vec<Exp> = parameters
                            .iter()
                            .map(|e| self.elab_exp_rec(e, handler))
                            .collect::<Result<_, _>>()?;
                        Ok(Exp::IndType {
                            indspec: rc_spec_as_indtype,
                            parameters,
                        })
                    }
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
            // this includes accessing constructor of the inductive type, accessing field of record type
            // `List[Nat]#nil` or `some_group#unit`
            SExp::AssociatedAccess { base, field } => {
                // 1. if base is local access, try to get constructor (parameter is allowed)
                if let SExp::AccessPath { access, parameters } = base.as_ref() {
                    let item = handler.get_item_from_access_path(access)?;
                    match item {
                        ItemAccessResult::Inductive { ind_defs, type_name, ctor_names  } => {
                            for (idx, ctor_name) in ctor_names.iter().enumerate() {
                                if ctor_name.as_str() == field.as_str() {
                                    let parameters: Vec<Exp> = parameters
                                        .iter()
                                        .map(|e| self.elab_exp_rec(e, handler))
                                        .collect::<Result<_, _>>()?;
                                    return Ok(Exp::IndCtor {
                                        indspec: ind_defs.clone(),
                                        idx,
                                        parameters,
                                    });
                                }
                            }
                            Err(format!(
                                "Constructor {} not found in inductive type {}",
                                field.as_str(),
                                type_name.as_str()
                            ).into())
                        },
                        _ => Err(format!(
                            "Expected inductive constructor or record type in base of associated access {:?}",
                            base
                        )
                        .into()),
                    }
                } else {
                    // 2. otherwise, elab base first, then project field
                    let base_elab = self.elab_exp_rec(base, handler)?;
                    handler.field_projection(&base_elab, field)
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
                    let def_cst = DefinedConstant { ty, body };
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
                        if right_bind.vars.is_empty() {
                            // same as Anonymous
                            let ty_elab = self.elab_exp_rec(&right_bind.ty, handler)?;
                            let body_elab = self.elab_exp_rec(body, handler)?;
                            return Ok(if is_prod {
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
                            });
                        }

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
                let ItemAccessResult::Inductive {
                    type_name: _,
                    ctor_names,
                    ind_defs,
                } = handler.get_item_from_access_path(path)?
                else {
                    return Err(format!(
                        "Expected inductive type in ind elim access path {:?}",
                        path
                    )
                    .into());
                };

                let elim_elab = self.elab_exp_rec(elim, handler)?;
                let return_type_elab = self.elab_exp_rec(return_type, handler)?;
                let mut cases_elab: Vec<Exp> = vec![];
                for (idx, (ctor_name, case)) in cases.iter().enumerate() {
                    let case_elab = self.elab_exp_rec(case, handler)?;
                    if ctor_names[idx].as_str() != ctor_name.as_str() {
                        return Err(format!(
                            "Constructor name mismatch in ind elim: expected {}, found {}",
                            ctor_names[idx].as_str(),
                            ctor_name.as_str()
                        )
                        .into());
                    }
                    cases_elab.push(case_elab);
                }

                Ok(Exp::IndElim {
                    indspec: ind_defs.clone(),
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
                let ItemAccessResult::Inductive {
                    type_name: _,
                    ctor_names: _,
                    ind_defs,
                } = handler.get_item_from_access_path(path)?
                else {
                    return Err(format!(
                        "Expected inductive type in ind elim prim access path {:?}",
                        path
                    )
                    .into());
                };

                let parameters: Vec<Exp> = parameters
                    .iter()
                    .map(|e| self.elab_exp_rec(e, handler))
                    .collect::<Result<_, _>>()?;
                Ok(InductiveTypeSpecs::primitive_recursion(
                    &ind_defs, parameters, *sort,
                ))
            }

            SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => {
                let ItemAccessResult::Record(ModItemRecord {
                    type_name: _,
                    fields: _,
                    rc_spec_as_indtype,
                }) = handler.get_item_from_access_path(access)?
                else {
                    return Err(format!(
                        "Expected record type in record type ctor access path {:?}",
                        access
                    )
                    .into());
                };

                let parameters: Vec<Exp> = parameters
                    .iter()
                    .map(|e| self.elab_exp_rec(e, handler))
                    .collect::<Result<_, _>>()?;
                let mut fields_elab: Vec<(Identifier, Exp)> = vec![];
                for (field_name, field_ty) in fields.iter() {
                    let field_ty_elab = self.elab_exp_rec(field_ty, handler)?;
                    fields_elab.push((field_name.clone(), field_ty_elab));
                }

                Ok(Exp::IndCtor {
                    indspec: rc_spec_as_indtype.clone(),
                    parameters,
                    idx: 0, // record type has only one constructor
                })
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
        handler: &mut impl Handler,
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
