use std::rc::Rc;

use crate::elaborator::ItemAccessResult;
use crate::syntax::*;
use kernel::calculus::{exp_contains_as_freevar, exp_subst_map};
use kernel::exp::*;
use kernel::inductive::InductiveTypeSpecs;

pub trait Handler {
    fn get_item_from_access_path(
        &mut self,
        access_path: &LocalAccess,
    ) -> Result<ItemAccessResult, String>;
    fn field_projection(&mut self, e: &Exp, field_name: &Identifier) -> Result<Exp, String>;
    fn infer(&mut self, local_ctx: &Context, e: &Exp) -> Result<Exp, String>;
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
    // Types of local variables known to the elaborator. Module variables are
    // supplied by the handler and therefore do not appear here.
    typing_binds: Context,
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
            typing_binds: vec![],
        }
    }

    pub fn push_decl_var(&mut self, var: Var) {
        self.decl_binds.push(var);
    }

    pub fn push_typed_decl_var(&mut self, var: Var, ty: Exp) {
        self.decl_binds.push(var.clone());
        self.typing_binds.push((var, ty));
    }

    // does not pop decl_binds
    pub fn elab_telescope_bind_in_decl(
        &mut self,
        binds: &[RightBind],
        handler: &mut impl Handler,
    ) -> Result<Vec<(Var, Exp)>, String> {
        let mut result = vec![];
        for RightBind { vars, ty } in binds.iter() {
            let ty_elab = self.elab_exp(ty, handler)?;
            for var in vars {
                let var = Var::new(var.as_str());
                result.push((var.clone(), ty_elab.clone()));
                self.push_typed_decl_var(var, ty_elab.clone());
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

    fn push_binded_var(&mut self, var: Var, ty: Exp) {
        self.binded_vars.push(var.clone());
        self.typing_binds.push((var, ty));
    }
    fn pop_binded_var(&mut self) {
        self.binded_vars.pop();
        self.typing_binds.pop();
    }

    pub fn elab_exp(&mut self, exp: &SExp, handler: &mut impl Handler) -> Result<Exp, String> {
        assert!(self.binded_vars.is_empty());
        let e = self.elab_exp_rec(exp, handler);
        assert!(e.is_err() || self.binded_vars.is_empty());
        e
    }

    fn elab_take_parts(
        &mut self,
        bind: &Bind,
        body: &SExp,
        handler: &mut impl Handler,
    ) -> Result<(Exp, Exp, Exp), String> {
        match bind {
            Bind::Named(right_bind) => {
                if right_bind.vars.len() != 1 {
                    return Err("\\take currently expects exactly one named variable".into());
                }

                let var = Var::new(right_bind.vars[0].as_str());
                let domain = self.elab_exp_rec(&right_bind.ty, handler)?;
                self.push_binded_var(var.clone(), domain.clone());
                let map_body = self.elab_exp_rec(body, handler)?;
                self.pop_binded_var();
                let map = Exp::Lam {
                    var: var.clone(),
                    ty: Box::new(domain.clone()),
                    body: Box::new(map_body),
                };
                let map_ty = handler.infer(&self.typing_binds, &map)?;
                let Exp::Prod { body: codomain, .. } = map_ty else {
                    return Err("failed to infer a product type for \\take map".into());
                };
                if exp_contains_as_freevar(&codomain, &var) {
                    return Err("\\take map must have a non-dependent codomain".into());
                }
                Ok((domain, map, *codomain))
            }
            Bind::Subset { var, ty, predicate } => {
                let carrier = self.elab_exp_rec(ty, handler)?;
                let var = Var::new(var.as_str());
                self.push_binded_var(var.clone(), carrier.clone());
                let predicate = self.elab_exp_rec(predicate, handler)?;
                self.pop_binded_var();

                let subset = Exp::SubSet {
                    var: var.clone(),
                    set: Box::new(carrier.clone()),
                    predicate: Box::new(predicate),
                };
                let domain = Exp::TypeLift {
                    superset: Box::new(carrier),
                    subset: Box::new(subset),
                };
                self.push_binded_var(var.clone(), domain.clone());
                let map_body = self.elab_exp_rec(body, handler)?;
                self.pop_binded_var();
                let map = Exp::Lam {
                    var: var.clone(),
                    ty: Box::new(domain.clone()),
                    body: Box::new(map_body),
                };
                let map_ty = handler.infer(&self.typing_binds, &map)?;
                let Exp::Prod { body: codomain, .. } = map_ty else {
                    return Err("failed to infer a product type for \\take map".into());
                };
                if exp_contains_as_freevar(&codomain, &var) {
                    return Err("\\take map must have a non-dependent codomain".into());
                }
                Ok((domain, map, *codomain))
            }
            Bind::SubsetWithProof { .. } => {
                Err("\\take with proof bind is not supported by kernel Take(X,T,f)".into())
            }
        }
    }

    fn elab_exp_rec(&mut self, exp: &SExp, handler: &mut impl Handler) -> Result<Exp, String> {
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
                    ItemAccessResult::Definition(ModItemDefinition { body, .. }) => {
                        if parameters.is_empty() {
                            Ok(Exp::DefinedConstant(body.clone()))
                        } else {
                            Err(format!(
                                "Defined constant {:?} cannot be applied with parameters",
                                access
                            ))
                        }
                    }
                    ItemAccessResult::Inductive(ModItemInductive {
                        ind_defs,
                        type_name: _,
                        ctor_names: _,
                    }) => {
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
                    ItemAccessResult::Expression(exp) => {
                        if parameters.is_empty() {
                            Ok(exp.clone())
                        } else {
                            Err("Module parameter cannot be applied with parameters".to_string())
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
                        ItemAccessResult::Inductive(ModItemInductive {
                            ind_defs,
                            type_name,
                            ctor_names,
                        }) => {
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
                            ))
                        }
                        _ => Err(format!(
                            "Expected inductive constructor or record type in base of associated access {:?}",
                            base
                        )),
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
            SExp::Sort(sort) => Ok(Exp::Sort(*sort)),
            SExp::Prod { bind, body } | SExp::Lam { bind, body } => {
                let is_prod = matches!(exp, SExp::Prod { .. });
                match bind {
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
                            self.push_binded_var(var, ty_elab.clone());
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
                        self.push_binded_var(var.clone(), ty_elab.clone());
                        let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                        self.pop_binded_var();

                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        let refined_ty = Exp::TypeLift {
                            superset: Box::new(ty_elab.clone()),
                            subset: Box::new(subset),
                        };
                        self.push_binded_var(var.clone(), refined_ty.clone());
                        let body_elab = self.elab_exp_rec(body, handler)?;
                        self.pop_binded_var();

                        Ok(if is_prod {
                            Exp::Prod {
                                var: var.clone(),
                                ty: Box::new(refined_ty),
                                body: Box::new(body_elab),
                            }
                        } else {
                            Exp::Lam {
                                var: var.clone(),
                                ty: Box::new(refined_ty),
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
                        self.push_binded_var(var.clone(), ty_elab.clone());
                        let predicate_elab = self.elab_exp_rec(predicate, handler)?;
                        self.pop_binded_var();

                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };
                        let refined_ty = Exp::TypeLift {
                            superset: Box::new(ty_elab),
                            subset: Box::new(subset),
                        };
                        self.push_binded_var(var.clone(), refined_ty.clone());
                        let proof: Var = Var::new(proof_var.as_str());
                        self.push_binded_var(proof.clone(), predicate_elab.clone());
                        let body_elab = self.elab_exp_rec(body, handler)?;
                        self.pop_binded_var();
                        self.pop_binded_var();
                        let body_elab = Box::new(Exp::Prod {
                            var: proof,
                            ty: Box::new(predicate_elab),
                            body: Box::new(body_elab),
                        });

                        Ok(if is_prod {
                            Exp::Prod {
                                var: var.clone(),
                                ty: Box::new(refined_ty),
                                body: body_elab,
                            }
                        } else {
                            Exp::Lam {
                                var: var.clone(),
                                ty: Box::new(refined_ty),
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
            SExp::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => {
                let superset_elab = self.elab_exp_rec(superset, handler)?;
                let subset_elab = self.elab_exp_rec(subset, handler)?;
                let element_elab = self.elab_exp_rec(element, handler)?;
                let proof_elab = self.elab_exp_rec(proof, handler)?;
                Ok(Exp::SubsetIntro {
                    superset: Box::new(superset_elab),
                    subset: Box::new(subset_elab),
                    element: Box::new(element_elab),
                    proof: Box::new(proof_elab),
                })
            }
            SExp::IndElim {
                path,
                elim,
                return_type,
                cases,
            } => {
                let ItemAccessResult::Inductive(ModItemInductive {
                    type_name: _,
                    ctor_names,
                    ind_defs,
                }) = handler.get_item_from_access_path(path)?
                else {
                    return Err(format!(
                        "Expected inductive type in ind elim access path {:?}",
                        path
                    ));
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
                        ));
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
                let ItemAccessResult::Inductive(ModItemInductive {
                    type_name: _,
                    ctor_names: _,
                    ind_defs,
                }) = handler.get_item_from_access_path(path)?
                else {
                    return Err(format!(
                        "Expected inductive type in ind elim prim access path {:?}",
                        path
                    ));
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
                    rc_spec_as_indtype,
                }) = handler.get_item_from_access_path(access)?
                else {
                    return Err(format!(
                        "Expected record type in record type ctor access path {:?}",
                        access
                    ));
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
                self.push_binded_var(var.clone(), set_elab.clone());
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
                Bind::Named(rightbind) => {
                    if rightbind.vars.len() >= 2 {
                        return Err(
                            "Elaboration of multiple named binds in Exists is not implemented"
                                .to_string(),
                        );
                    }
                    let ty_elab = self.elab_exp_rec(&rightbind.ty, handler)?;
                    Ok(Exp::Exists {
                        set: Box::new(ty_elab),
                    })
                }
                Bind::SubsetWithProof { .. } => Err(
                    "Elaboration of named bind or subset with proof in Exists is not implemented"
                        .to_string(),
                ),
                Bind::Subset { var, ty, predicate } => {
                    let subset_as_exp = {
                        let ty_elab = self.elab_exp_rec(ty, handler)?;
                        let var: Var = Var::new(var.as_str());
                        self.push_binded_var(var.clone(), ty_elab.clone());
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
            SExp::TakeSet {
                bind,
                body,
                existence,
                uniqueness,
            } => {
                let (domain, map, codomain) = self.elab_take_parts(bind, body, handler)?;
                Ok(Exp::TakeSet {
                    domain: Box::new(domain),
                    codomain: Box::new(codomain),
                    map: Box::new(map),
                    existence: Box::new(self.elab_exp_rec(existence, handler)?),
                    uniqueness: Box::new(self.elab_exp_rec(uniqueness, handler)?),
                })
            }
            SExp::TakeProp {
                bind,
                body,
                existence,
            } => {
                let (domain, map, proposition) = self.elab_take_parts(bind, body, handler)?;
                Ok(Exp::TakeProp {
                    domain: Box::new(domain),
                    proposition: Box::new(proposition),
                    map: Box::new(map),
                    existence: Box::new(self.elab_exp_rec(existence, handler)?),
                })
            }
            SExp::ExistsIntro { element, set } => Ok(Exp::ExistsIntro {
                element: Box::new(self.elab_exp_rec(element, handler)?),
                set: Box::new(self.elab_exp_rec(set, handler)?),
            }),
            SExp::SubsetElim {
                element,
                subset,
                superset,
            } => Ok(Exp::SubsetElim {
                element: Box::new(self.elab_exp_rec(element, handler)?),
                subset: Box::new(self.elab_exp_rec(subset, handler)?),
                superset: Box::new(self.elab_exp_rec(superset, handler)?),
            }),
            SExp::IdRefl { element } => Ok(Exp::IdRefl {
                element: Box::new(self.elab_exp_rec(element, handler)?),
            }),
            SExp::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
                base,
                equality,
            } => {
                let left = Box::new(self.elab_exp_rec(left, handler)?);
                let right = Box::new(self.elab_exp_rec(right, handler)?);
                let ty = Box::new(self.elab_exp_rec(ty, handler)?);
                let var = Var::new(var.as_str());
                self.push_binded_var(var.clone(), ty.as_ref().clone());
                let predicate = Box::new(self.elab_exp_rec(predicate, handler)?);
                self.pop_binded_var();
                let base = Box::new(self.elab_exp_rec(base, handler)?);
                let equality = Box::new(self.elab_exp_rec(equality, handler)?);
                Ok(Exp::IdElim {
                    left,
                    right,
                    var,
                    ty,
                    predicate,
                    base,
                    equality,
                })
            }
            SExp::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
            } => Ok(Exp::TakeEq {
                func: Box::new(self.elab_exp_rec(func, handler)?),
                domain: Box::new(self.elab_exp_rec(domain, handler)?),
                codomain: Box::new(self.elab_exp_rec(codomain, handler)?),
                element: Box::new(self.elab_exp_rec(element, handler)?),
                existence: Box::new(self.elab_exp_rec(existence, handler)?),
                uniqueness: Box::new(self.elab_exp_rec(uniqueness, handler)?),
            }),
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
                        Statement::TakeSet {
                            bind,
                            existence,
                            uniqueness,
                        } => {
                            term = SExp::TakeSet {
                                bind: bind.clone(),
                                body: Box::new(term),
                                existence: Box::new(existence.clone()),
                                uniqueness: Box::new(uniqueness.clone()),
                            };
                        }
                        Statement::TakeProp { bind, existence } => {
                            term = SExp::TakeProp {
                                bind: bind.clone(),
                                body: Box::new(term),
                                existence: Box::new(existence.clone()),
                            };
                        }
                        Statement::Sufficient { map, map_ty: _ } => {
                            term = SExp::App {
                                func: Box::new(map.clone()),
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
}
