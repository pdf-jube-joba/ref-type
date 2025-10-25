use crate::middle::*;
use kernel::{
    calculus::subst_map,
    checker::Checker,
    exp::{Exp, ProveGoal, Var},
};

pub struct Elaborator {
    global: Vec<MirModule>,
    // self.global[current_mod] is the module being checked
    // self.global[j] for j < current_mod have been checked => usable module
    current_mod: usize,
    // self.global[current_mod].items[current_item] is the item being checked
    // self.global[j].items[l] for (j < current_mod) or (j = current_mod && l < current_item) have been checked => usable item
    current_item: usize,

    // all items that have been checked
    checked_item: Vec<Vec<Item>>,

    // logs
    checker: Checker,
    checker_log: Vec<Checker>,
    log: Vec<String>,
}

pub enum Item {
    Def {
        name: Var,
        ty: Exp,
        body: Exp,
        goals: Vec<ProveGoal>,
    },
    Inductive {
        ind_defs: std::rc::Rc<kernel::inductive::InductiveTypeSpecs>,
    },
}

impl Elaborator {
    pub fn new_global(global: MirGlobal) -> Self {
        Elaborator {
            global: global.mods,
            current_mod: 0,
            current_item: 0,
            checked_item: vec![],
            checker: Checker::default(),
            checker_log: vec![],
            log: vec![],
        }
    }
    fn get_checked_mod(&self, mod_idx: usize) -> Result<&MirModule, String> {
        if self.current_mod <= mod_idx {
            Err(format!("Module {} has not been checked yet", mod_idx))
        } else {
            Ok(&self.global[mod_idx])
        }
    }
    fn get_check_item(&self, mod_idx: usize, item_idx: usize) -> Result<&Item, String> {
        if mod_idx > self.current_mod
            || (mod_idx == self.current_mod && item_idx >= self.current_item)
        {
            Err(format!(
                "Module item {} of module {} has not been checked yet",
                item_idx, mod_idx
            ))
        } else {
            Ok(&self.checked_item[mod_idx][item_idx])
        }
    }
    fn start_chk(&mut self) -> Result<(), String> {
        for i in 0..self.global.len() {
            self.current_mod = i;
            let old_checker = std::mem::replace(&mut self.checker, Checker::default());
            self.checker_log.push(old_checker);
            self.checked_item.push(vec![]);
            let mod_defs = self.global[self.current_mod].clone();

            for item in mod_defs.items {
                match item {
                    MirModuleItem::Definition {
                        name,
                        ty,
                        body,
                        goals,
                    } => {
                        // get elaborated types and body
                        let name = name.clone();
                        let ty = ty.clone();
                        let elab_ty = self.elab_mir(&ty)?;
                        let body = body.clone();
                        let elab_body = self.elab_mir(&body)?;
                        let goals = goals
                            .iter()
                            .map(|g| {
                                let WithGoal {
                                    extend_ctx,
                                    goal_prop,
                                    proof,
                                } = g.clone();

                                let extended_ctx_elab = extend_ctx
                                    .iter()
                                    .map(|(v, ty_mir)| {
                                        let ty_elab = self.elab_mir(ty_mir).unwrap();
                                        (v.clone(), ty_elab)
                                    })
                                    .collect::<Vec<_>>();
                                let goal_prop_elab = self.elab_mir(&goal_prop).unwrap();
                                let proof_elab = self.elab_mir(&proof).unwrap();

                                ProveGoal {
                                    extended_ctx: extended_ctx_elab.into(),
                                    goal_prop: goal_prop_elab,
                                    proof_term: proof_elab,
                                }
                            })
                            .collect::<Vec<_>>();

                        // check
                        match self.checker.check(
                            &Exp::ProveHere {
                                exp: Box::new(elab_body.clone()),
                                goals: goals.clone(),
                            },
                            &elab_ty,
                        ) {
                            Ok(_) => {
                                self.checked_item.last_mut().unwrap().push(Item::Def {
                                    name,
                                    ty: elab_ty,
                                    body: elab_body,
                                    goals,
                                });
                            }
                            Err(_) => {
                                return Err(format!(
                                    "Definition {} does not have the expected type",
                                    name
                                ));
                            }
                        }
                    }
                    MirModuleItem::Inductive { ind_defs } => {
                        let InductiveTypeSpecs {
                            parameters,
                            indices,
                            sort,
                            constructors,
                        } = ind_defs;

                        let parameteres_elab = parameters
                            .iter()
                            .map(|(v, ty_mir)| {
                                let ty_elab = self.elab_mir(ty_mir).unwrap();
                                (v.clone(), ty_elab)
                            })
                            .collect::<Vec<_>>();
                        let indices_elab = indices
                            .iter()
                            .map(|(v, ty_mir)| {
                                let ty_elab = self.elab_mir(ty_mir).unwrap();
                                (v.clone(), ty_elab)
                            })
                            .collect::<Vec<_>>();
                        let constructors_elab = constructors
                            .iter()
                            .map(|(params_ctor, ret_types)| {
                                let params_ctor_elab = params_ctor
                                    .iter()
                                    .map(|param_ctor| match param_ctor {
                                        ParamCtor::StrictPositive(param_list, ret_types) => {
                                            let param_list_elab = param_list
                                                .iter()
                                                .map(|(v, ty_mir)| {
                                                    let ty_elab = self.elab_mir(ty_mir).unwrap();
                                                    (v.clone(), ty_elab)
                                                })
                                                .collect::<Vec<_>>();
                                            let ret_types_elab = ret_types
                                                .iter()
                                                .map(|ty_mir| self.elab_mir(ty_mir).unwrap())
                                                .collect::<Vec<_>>();
                                            kernel::inductive::CtorBinder::StrictPositive {
                                                binders: param_list_elab,
                                                self_indices: ret_types_elab,
                                            }
                                        }
                                        ParamCtor::Simple(v, ty_mir) => {
                                            let ty_elab = self.elab_mir(ty_mir).unwrap();
                                            kernel::inductive::CtorBinder::Simple((
                                                v.clone(),
                                                ty_elab,
                                            ))
                                        }
                                    })
                                    .collect::<Vec<_>>();
                                let ret_types_elab = ret_types
                                    .iter()
                                    .map(|ty_mir| self.elab_mir(ty_mir).unwrap())
                                    .collect::<Vec<_>>();
                                kernel::inductive::CtorType {
                                    telescope: params_ctor_elab,
                                    indices: ret_types_elab,
                                }
                            })
                            .collect::<Vec<_>>();

                        let res = self.checker.chk_indspec(
                            parameteres_elab,
                            indices_elab,
                            sort,
                            constructors_elab,
                        )?;

                        self.checked_item.last_mut().unwrap().push(Item::Inductive {
                            ind_defs: std::rc::Rc::new(res),
                        });
                    }
                }
            }
        }
        Ok(())
    }
    fn history_str(&mut self, s: String) {
        self.log.push(s);
    }
    pub fn elab_mid_mod_instantiated(
        &mut self,
        mid: &MirModuleInstantiated,
    ) -> Result<Vec<(Var, Exp)>, String> {
        let mod_def = self.get_checked_mod(mid.module)?.clone();

        let mut subst_map_acum = vec![];

        for ((param_name, param_ty_mir), arg_mir) in
            mod_def.parameters.iter().zip(mid.arguments.iter())
        {
            let param_ty_elab = self.elab_mir(param_ty_mir)?;
            let param_ty_subst = subst_map(&param_ty_elab, subst_map_acum.as_slice());
            let arg_elab = self.elab_mir(arg_mir)?;
            match self.checker.check(&arg_elab, &param_ty_subst) {
                Ok(()) => {}
                Err(()) => {
                    return Err(format!(
                        "Module instantiation argument type mismatch for parameter {}",
                        param_name
                    ));
                }
            }
            subst_map_acum.push((param_name.clone(), arg_elab));
        }

        Ok(subst_map_acum)
    }
    pub fn elab_mir(&mut self, mir: &Mir) -> Result<Exp, String> {
        match mir {
            Mir::ModAccessDef { path, name } => {
                todo!()
            }
            Mir::IndType { path, idx } => {
                let exp = Exp::IndType {
                    indty: todo!(),
                    parameters: todo!(),
                };
                todo!()
            }
            _ => todo!(),
        }
    }
    pub fn elab_block(&mut self, block: &MirBlock) -> Result<Exp, String> {
        todo!()
    }
}
