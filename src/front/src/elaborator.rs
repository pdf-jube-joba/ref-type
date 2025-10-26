use crate::middle::*;
use kernel::{
    calculus::{is_alpha_eq, subst_map},
    checker::Checker,
    exp::{Exp, ProveGoal, Var},
};

pub struct Elaborator {
    global: Vec<(Var, Vec<(Var, Exp)>, Vec<Item>)>, // all modules

    // all paths that have been checked => access by "origin"
    checked_path: Vec<RealizedPath>,

    // logs
    checker: Checker,
    checker_log: Vec<Checker>,
    log: Vec<String>,
}

// store realized path
pub struct RealizedPath {
    origin_modname: Var,     // idx to self.global
    subst_mapping: Vec<Exp>, // substitution map for parameters
    items: Vec<Item>,        // items in the module
}

#[derive(Debug, Clone)]
pub enum Item {
    Def {
        ty: Exp,
        body: Exp,
        goals: Vec<ProveGoal>,
    },
    Inductive {
        ind_defs: std::rc::Rc<kernel::inductive::InductiveTypeSpecs>,
    },
}

impl Elaborator {
    pub fn new_global() -> Self {
        Elaborator {
            global: vec![],
            checked_path: vec![],
            checker: Checker::default(),
            checker_log: vec![],
            log: vec![],
        }
    }
    pub fn add_mod(&mut self, module: MirModule) -> Result<(), String> {
        let old_checker = std::mem::take(&mut self.checker);
        self.checker_log.push(old_checker);

        let MirModule {
            name,
            parameters,
            items,
        } = module;

        let mut parameters_elab = vec![];

        for (v, ty) in parameters {
            let ty_elab = self.elab_mir(&ty)?;
            let res = self.checker.push(v.clone(), ty_elab.clone());
            if res.is_err() {
                return Err(format!("Parameter {} has invalid type", v));
            }
            parameters_elab.push((v.clone(), ty_elab));
        }

        let mut items_elab = vec![];

        for item in items {
            match item {
                MirModuleItem::Definition {
                    name,
                    ty,
                    body,
                    goals,
                } => {
                    todo!()
                }
                MirModuleItem::Inductive { name, ind_defs } => {
                    todo!()
                }
            }
        }

        self.global.push((name, parameters_elab, items_elab));
        todo!();
    }
    fn get_mod_from_name(&self, name: &Var) -> Option<(Var, Vec<(Var, Exp)>, Vec<Item>)> {
        for (idx, (mod_name, _, _)) in self.global.iter().enumerate() {
            if mod_name.is_eq_ptr(name) {
                return Some(self.global[idx].clone());
            }
        }
        None
    }
    fn history_str(&mut self, s: String) {
        self.log.push(s);
    }
    fn access_path(
        &self,
        name: &Var,
        subst_mapping: Vec<Exp>,
    ) -> Result<&RealizedPath, String> {
        for rp in &self.checked_path {
            if rp.origin_modname.is_eq_ptr(name)
                && subst_mapping.len() == rp.subst_mapping.len()
                && subst_mapping
                    .iter()
                    .zip(rp.subst_mapping.iter())
                    .all(|(e1, e2)| is_alpha_eq(e1, e2))
            {
                return Ok(rp);
            }
        }
        Err(format!(
            "No realized path found for origin {} with given substitution",
            name
        ))
    }
    fn elab_mid_mod_instantiated(
        &mut self,
        mid: &MirModuleInstantiated,
    ) -> Result<usize, String> {
        let MirModuleInstantiated {
            mod_name,
            arguments,
        } = mid;
        let Some((_, mod_parameters, items)) = self.get_mod_from_name(mod_name) else {
            return Err(format!("Module {} not found", mod_name));
        };

        let mut subst_map_acum = vec![];

        for ((param_name, param_ty), arg_mir) in mod_parameters.iter().zip(arguments.iter()) {
            let param_ty_subst = subst_map(&param_ty, subst_map_acum.as_slice());
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

        let items = items
            .iter()
            .map(|it| match it {
                Item::Def { ty, body, goals } => Item::Def {
                    ty: subst_map(ty, subst_map_acum.as_slice()),
                    body: subst_map(body, subst_map_acum.as_slice()),
                    goals: goals
                        .iter()
                        .map(|g| ProveGoal {
                            extended_ctx: g
                                .extended_ctx
                                .vec()
                                .iter()
                                .map(|(v, ty)| {
                                    (v.clone(), subst_map(ty, subst_map_acum.as_slice()))
                                })
                                .collect::<Vec<_>>()
                                .into(),
                            goal_prop: subst_map(&g.goal_prop, subst_map_acum.as_slice()),
                            proof_term: subst_map(&g.proof_term, subst_map_acum.as_slice()),
                        })
                        .collect(),
                },
                Item::Inductive { ind_defs } => {
                    let kernel::inductive::InductiveTypeSpecs {
                        parameters,
                        indices,
                        sort,
                        constructors,
                    } = ind_defs.as_ref().clone();
                    Item::Inductive {
                        ind_defs: std::rc::Rc::new(kernel::inductive::InductiveTypeSpecs {
                            parameters: parameters
                                .iter()
                                .map(|(v, ty)| {
                                    (v.clone(), subst_map(ty, subst_map_acum.as_slice()))
                                })
                                .collect(),
                            indices: indices
                                .iter()
                                .map(|(v, ty)| {
                                    (v.clone(), subst_map(ty, subst_map_acum.as_slice()))
                                })
                                .collect(),
                            sort: sort.clone(),
                            constructors: constructors
                                .iter()
                                .map(|ctor| {
                                    let kernel::inductive::CtorType { telescope, indices } =
                                        ctor.clone();
                                    kernel::inductive::CtorType {
                                        telescope: telescope
                                            .iter()
                                            .map(|binder| match binder {
                                                kernel::inductive::CtorBinder::StrictPositive {
                                                    binders,
                                                    self_indices,
                                                } => {
                                                    kernel::inductive::CtorBinder::StrictPositive {
                                                        binders: binders
                                                            .iter()
                                                            .map(|(v, ty)| {
                                                                (
                                                                    v.clone(),
                                                                    subst_map(
                                                                        ty,
                                                                        subst_map_acum.as_slice(),
                                                                    ),
                                                                )
                                                            })
                                                            .collect(),
                                                        self_indices: self_indices
                                                            .iter()
                                                            .map(|ty| {
                                                                subst_map(
                                                                    ty,
                                                                    subst_map_acum.as_slice(),
                                                                )
                                                            })
                                                            .collect(),
                                                    }
                                                }
                                                kernel::inductive::CtorBinder::Simple((v, ty)) => {
                                                    kernel::inductive::CtorBinder::Simple((
                                                        v.clone(),
                                                        subst_map(ty, subst_map_acum.as_slice()),
                                                    ))
                                                }
                                            })
                                            .collect(),
                                        indices: indices
                                            .iter()
                                            .map(|ty| subst_map(ty, subst_map_acum.as_slice()))
                                            .collect(),
                                    }
                                })
                                .collect(),
                        }),
                    }
                }
            })
            .collect();

        self.checked_path.push(RealizedPath {
            origin_modname: mod_name.clone(),
            subst_mapping: subst_map_acum.iter().map(|(_, e)| e.clone()).collect(),
            items,
        });

        Ok(self.checked_path.len() - 1)
    }
    pub fn elab_mir(&mut self, mir: &Mir) -> Result<Exp, String> {
        match mir {
            Mir::ModAccessDef { path, name } => {
                let MirModuleInstantiated {
                    mod_name: module,
                    arguments,
                } = path;

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
