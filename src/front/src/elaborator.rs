use crate::middle::*;
use kernel::{
    calculus::subst_map,
    checker::Checker,
    exp::{Exp, ProveGoal, Var},
};

pub struct Elaborator {
    global: Vec<MirModule>,
    current_mod: usize, // self.global[current_mod] is the module being checked
    checker: Checker,
    checker_log: Vec<Checker>,
    log: Vec<String>,
}

impl Elaborator {
    pub fn new_global(global: MirGlobal) -> Self {
        Elaborator {
            global: global.mods,
            current_mod: 0,
            checker: Checker::default(),
            checker_log: vec![],
            log: vec![],
        }
    }
    fn new_chk(&mut self) {
        let old_checker = std::mem::replace(&mut self.checker, Checker::default());
        self.checker_log.push(old_checker);
    }
    fn get_checked_mod(&self, mod_idx: usize) -> Result<&MirModule, String> {
        if self.current_mod <= mod_idx {
            Err(format!("Module {} has not been checked yet", mod_idx))
        } else {
            Ok(&self.global[mod_idx])
        }
    }
    fn start_chk(&mut self) -> Result<(), String> {
        for i in 0..self.global.len() {
            self.current_mod = i;
            self.new_chk();
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
                                exp: Box::new(elab_body),
                                goals,
                            },
                            &elab_ty,
                        ) {
                            Ok(_) => {}
                            Err(_) => {
                                return Err(format!(
                                    "Definition {} does not have the expected type",
                                    name
                                ));
                            }
                        }
                    }
                    MirModuleItem::Inductive { ind_defs } => {}
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
                self.elab_mid_mod_instantiated(path)?;
                todo!()
            }
            _ => todo!(),
        }
    }
    pub fn elab_block(&mut self, block: &MirBlock) -> Result<Exp, String> {
        todo!()
    }
}
