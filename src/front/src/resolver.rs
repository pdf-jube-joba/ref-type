use std::collections::HashMap;

use crate::{syntax::*, utils};
use kernel::{calculus::contains_as_freevar, exp::*, inductive::CtorBinder};

pub struct Resolver {
    pub module_stack: Vec<ModuleResolved>,
    pub current_local_state: LocalState,
    pub old_local_states: Vec<LocalState>,
}

impl Default for Resolver {
    fn default() -> Self {
        Self {
            module_stack: vec![],
            current_local_state: LocalState {
                checker: kernel::checker::Checker::default(),
                imports: HashMap::new(),
                items: vec![],
            },
            old_local_states: vec![],
        }
    }
}

pub struct LocalState {
    checker: kernel::checker::Checker,
    imports: HashMap<Var, ModuleRealized>,
    items: Vec<Item>,
    // mathmacros, usermacro ... implement after
}

pub struct ModuleResolved {
    pub name: Var,
    pub parameters: Vec<(Var, Exp)>,
    pub items: Vec<Item>,
}

pub enum Item {
    Definition {
        name: kernel::exp::Var,
        ty: Exp,
        body: Exp,
    },
    Inductive {
        name: kernel::exp::Var,
        ctor_names: Vec<kernel::exp::Var>,
        ind_defs: std::rc::Rc<kernel::inductive::InductiveTypeSpecs>,
    },
}

pub struct ModuleRealized {
    pub name: Var,
    pub arguments: Vec<(Var, Exp)>,
    pub items: Vec<Item>,
}

impl Resolver {
    pub fn new_module(&mut self, module: &Module) -> Result<(), String> {
        let Module {
            name,
            parameters,
            declarations,
        } = module;

        let mut parameteres_elab = vec![];

        for (var, ty) in parameters {
            let var = Var::new(var.0.as_str());
            let ty = self.elab_exp(ty, vec![])?;
            self.current_local_state
                .checker
                .push(var.clone(), ty.clone())
                .map_err(|_| format!("Error in module parameter elaboration: {ty}"))?;
            parameteres_elab.push((var, ty));
        }

        let module = ModuleResolved {
            name: Var::new(name.0.as_str()),
            parameters: parameteres_elab,
            items: Vec::new(),
        };

        self.module_stack.push(module);

        for item in declarations {
            match item {
                ModuleItem::Definition { var, ty, body } => {
                    let var = Var::new(var.0.as_str());
                    let ty = self.elab_exp(ty, vec![])?;
                    let body = self.elab_exp(body, vec![])?;

                    self.current_local_state
                        .checker
                        .check(&ty, &body)
                        .map_err(|_| format!("Error in definition elaboration: {var} : {ty}"))?;

                    let item_elab = Item::Definition {
                        name: var,
                        ty,
                        body,
                    };

                    self.current_local_state.items.push(item_elab);
                }
                ModuleItem::Inductive { ind_defs } => {
                    let SInductiveTypeSpecs {
                        type_name,
                        parameter,
                        indices,
                        sort,
                        constructors,
                    } = ind_defs;

                    let type_name = Var::new(type_name.0.as_str());

                    let parameter_elab: Vec<(Var, Exp)> = parameter
                        .iter()
                        .map(|(var, ty)| {
                            Ok((
                                Var::new(var.0.as_str()),
                                self.elab_exp(ty, vec![])?, // Handle error properly
                            ))
                        })
                        .collect::<Result<Vec<(Var, Exp)>, String>>()?;

                    let indices_elab: Vec<(Var, Exp)> = indices
                        .iter()
                        .map(|(var, ty)| {
                            Ok((
                                Var::new(var.0.as_str()),
                                self.elab_exp(ty, vec![])?, // Handle error properly
                            ))
                        })
                        .collect::<Result<Vec<(Var, Exp)>, String>>()?;

                    let mut ctor_names = vec![];
                    let mut constructors_elab = vec![];

                    for (ctor_name, ctor_args) in constructors {
                        let ctor_name_var = Var::new(ctor_name.0.as_str());
                        ctor_names.push(ctor_name_var);

                        let ctor_type_elab = self.elab_exp(ctor_args, vec![type_name.clone()])?;

                        let (telescope, tails) = kernel::utils::decompose_prod(ctor_type_elab);

                        let mut ctor_binders = vec![];
                        for (v, e) in telescope {
                            // may be problematic
                            if contains_as_freevar(&e, &type_name) {
                                // strict positive case
                                let (inner_binders, inner_tail) = kernel::utils::decompose_prod(e);
                                for (iv, it) in inner_binders.iter() {
                                    if contains_as_freevar(&it, &type_name) {
                                        return Err(format!(
                                            "Constructor binder type {it} contains inductive type name {type_name} in non-strictly positive position"
                                        ));
                                    }
                                }
                                let (head, tail) = kernel::utils::decompose_app(inner_tail);
                                for tail_elm in tail.iter() {
                                    if contains_as_freevar(tail_elm, &type_name) {
                                        return Err(format!(
                                            "Constructor binder type tail {tail_elm} contains inductive type name {type_name} in non-strictly positive position"
                                        ));
                                    }
                                }
                                ctor_binders.push(CtorBinder::StrictPositive {
                                    binders: inner_binders,
                                    self_indices: tail,
                                });
                            } else {
                                // simple case
                                ctor_binders.push(CtorBinder::Simple((v, e)));
                            }
                        }

                        let (head, tail) = kernel::utils::decompose_app(tails);
                        let Exp::Var(head_var) = head else {
                            return Err(format!("Constructor type head {head} is not a Var"));
                        };
                        if !head_var.is_eq_ptr(&type_name) {
                            return Err(format!(
                                "Constructor type head {head_var} does not match inductive type name {type_name}"
                            ));
                        }
                        for tail_elm in tail.iter() {
                            if contains_as_freevar(tail_elm, &type_name) {
                                return Err(format!(
                                    "Constructor type tail {tail_elm} contains inductive type name {type_name}"
                                ));
                            }
                        }

                        constructors_elab.push(kernel::inductive::CtorType {
                            telescope: ctor_binders,
                            indices: tail,
                        });
                    }

                    let indspecs_elab = self
                        .current_local_state
                        .checker
                        .chk_indspec(parameter_elab, indices_elab, *sort, constructors_elab)
                        .map_err(|e| format!("Error in inductive type elaboration: {e}"))?;

                    let item_elab = Item::Inductive {
                        name: type_name,
                        ctor_names,
                        ind_defs: std::rc::Rc::new(indspecs_elab),
                    };
                    self.current_local_state.items.push(item_elab);
                }
                ModuleItem::ChildModule { module } => todo!(),
                ModuleItem::Import {
                    instantiated_module,
                    import_name,
                } => todo!(),
                ModuleItem::MathMacro { before, after } => todo!(),
                ModuleItem::UserMacro {
                    name,
                    before,
                    after,
                } => todo!(),
            }
        }
        Ok(())
    }
    pub fn get_resolved_module(&mut self) {
        todo!()
    }
    pub fn elab_exp(&mut self, sexp: &SExp, bind_var: Vec<Var>) -> Result<Exp, String> {
        todo!()
    }
}
