use std::collections::HashMap;

use crate::{syntax::*, utils};
use kernel::{
    calculus::{contains_as_freevar, is_alpha_eq, subst_map},
    exp::*,
    inductive::{CtorBinder, CtorType, InductiveTypeSpecs},
};

pub struct Resolver {
    pub module_stack: Vec<ModuleResolved>, // templates
    pub current_local_state: LocalState,
    pub old_local_states: Vec<LocalState>,
}

pub struct LocalState {
    checker: kernel::checker::Checker,
    imports: HashMap<Var, usize>, // index to realized
    realized: Vec<ModuleRealized>,
    items: Vec<Item>,
    // mathmacros, usermacro ... implement after
}

// for templates
#[derive(Debug, Clone)]
pub struct ModuleResolved {
    pub name: Var,
    pub parameters: Vec<(Var, Exp)>, // v: ty
    pub items: Vec<Item>,
}

impl ModuleResolved {
    // assume all aguments are provided, and type checked
    fn realize(&self, arguments: Vec<Exp>) -> ModuleRealized {
        assert!(self.parameters.len() == arguments.len());
        let arguments_substmap = self
            .parameters
            .iter()
            .map(|(v, _)| v.clone())
            .zip(arguments.iter().cloned())
            .collect::<Vec<(Var, Exp)>>();
        let items_substed = self
            .items
            .iter()
            .map(|it| match it {
                Item::Definition { name, ty, body } => {
                    let ty_substed = subst_map(ty, &arguments_substmap);
                    let body_substed = subst_map(body, &arguments_substmap);
                    Item::Definition {
                        name: name.clone(),
                        ty: ty_substed,
                        body: body_substed,
                    }
                }
                Item::Inductive {
                    name,
                    ctor_names,
                    ind_defs,
                } => {
                    let InductiveTypeSpecs {
                        parameters,
                        indices,
                        sort,
                        constructors,
                    } = ind_defs.as_ref().clone();

                    let parameters_substed: Vec<(Var, Exp)> = parameters
                        .iter()
                        .map(|(v, e)| (v.clone(), subst_map(e, &arguments_substmap)))
                        .collect();

                    let indices_substed: Vec<(Var, Exp)> = indices
                        .iter()
                        .map(|(v, e)| (v.clone(), subst_map(e, &arguments_substmap)))
                        .collect();

                    let constructors_substed: Vec<kernel::inductive::CtorType> = constructors
                        .iter()
                        .map(|ctor| {
                            let CtorType { telescope, indices } = ctor;
                            let telescope_substed: Vec<CtorBinder> = telescope
                                .iter()
                                .map(|binder| match binder {
                                    CtorBinder::Simple((v, e)) => CtorBinder::Simple((
                                        v.clone(),
                                        subst_map(e, &arguments_substmap),
                                    )),
                                    CtorBinder::StrictPositive {
                                        binders,
                                        self_indices,
                                    } => {
                                        let binders_substed: Vec<(Var, Exp)> = binders
                                            .iter()
                                            .map(|(bv, be)| {
                                                (bv.clone(), subst_map(be, &arguments_substmap))
                                            })
                                            .collect();
                                        let self_indices_substed: Vec<Exp> = self_indices
                                            .iter()
                                            .map(|e| subst_map(e, &arguments_substmap))
                                            .collect();
                                        CtorBinder::StrictPositive {
                                            binders: binders_substed,
                                            self_indices: self_indices_substed,
                                        }
                                    }
                                })
                                .collect();
                            let indices_substed: Vec<Exp> = indices
                                .iter()
                                .map(|e| subst_map(e, &arguments_substmap))
                                .collect();
                            CtorType {
                                telescope: telescope_substed,
                                indices: indices_substed,
                            }
                        })
                        .collect();

                    let ind_defs_substed = InductiveTypeSpecs {
                        parameters: parameters_substed,
                        indices: indices_substed,
                        sort,
                        constructors: constructors_substed,
                    };

                    Item::Inductive {
                        name: name.clone(),
                        ctor_names: ctor_names.clone(),
                        ind_defs: std::rc::Rc::new(ind_defs_substed),
                    }
                }
            })
            .collect();

        ModuleRealized {
            name: self.name.clone(),
            arguments,
            items: items_substed,
        }
    }
}

#[derive(Debug, Clone)]
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
    pub arguments: Vec<Exp>, // v := arg
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
    pub fn get_resolved_module(
        &mut self,
        mod_instantiated: &ModuleInstantiated,
    ) -> Result<usize, String> {
        let ModuleInstantiated {
            module_name,
            arguments,
        } = mod_instantiated;

        let Some(mod_templates) = self
            .module_stack
            .iter()
            .find(|mod_templates| mod_templates.name.name() == module_name.0.as_str())
        else {
            return Err(format!(
                "Module {} not found",
                mod_instantiated.module_name.0.as_str()
            ));
        };
        let mod_templates = mod_templates.clone();

        // check arguments
        if mod_templates.parameters.len() != arguments.len() {
            return Err(format!(
                "Module {} expects {} arguments, but {} were provided",
                mod_instantiated.module_name.0.as_str(),
                mod_templates.parameters.len(),
                arguments.len()
            ));
        }

        let mut arguments_elab = vec![];
        for i in 0..arguments.len() {
            let (name, arg) = &arguments[i];
            if name.0.as_str() != mod_templates.parameters[i].0.name() {
                return Err(format!(
                    "Argument name {} does not match parameter name {}",
                    name.0.as_str(),
                    mod_templates.parameters[i].0.name()
                ));
            }
            arguments_elab.push(self.elab_exp(arg, vec![])?);
        }

        // case: already realized
        if let Some(idx) = self
            .current_local_state
            .realized
            .iter()
            .position(|mod_realized| {
                mod_realized.name.name() == mod_instantiated.module_name.0.as_str()
                    && mod_realized
                        .arguments
                        .iter()
                        .zip(arguments_elab.iter())
                        .all(|(a, b)| is_alpha_eq(a, b))
            })
        {
            return Ok(idx);
        }

        // case: not yet realized
        let mut subst_stack = vec![];

        for i in 0..mod_templates.parameters.len() {
            let (var, ty) = &mod_templates.parameters[i];
            let ty_substed = subst_map(&ty, &subst_stack);
            let arg_elab = &arguments_elab[i];

            self.current_local_state
                .checker
                .check(arg_elab, &ty_substed)
                .map_err(|_| {
                    format!(
                        "Error in module instantiation: argument {arg_elab} does not match parameter type {ty}"
                    )
                })?;

            subst_stack.push((var.clone(), arg_elab.clone()));
        }

        self.current_local_state
            .realized
            .push(mod_templates.realize(arguments_elab));

        Ok(self.current_local_state.realized.len() - 1)
    }
    pub fn elab_exp(&mut self, sexp: &SExp, bind_var: Vec<Var>) -> Result<Exp, String> {
        todo!()
    }
}
