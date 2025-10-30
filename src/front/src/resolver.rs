use crate::syntax::*;
use either::Either;
use kernel::{
    calculus::{contains_as_freevar, is_alpha_eq, subst_map},
    exp::*,
    inductive::{CtorBinder, CtorType, InductiveTypeSpecs},
};

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

// do type checking
pub struct GlobalEnvironment {
    resolver: Resolver,
    elaborator: Elaborator,
    logger: Logger,
}

impl Default for GlobalEnvironment {
    fn default() -> Self {
        GlobalEnvironment {
            resolver: Resolver {
                module_templates: vec![],
                realized_modules: vec![],
            },
            elaborator: Elaborator {
                parameters: vec![],
                items: vec![],
            },
            logger: Logger { log: vec![] },
        }
    }
}

impl GlobalEnvironment {
    pub fn new_module(&mut self, module: &Module) -> Result<(), String> {
        let Module {
            name,
            parameters,
            declarations,
        } = module;

        let parameteres_elab =
            self.elaborator
                .elab_telescope(&mut self.resolver, &mut self.logger, parameters)?;

        // sort check parameter's ty
        {
            for (_, ty) in parameteres_elab.iter() {
                let der = kernel::derivation::infer_sort(&self.elaborator.parameters, ty);
                self.logger.log_derivation(der.clone());
                if !der.node().unwrap().is_success() {
                    return Err(format!(
                        "Parameter type checking failed: type {ty} is not a valid type",
                    ));
                }
            }
        }

        let mut items_elab = vec![];
        for item in declarations {
            let item_elab =
                self.elaborator
                    .elab_item(&mut self.resolver, &mut self.logger, item)?;
            self.elaborator.items.push(item_elab.clone()); // to resolve later items
            items_elab.push(item_elab);
        }

        // chek well-formedness of items
        {
            for item in items_elab.iter() {
                match item {
                    Item::Definition { name, ty, body } => {
                        let der = kernel::derivation::check(&parameteres_elab, body, ty);
                        self.logger.log_derivation(der.clone());
                        if !der.node().unwrap().is_success() {
                            return Err(format!(
                                "Definition {} type checking failed: body {} does not have type {}",
                                name.name(),
                                body,
                                ty
                            ));
                        }
                    }
                    Item::Inductive {
                        name,
                        ctor_names: _,
                        ind_defs,
                    } => {
                        let (ders, res) =
                            kernel::inductive::acceptable_typespecs(&parameteres_elab, ind_defs);
                        for der in ders {
                            self.logger.log_derivation(der);
                        }
                        if let Err(err) = res {
                            return Err(format!(
                                "Inductive type {} definition is not acceptable: {}",
                                name.name(),
                                err
                            ));
                        }
                    }
                }
            }
        }

        self.resolver.module_templates.push(ModuleResolved {
            name: Var::new(name.0.as_str()),
            parameters: parameteres_elab,
            items: items_elab,
        });

        Ok(())
    }
    pub fn history(&self) -> Vec<Either<Derivation, String>> {
        self.logger.log.clone()
    }
}

// contains checked module templates and realized modules
pub struct Resolver {
    module_templates: Vec<ModuleResolved>,
    realized_modules: Vec<ModuleRealized>,
}

impl Resolver {
    pub fn get_module_template(&self, name: &Var) -> Option<ModuleResolved> {
        for module in self.module_templates.iter().rev() {
            if module.name.is_eq_ptr(name) {
                return Some(module.clone());
            }
        }
        None
    }
    pub fn realize_module(&mut self, name: &Var, arguments: Vec<Exp>) -> Result<usize, String> {
        let Some(module_template) = self.get_module_template(name) else {
            return Err(format!("Module template {} not found", name.name()));
        };

        if module_template.parameters.len() != arguments.len() {
            return Err(format!(
                "Module {} expects {} arguments, but {} were provided",
                name.name(),
                module_template.parameters.len(),
                arguments.len()
            ));
        }

        let module_realized = module_template.realize(arguments);

        self.realized_modules.push(module_realized);

        Ok(self.realized_modules.len() - 1)
    }
}

// elaborator does not type check
pub struct Elaborator {
    parameters: Vec<(Var, Exp)>,
    items: Vec<Item>, // previously elaborated items
}

impl Elaborator {
    fn elab_item(
        &mut self,
        resolver: &mut Resolver,
        logger: &mut Logger,
        item: &crate::syntax::ModuleItem,
    ) -> Result<Item, String> {
        match item {
            ModuleItem::Definition { var, ty, body } => {
                let var: Var = var.into();
                let ty_elab = self.elab_exp(resolver, logger, ty, &[])?;
                let body_elab = self.elab_exp(resolver, logger, body, &[])?;
                Ok(Item::Definition {
                    name: var,
                    ty: ty_elab,
                    body: body_elab,
                })
            }
            ModuleItem::Inductive {
                type_name,
                parameter,
                arity,
                constructors,
            } => {
                let type_name: Var = type_name.into();

                // elaborate parameters
                let parameter_elab = self.elab_telescope(resolver, logger, parameter)?;

                // elaborate arity and decompose to (x[0]: A[0]) -> ... -> (x[n]: A[n]) -> Sort
                let arity_elab = self.elab_exp(resolver, logger, arity, &[])?;
                let (indices_elab, sort) = kernel::utils::decompose_prod(arity_elab);
                let Exp::Sort(sort) = sort else {
                    return Err(format!(
                        "Inductive type arity {arity:?} does not end with a Sort"
                    ));
                };

                // elaborate constructors
                let mut ctor_names = vec![];
                let mut ctor_type_elabs = vec![];

                for (ctor_name, ctor_args) in constructors {
                    let ctor_name_var: Var = ctor_name.into();
                    ctor_names.push(ctor_name_var.clone());

                    // elaborate constructor type and decompose to telescope and tails
                    let ctor_type_elab =
                        self.elab_exp(resolver, logger, ctor_args, &[type_name.clone()])?;
                    let (telescope, tails) = kernel::utils::decompose_prod(ctor_type_elab);

                    let mut ctor_binders = vec![];
                    for (v, e) in telescope {
                        if contains_as_freevar(&e, &type_name) {
                            // strict positive case
                            let (inner_binders, inner_tail) = kernel::utils::decompose_prod(e);
                            for (_, it) in inner_binders.iter() {
                                if contains_as_freevar(it, &type_name) {
                                    return Err(format!(
                                        "Constructor binder type {it} contains inductive type name {type_name} in non-strictly positive position"
                                    ));
                                }
                            }
                            let (head, tail) = kernel::utils::decompose_app(inner_tail);
                            if !matches!(head, Exp::Var(head_var) if head_var.is_eq_ptr(&type_name))
                            {
                                return Err(format!(
                                    "Constructor binder type head does not match inductive type name {type_name}"
                                ));
                            }

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
                    if !matches!(head, Exp::Var(head_var) if head_var.is_eq_ptr(&type_name)) {
                        return Err(format!(
                            "Constructor type head does not match inductive type name {type_name}"
                        ));
                    }

                    for tail_elm in tail.iter() {
                        if contains_as_freevar(tail_elm, &type_name) {
                            return Err(format!(
                                "Constructor type tail {tail_elm} contains inductive type name {type_name}"
                            ));
                        }
                    }

                    ctor_type_elabs.push(kernel::inductive::CtorType {
                        telescope: ctor_binders,
                        indices: tail,
                    });
                }

                let indtype_specs = InductiveTypeSpecs {
                    parameters: parameter_elab,
                    indices: indices_elab,
                    sort,
                    constructors: ctor_type_elabs,
                };

                Ok(Item::Inductive {
                    name: type_name,
                    ctor_names,
                    ind_defs: std::rc::Rc::new(indtype_specs),
                })
            }
            ModuleItem::MathMacro { .. } | ModuleItem::UserMacro { .. } => todo!(),
        }
    }
    fn elab_exp(
        &mut self,
        resolver: &mut Resolver,
        logger: &mut Logger,
        sexp: &crate::syntax::SExp,
        reference_var: &[Var],
    ) -> Result<Exp, String> {
        self.elab_exp_rec(resolver, logger, sexp, reference_var, vec![])
    }
    fn elab_telescope(
        &mut self,
        resolver: &mut Resolver,
        logger: &mut Logger,
        telescope: &Vec<(Identifier, crate::syntax::SExp)>,
    ) -> Result<Vec<(Var, Exp)>, String> {
        let mut result = vec![];
        let mut reference_var = vec![];
        for (v, ty) in telescope {
            let v: Var = v.into();
            let ty_elab = self.elab_exp(resolver, logger, ty, &reference_var)?;
            reference_var.push(v.clone());
            result.push((v, ty_elab));
        }
        Ok(result)
    }
    fn elab_exp_rec(
        &mut self,
        resolver: &mut Resolver,
        logger: &mut Logger,
        sexp: &crate::syntax::SExp,
        reference_var: &[Var],
        bind_var: Vec<(Var, Exp)>,
    ) -> Result<Exp, String> {
        match sexp {
            SExp::Identifier(ident) => {
                // check bound variables from bind_var
                for (v, _) in bind_var.iter().rev() {
                    if v.name() == ident.0.as_str() {
                        return Ok(Exp::Var(v.clone()));
                    }
                }

                // check from previously elaborated items
                for item in self.items.iter().rev() {
                    match item {
                        Item::Definition {
                            name: def_name,
                            ty: _,
                            body,
                        } => {
                            if def_name.name() == ident.0.as_str() {
                                return Ok(body.clone());
                            }
                        }
                        Item::Inductive {
                            name: ind_name,
                            ctor_names: _,
                            ind_defs,
                        } => {
                            if ind_name.name() == ident.0.as_str() {
                                return Ok(Exp::IndType {
                                    indty: ind_defs.clone(),
                                    parameters: vec![],
                                });
                            }
                        }
                    }
                }

                // check from current parameters
                for (v, ty) in self.parameters.iter().rev() {
                    if v.name() == ident.0.as_str() {
                        return Ok(Exp::Var(v.clone()));
                    }
                }

                Err(format!("Unbound identifier: {}", ident.0.as_str()))
            }
            _ => todo!(),
        }
    }
}

pub struct Logger {
    log: Vec<Either<Derivation, String>>,
}

impl Logger {
    fn log_derivation(&mut self, der: Derivation) {
        self.log.push(Either::Left(der));
    }
    fn log_message<S>(&mut self, s: S)
    where
        S: Into<String>,
    {
        self.log.push(Either::Right(s.into()));
    }
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
    // items will be substituted accordingly
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

pub struct ModuleRealized {
    pub name: Var,
    pub arguments: Vec<Exp>, // v := arg
    pub items: Vec<Item>,
}

// pub struct Resolver {
//     pub module_stack: Vec<ModuleResolved>, // templates
//     pub current_local_state: LocalState,
//     pub old_local_states: Vec<LocalState>,
// }

// impl Default for Resolver {
//     fn default() -> Self {
//         Resolver {
//             module_stack: vec![],
//             current_local_state: LocalState {
//                 parameters: vec![],
//                 realized: vec![],
//                 items: vec![],
//                 log: vec![],
//             },
//             old_local_states: vec![],
//         }
//     }
// }

// impl Resolver {
//     pub fn history(&self) -> Vec<Either<Derivation, String>> {
//         self.current_local_state.log.clone()
//     }
//     fn get_module_templates(&self, name: &Identifier) -> Option<ModuleResolved> {
//         for module in self.module_stack.iter().rev() {
//             if module.name.name() == name.0.as_str() {
//                 return Some(module.clone());
//             }
//         }
//         None
//     }
//     fn log<S>(&mut self, s: S)
//     where
//         S: Into<String>,
//     {
//         self.current_local_state.log.push(Either::Right(s.into()));
//     }
// }

// pub struct LocalState {
//     parameters: Vec<(Var, Exp)>,
//     realized: Vec<ModuleRealized>,
//     items: Vec<Item>,
//     log: Vec<Either<Derivation, String>>,
//     // mathmacros, usermacro ... implement after
// }

// impl LocalState {
//     fn push_parameter(&mut self, var: Var, ty: Exp) -> Result<(), String> {
//         // check well-sortedness
//         let der = kernel::derivation::infer_sort(&self.parameters, &ty);
//         self.log.push(Either::Left(der.clone()));
//         if !der.node().unwrap().is_success() {
//             return Err(format!(
//                 "Parameter type checking failed: type {} is not a valid type",
//                 ty
//             ));
//         }
//         self.parameters.push((var, ty));
//         Ok(())
//     }
//     fn push_item(&mut self, item: Item) {
//         self.items.push(item);
//     }
//     fn resolve_var_in_param(&self, ident: &Identifier) -> Option<Exp> {
//         for (var, _) in self.parameters.iter().rev() {
//             if var.name() == ident.0.as_str() {
//                 return Some(Exp::Var(var.clone()));
//             }
//         }
//         None
//     }
//     fn resolve_item(&self, ident: &Identifier) -> Option<Item> {
//         for item in self.items.iter().rev() {
//             match item {
//                 Item::Definition { name, .. } | Item::Inductive { name, .. } => {
//                     if name.name() == ident.0.as_str() {
//                         return Some(item.clone());
//                     }
//                 }
//             }
//         }
//         None
//     }
//     fn check(&mut self, term: &Exp, ty: &Exp) -> Result<(), String> {
//         // run a derivation check with the current global context and log the derivation
//         let der = kernel::derivation::check(&self.parameters, term, ty);
//         self.log.push(Either::Left(der.clone()));
//         if !der.node().unwrap().is_success() {
//             return Err(format!(
//                 "Type checking failed: term {} does not have type {}",
//                 term, ty
//             ));
//         }
//         Ok(())
//     }
//     fn is_realized(&self, module_name: &Identifier, arguments: &[Exp]) -> Option<usize> {
//         for (idx, mod_realized) in self.realized.iter().enumerate() {
//             if mod_realized.name.name() == module_name.0.as_str()
//                 && mod_realized
//                     .arguments
//                     .iter()
//                     .zip(arguments.iter())
//                     .all(|(a, b)| is_alpha_eq(a, b))
//             {
//                 return Some(idx);
//             }
//         }
//         None
//     }
//     // assume well-typedness is already checked
//     fn push_realized(&mut self, module_realized: ModuleRealized) {
//         self.realized.push(module_realized);
//     }
// }

// impl Resolver {
//     pub fn new_module(&mut self, module: &Module) -> Result<(), String> {
//         self.log(format!("Resolving module {}", module.name.0.as_str()));
//         let old_state = std::mem::replace(
//             &mut self.current_local_state,
//             LocalState {
//                 parameters: vec![],
//                 realized: vec![],
//                 items: vec![],
//                 log: vec![],
//             },
//         );
//         self.old_local_states.push(old_state);

//         let Module {
//             name,
//             parameters,
//             declarations,
//         } = module;

//         for (var, ty) in parameters {
//             self.log(format!("check {var}"));
//             let var = Var::new(var.0.as_str());
//             let ty = self.elab_exp(ty)?;
//             self.current_local_state.push_parameter(var, ty)?;
//         }

//         self.log("parameter ok");

//         for item in declarations {
//             match item {
//                 ModuleItem::Definition { var, ty, body } => {
//                     let ty = self.elab_exp(ty)?;
//                     let body = self.elab_exp(body)?;

//                     self.current_local_state.check(&body, &ty)?;

//                     self.current_local_state.push_item(Item::Definition {
//                         name: Var::new(var.0.as_str()),
//                         ty,
//                         body,
//                     });
//                 }
//                 ModuleItem::Inductive {
//                     type_name,
//                     parameter,
//                     arity,
//                     constructors,
//                 } => {
//                     let type_name = Var::new(type_name.0.as_str());

//                     let parameter_elab: Vec<(Var, Exp)> = parameter
//                         .iter()
//                         .map(|(var, ty)| Ok((Var::new(var.0.as_str()), self.elab_exp(ty)?)))
//                         .collect::<Result<Vec<(Var, Exp)>, String>>()?;

//                     let (indices_elab, sort) = kernel::utils::decompose_prod(self.elab_exp(arity)?);

//                     let Exp::Sort(sort) = sort else {
//                         return Err(format!(
//                             "Inductive type arity {arity:?} does not end with a Sort"
//                         ));
//                     };

//                     let mut ctor_names = vec![];
//                     let mut constructors_elab = vec![];

//                     for (ctor_name, ctor_args) in constructors {
//                         let ctor_name_var = Var::new(ctor_name.0.as_str());
//                         ctor_names.push(ctor_name_var);

//                         let ctor_type_elab =
//                             self.elab_exp_rec(ctor_args, vec![type_name.clone()])?;

//                         let (telescope, tails) = kernel::utils::decompose_prod(ctor_type_elab);

//                         let mut ctor_binders = vec![];
//                         for (v, e) in telescope {
//                             // may be problematic
//                             if contains_as_freevar(&e, &type_name) {
//                                 // strict positive case
//                                 let (inner_binders, inner_tail) = kernel::utils::decompose_prod(e);
//                                 for (_, it) in inner_binders.iter() {
//                                     if contains_as_freevar(it, &type_name) {
//                                         return Err(format!(
//                                             "Constructor binder type {it} contains inductive type name {type_name} in non-strictly positive position"
//                                         ));
//                                     }
//                                 }
//                                 let (head, tail) = kernel::utils::decompose_app(inner_tail);
//                                 if !matches!(head, Exp::Var(head_var) if head_var.is_eq_ptr(&type_name))
//                                 {
//                                     return Err(format!(
//                                         "Constructor binder type head does not match inductive type name {type_name}"
//                                     ));
//                                 }

//                                 for tail_elm in tail.iter() {
//                                     if contains_as_freevar(tail_elm, &type_name) {
//                                         return Err(format!(
//                                             "Constructor binder type tail {tail_elm} contains inductive type name {type_name} in non-strictly positive position"
//                                         ));
//                                     }
//                                 }
//                                 ctor_binders.push(CtorBinder::StrictPositive {
//                                     binders: inner_binders,
//                                     self_indices: tail,
//                                 });
//                             } else {
//                                 // simple case
//                                 ctor_binders.push(CtorBinder::Simple((v, e)));
//                             }
//                         }

//                         let (head, tail) = kernel::utils::decompose_app(tails);
//                         let Exp::Var(head_var) = head else {
//                             return Err(format!("Constructor type head {head} is not a Var"));
//                         };
//                         if !head_var.is_eq_ptr(&type_name) {
//                             return Err(format!(
//                                 "Constructor type head {head_var} does not match inductive type name {type_name}"
//                             ));
//                         }
//                         for tail_elm in tail.iter() {
//                             if contains_as_freevar(tail_elm, &type_name) {
//                                 return Err(format!(
//                                     "Constructor type tail {tail_elm} contains inductive type name {type_name}"
//                                 ));
//                             }
//                         }

//                         constructors_elab.push(kernel::inductive::CtorType {
//                             telescope: ctor_binders,
//                             indices: tail,
//                         });
//                     }

//                     let (ders, res) = kernel::inductive::acceptable_typespecs(
//                         &self.current_local_state.parameters,
//                         parameter_elab.clone(),
//                         indices_elab.clone(),
//                         sort,
//                         constructors_elab,
//                     );

//                     for der in ders {
//                         self.current_local_state.log.push(Either::Left(der));
//                     }

//                     match res {
//                         Ok(indspecs_elab) => {
//                             let item_elab = Item::Inductive {
//                                 name: type_name,
//                                 ctor_names,
//                                 ind_defs: std::rc::Rc::new(indspecs_elab),
//                             };
//                             self.current_local_state.items.push(item_elab);
//                         }
//                         Err(err) => {
//                             return Err(format!(
//                                 "Inductive type {} definition is not acceptable: {}",
//                                 type_name.name(),
//                                 err
//                             ));
//                         }
//                     }
//                 }
//                 ModuleItem::MathMacro { .. } | ModuleItem::UserMacro { .. } => todo!(),
//             }
//         }

//         self.module_stack.push(ModuleResolved {
//             name: Var::new(name.0.as_str()),
//             parameters: self.current_local_state.parameters.clone(),
//             items: self.current_local_state.items.clone(),
//         });

//         Ok(())
//     }
//     pub fn get_resolved_module(
//         &mut self,
//         mod_instantiated: &ModuleInstantiated,
//     ) -> Result<usize, String> {
//         let ModuleInstantiated {
//             module_name,
//             arguments,
//         } = mod_instantiated;

//         let Some(mod_templates) = self.get_module_templates(module_name) else {
//             return Err(format!(
//                 "Module {} not found",
//                 mod_instantiated.module_name.0.as_str()
//             ));
//         };

//         // check arguments
//         if mod_templates.parameters.len() != arguments.len() {
//             return Err(format!(
//                 "Module {} expects {} arguments, but {} were provided",
//                 mod_instantiated.module_name.0.as_str(),
//                 mod_templates.parameters.len(),
//                 arguments.len()
//             ));
//         }

//         let arguments_elab: Vec<Exp> = arguments
//             .iter()
//             .zip(mod_templates.parameters.iter())
//             .map(|((n, arg), (v, _))| {
//                 if n.0.as_str() != v.name() {
//                     return Err(format!(
//                         "Argument name {} does not match parameter name {}",
//                         n.0.as_str(),
//                         v.name()
//                     ));
//                 }
//                 self.elab_exp(arg)
//             })
//             .collect::<Result<Vec<Exp>, String>>()?;

//         // case: already realized <= checked arg[]: ty[]
//         if let Some(idx) = self
//             .current_local_state
//             .is_realized(module_name, &arguments_elab)
//         {
//             return Ok(idx);
//         }

//         // case: not yet realized => need to check arg[]: ty[]
//         let mut subst_stack = vec![];

//         for i in 0..mod_templates.parameters.len() {
//             let (var, ty) = &mod_templates.parameters[i];
//             let ty_substed = subst_map(ty, &subst_stack);
//             let arg_elab = &arguments_elab[i];

//             self.current_local_state.check(arg_elab, &ty_substed)?;

//             subst_stack.push((var.clone(), arg_elab.clone()));
//         }

//         self.current_local_state
//             .push_realized(mod_templates.realize(arguments_elab));

//         Ok(self.current_local_state.realized.len() - 1)
//     }
//     pub fn mod_path_instantiation(&self, path: &ModPath) -> Result<ModuleInstantiated, String> {
//         match path {
//             ModPath::AbsoluteRoot(instantiated_module) => Ok(instantiated_module.clone()),
//         }
//     }
//     fn elab_exp(&mut self, sexp: &SExp) -> Result<Exp, String> {
//         self.elab_exp_rec(sexp, vec![])
//     }

//     // does not check well-typed ness
//     // bind_var ... recursion on expression to bindings
//     pub fn elab_exp_rec(&mut self, sexp: &SExp, mut bind_var: Vec<Var>) -> Result<Exp, String> {
//         match sexp {
//             SExp::ModAccessDef { path, name } => {
//                 let inst = self.mod_path_instantiation(path)?;
//                 let mod_realized_idx = self.get_resolved_module(&inst)?;
//                 self.current_local_state.realized[mod_realized_idx]
//                     .items
//                     .iter()
//                     .find_map(|item| match item {
//                         Item::Definition {
//                             name: def_name,
//                             ty: _,
//                             body,
//                         } => {
//                             if def_name.name() == name.0.as_str() {
//                                 Some(body.clone())
//                             } else {
//                                 None
//                             }
//                         }
//                         _ => None,
//                     })
//                     .ok_or(format!(
//                         "Definition {} not found in module {}",
//                         name.0.as_str(),
//                         inst.module_name.0.as_str()
//                     ))
//             }
//             SExp::MathMacro { .. } | SExp::NamedMacro { .. } => {
//                 todo!("Macro expansion not implemented yet")
//             }
//             SExp::Where { exp, clauses } => {
//                 let mut bind_var_exp = bind_var.clone();
//                 let let_ins: Vec<(Var, Exp, Exp)> = clauses
//                     .iter()
//                     .map(|(var, ty, body)| {
//                         bind_var_exp.push(Var::new(var.0.as_str())); // to capture var in body
//                         Ok((
//                             Var::new(var.0.as_str()),
//                             // doen't capture var each other
//                             self.elab_exp_rec(ty, bind_var.clone())?,
//                             self.elab_exp_rec(body, bind_var.clone())?,
//                         ))
//                     })
//                     .collect::<Result<Vec<(Var, Exp, Exp)>, String>>()?;
//                 let mut exp_elab = self.elab_exp_rec(exp, bind_var_exp.clone())?;
//                 for (var, ty, body) in let_ins.into_iter().rev() {
//                     exp_elab = Exp::App {
//                         func: Box::new(Exp::Lam {
//                             var,
//                             ty: Box::new(ty),
//                             body: Box::new(exp_elab),
//                         }),
//                         arg: Box::new(body),
//                     };
//                 }
//                 Ok(exp_elab)
//             }
//             SExp::WithProof { exp, proofs } => {
//                 let exp_elab = self.elab_exp_rec(exp, bind_var.clone())?;
//                 let mut goals_elab = vec![];
//                 for goal in proofs {
//                     goals_elab.push(self.map_goal(goal.clone())?);
//                 }
//                 Ok(Exp::ProveHere {
//                     exp: Box::new(exp_elab),
//                     goals: goals_elab,
//                 })
//             }
//             SExp::Sort(sort) => Ok(Exp::Sort(*sort)),
//             SExp::Identifier(identifier) => {
//                 // check bounded variables from bind_var
//                 if bind_var.iter().any(|v| v.name() == identifier.0.as_str()) {
//                     return Ok(Exp::Var(Var::new(identifier.0.as_str())));
//                 }

//                 // check items
//                 if let Some(item) = self.current_local_state.resolve_item(identifier) {
//                     match item {
//                         Item::Definition {
//                             name: _,
//                             ty: _,
//                             body,
//                         } => {
//                             return Ok(body);
//                         }
//                         Item::Inductive {
//                             name: _,
//                             ctor_names: _,
//                             ind_defs,
//                         } => {
//                             return Ok(Exp::IndType {
//                                 indty: ind_defs,
//                                 parameters: vec![],
//                             });
//                         }
//                     }
//                 }

//                 // check from current parameters
//                 if let Some(exp) = self.current_local_state.resolve_var_in_param(identifier) {
//                     return Ok(exp);
//                 }

//                 Err(format!("Unbound identifier: {}", identifier.0.as_str()))
//             }
//             SExp::Prod { bind, body } => {
//                 // 1. { var: None, ty: A, predicate: None }  -->  ( _: A ) -> B
//                 // 2. { var: Some x, ty: A, predicate: None }  -->  ( x: A ) -> B(x)
//                 // 3. { var: Some x, ty: A, predicate: Some (None, P) }  -->  ( x: {x: A | P(x)} ) -> B(x)
//                 // 4. { var: Some x, ty: A, predicate: Some (Some p, P) }  -->  ( x: {x: A | P(x)} ) -> ( p: P(x) ) -> B(x, p)
//                 let crate::syntax::Bind { var, ty, predicate } = bind;

//                 let ty_elab = self.elab_exp_rec(ty, bind_var.clone())?;

//                 match var {
//                     // 1.
//                     None => {
//                         // assetion: predicate == None
//                         if predicate.is_some() {
//                             return Err(
//                                 "Predicate in anonymous product is not supported yet".to_string()
//                             );
//                         }
//                         let body_elab = self.elab_exp_rec(body, bind_var.clone())?;
//                         Ok(Exp::Prod {
//                             var: Var::dummy(),
//                             ty: Box::new(ty_elab),
//                             body: Box::new(body_elab),
//                         })
//                     }
//                     Some(var) => {
//                         let v = Var::new(var.0.as_str());
//                         bind_var.push(v.clone());
//                         match predicate {
//                             // 2.
//                             None => {
//                                 let body_elab = self.elab_exp_rec(body, bind_var.clone())?;
//                                 Ok(Exp::Prod {
//                                     var: v,
//                                     ty: Box::new(ty_elab),
//                                     body: Box::new(body_elab),
//                                 })
//                             }
//                             Some((may_name, predicate)) => {
//                                 let predicate_elab =
//                                     self.elab_exp_rec(predicate, bind_var.clone())?;
//                                 let refined_ty =
//                                     Exp::refinement(v.clone(), ty_elab, predicate_elab.clone());
//                                 match may_name {
//                                     // 3.
//                                     None => {
//                                         let body_elab =
//                                             self.elab_exp_rec(body, bind_var.clone())?;
//                                         Ok(Exp::Prod {
//                                             var: v,
//                                             ty: Box::new(refined_ty),
//                                             body: Box::new(body_elab),
//                                         })
//                                     }
//                                     // 4.
//                                     Some(name) => {
//                                         bind_var.push(Var::new(name.0.as_str()));
//                                         let body_elab =
//                                             self.elab_exp_rec(body, bind_var.clone())?;
//                                         Ok(Exp::Prod {
//                                             var: v,
//                                             ty: Box::new(refined_ty),
//                                             body: Exp::Prod {
//                                                 var: Var::new(name.0.as_str()),
//                                                 ty: Box::new(predicate_elab),
//                                                 body: body_elab.into(),
//                                             }
//                                             .into(),
//                                         })
//                                     }
//                                 }
//                             }
//                         }
//                     }
//                 }
//             }
//             SExp::Lam { bind, body } => {
//                 // 1. { var: None, ty: A, predicate: None }  -->  ( _: A ) => B
//                 // 2. { var: Some x, ty: A, predicate: None }  -->  ( x: A ) => B(x)
//                 // 3. { var: Some x, ty: A, predicate: Some (None, P) }  -->  ( x: {x: A | P(x)} ) => B(x)
//                 // 4. { var: Some x, ty: A, predicate: Some (Some p, P) }  -->  ( x: {x: A | P(x)} ) => ( p: P(x) ) => B(x, p)
//                 let crate::syntax::Bind { var, ty, predicate } = bind;

//                 let ty_elab = self.elab_exp_rec(ty, bind_var.clone())?;

//                 match var {
//                     // 1.
//                     None => {
//                         // assertion: predicate == None
//                         if predicate.is_some() {
//                             return Err(
//                                 "Predicate in anonymous lambda is not supported yet".to_string()
//                             );
//                         }
//                         let body_elab = self.elab_exp_rec(body, bind_var.clone())?;
//                         Ok(Exp::Lam {
//                             var: Var::dummy(),
//                             ty: Box::new(ty_elab),
//                             body: Box::new(body_elab),
//                         })
//                     }
//                     Some(var) => {
//                         let v = Var::new(var.0.as_str());
//                         bind_var.push(v.clone());
//                         match predicate {
//                             // 2.
//                             None => {
//                                 let body_elab = self.elab_exp_rec(body, bind_var.clone())?;
//                                 Ok(Exp::Lam {
//                                     var: v,
//                                     ty: Box::new(ty_elab),
//                                     body: Box::new(body_elab),
//                                 })
//                             }
//                             Some((may_name, predicate)) => {
//                                 let predicate_elab =
//                                     self.elab_exp_rec(predicate, bind_var.clone())?;
//                                 let refined_ty =
//                                     Exp::refinement(v.clone(), ty_elab, predicate_elab.clone());
//                                 match may_name {
//                                     // 3.
//                                     None => {
//                                         let body_elab =
//                                             self.elab_exp_rec(body, bind_var.clone())?;
//                                         Ok(Exp::Lam {
//                                             var: v,
//                                             ty: Box::new(refined_ty),
//                                             body: Box::new(body_elab),
//                                         })
//                                     }
//                                     // 4.
//                                     Some(name) => {
//                                         bind_var.push(Var::new(name.0.as_str()));
//                                         let body_elab =
//                                             self.elab_exp_rec(body, bind_var.clone())?;
//                                         Ok(Exp::Lam {
//                                             var: v,
//                                             ty: Box::new(refined_ty),
//                                             body: Box::new(Exp::Lam {
//                                                 var: Var::new(name.0.as_str()),
//                                                 ty: Box::new(predicate_elab),
//                                                 body: Box::new(body_elab),
//                                             }),
//                                         })
//                                     }
//                                 }
//                             }
//                         }
//                     }
//                 }
//             }
//             SExp::App {
//                 func,
//                 arg,
//                 piped: _,
//             } => {
//                 let func_elab = self.elab_exp_rec(func, bind_var.clone())?;
//                 let arg_elab = self.elab_exp_rec(arg, bind_var.clone())?;
//                 Ok(Exp::App {
//                     func: Box::new(func_elab),
//                     arg: Box::new(arg_elab),
//                 })
//             }
//             SExp::Annotation { exp, ty } => {
//                 let exp_elab = self.elab_exp_rec(exp, bind_var.clone())?;
//                 let ty_elab = self.elab_exp_rec(ty, bind_var.clone())?;
//                 Ok(Exp::Cast {
//                     exp: Box::new(exp_elab),
//                     to: Box::new(ty_elab),
//                 })
//             }
//             SExp::IndType {
//                 ind_type_name,
//                 parameters,
//             } => {
//                 // find inductive type from current
//                 let item = self
//                     .current_local_state
//                     .resolve_item(ind_type_name)
//                     .ok_or(format!(
//                         "Inductive type {} not found",
//                         ind_type_name.0.as_str()
//                     ))?;

//                 let Item::Inductive {
//                     name: _,
//                     ctor_names: _,
//                     ind_defs,
//                 } = item
//                 else {
//                     return Err(format!(
//                         "{} is not an inductive type",
//                         ind_type_name.0.as_str()
//                     ));
//                 };

//                 let mut parameters_elab = vec![];
//                 for param in parameters {
//                     let param_elab = self.elab_exp_rec(param, bind_var.clone())?;
//                     parameters_elab.push(param_elab);
//                 }
//                 Ok(Exp::IndType {
//                     indty: ind_defs,
//                     parameters: parameters_elab,
//                 })
//             }
//             SExp::IndCtor {
//                 ind_type_name,
//                 constructor_name,
//                 parameteres,
//             } => todo!(),
//             SExp::IndElim {
//                 ind_type_name,
//                 eliminated_exp,
//                 return_type,
//                 cases,
//             } => todo!(),
//             SExp::Proof { term } => todo!(),
//             SExp::Pow { power } => todo!(),
//             SExp::Sub { var, ty, predicate } => todo!(),
//             SExp::Pred {
//                 superset,
//                 subset,
//                 elem,
//             } => todo!(),
//             SExp::TypeLift { superset, subset } => todo!(),
//             SExp::Equal { left, right } => todo!(),
//             SExp::Exists { bind } => todo!(),
//             SExp::Take { bind, body } => todo!(),
//             SExp::ProofBy(proof_by) => todo!(),
//             SExp::Block(block) => todo!(),
//         }
//     }
//     fn map_goal(&mut self, goal: WithGoal) -> Result<ProveGoal, String> {
//         let WithGoal {
//             extended_ctx,
//             goal,
//             proof_term,
//         } = goal;
//         let mut ctx_elab = vec![];
//         for (var, ty) in extended_ctx {
//             let var = Var::new(var.0.as_str());
//             let ty = self.elab_exp(&ty)?;
//             ctx_elab.push((var, ty));
//         }
//         let goal_elab = self.elab_exp(&goal)?;
//         let proof_term_elab = self.elab_exp(&proof_term)?;
//         Ok(ProveGoal {
//             extended_ctx: ctx_elab.into(),
//             goal_prop: goal_elab,
//             proof_term: proof_term_elab,
//         })
//     }
// }
