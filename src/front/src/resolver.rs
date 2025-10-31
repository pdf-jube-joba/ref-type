use std::collections::HashMap;

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
    Import {
        name: kernel::exp::Var,
        module_idx: usize,
        args: Vec<Exp>,
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
                name_map: HashMap::new(),
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

        // elaborator setup
        {
            // reset
            self.elaborator = Elaborator {
                parameters: vec![],
                items: vec![],
            };

            // get elaborated parameters
            let parameteres_elab =
                self.elaborator
                    .elab_telescope(&mut self.resolver, &mut self.logger, parameters)?;

            // sort check parameter's ty
            for (_, ty) in parameteres_elab.iter() {
                let der = kernel::derivation::infer_sort(&self.elaborator.parameters, ty);
                self.logger.log_derivation(der.clone());
                if !der.node().unwrap().is_success() {
                    return Err(format!(
                        "Parameter type checking failed: type {ty} is not a valid type",
                    ));
                }
            }

            // set elaborator parameters
            self.elaborator.parameters = parameteres_elab.clone();
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
                        let der = kernel::derivation::check(&self.elaborator.parameters, body, ty);
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
                        let (ders, res) = kernel::inductive::acceptable_typespecs(
                            &self.elaborator.parameters,
                            ind_defs,
                        );
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
                    Item::Import {
                        name,
                        module_idx,
                        args,
                    } => {}
                }
            }
        }

        self.resolver.module_templates.push(ModuleResolved {
            name: Var::new(name.0.as_str()),
            parameters: self.elaborator.parameters.clone(),
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
    name_map: HashMap<Var, usize>,
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
    pub fn get_module_template_idx(&self, name: &Identifier) -> Option<usize> {
        for (idx, module) in self.module_templates.iter().rev().enumerate() {
            if module.name.name() == name.0.as_str() {
                return Some(idx);
            }
        }
        None
    }
    pub fn get_module_template_from_idx(&self, idx: usize) -> Option<ModuleResolved> {
        self.module_templates.get(idx).cloned()
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
    pub fn get_realized_module(&self, name: &Var) -> Option<&ModuleRealized> {
        let idx = self.name_map.get(name)?;
        Some(self.realized_modules.get(*idx).unwrap())
    }
    pub fn get_realized_module_item(
        &self,
        name: &Identifier,
        item: &Identifier,
    ) -> Result<Item, String> {
        for module in self.realized_modules.iter().rev() {
            if module.name.name() == name.0.as_str() {
                for it in module.items.iter() {
                    match it {
                        Item::Definition { name: def_name, .. }
                        | Item::Inductive { name: def_name, .. } => {
                            if def_name.name() == item.0.as_str() {
                                return Ok(it.clone());
                            }
                        }
                        _ => {}
                    }
                }
                return Err(format!(
                    "Item {} not found in realized module {}",
                    item.0.as_str(),
                    name.0.as_str()
                ));
            }
        }
        Err(format!("Realized module {} not found", name.0.as_str()))
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
            ModuleItem::Import {
                path:
                    ModuleInstantiated {
                        module_name,
                        arguments,
                    },
                import_name,
            } => {
                // we will check
                // - pointed module exists
                // - arguments are well-named

                let module_idx = resolver
                    .get_module_template_idx(module_name)
                    .ok_or(format!(
                        "Module template {} not found",
                        module_name.0.as_str()
                    ))?;

                let mod_template = resolver.get_module_template_from_idx(module_idx).unwrap();
                let mut args_elab = vec![];

                for i in 0..mod_template.parameters.len() {
                    let (param_var, _) = &mod_template.parameters[i];
                    let (arg_name, arg_sexp) = &arguments[i];
                    if param_var.name() != arg_name.0.as_str() {
                        return Err(format!(
                            "Argument name {} does not match parameter name {}",
                            arg_name.0.as_str(),
                            param_var.name()
                        ));
                    }
                    let arg_elab = self.elab_exp(resolver, logger, arg_sexp, &[])?;
                    args_elab.push(arg_elab);
                }

                Ok(Item::Import {
                    name: Var::new(import_name.0.as_str()),
                    module_idx,
                    args: args_elab,
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
                        _ => {
                            unreachable!(
                                "only Definition and Inductive are allowed in previously elaborated items"
                            )
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
            SExp::ModAccessDef { path, name } => {
                let module_path = match path {
                    ModPath::Named(mod_name) => mod_name.clone(),
                };
                let item = resolver.get_realized_module_item(&module_path, name)?;
                match item {
                    Item::Definition {
                        name: _,
                        ty: _,
                        body,
                    } => Ok(body.clone()),
                    Item::Inductive {
                        name: _,
                        ctor_names: _,
                        ind_defs,
                    } => Ok(Exp::IndType {
                        indty: ind_defs.clone(),
                        parameters: vec![],
                    }),
                    _ => unreachable!(
                        "only Definition and Inductive are allowed in realized module items"
                    ),
                }
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
                Item::Import {
                    name,
                    module_idx,
                    args,
                } => {
                    let args_substed: Vec<Exp> = args
                        .iter()
                        .map(|e| subst_map(e, &arguments_substmap))
                        .collect();
                    Item::Import {
                        name: name.clone(),
                        module_idx: *module_idx,
                        args: args_substed,
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
