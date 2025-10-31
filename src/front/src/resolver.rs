// NOTE for GitHub Copilot:
// In this compiler, variable handling differs between surface expression and kernel expression levels.
// surface ... `Identifier(String)` for names,
// kernel ... `Var(std::rc::Rc<String>)` as a global ID mechanism
//   each Rc pointer is unique,allowing fresh variables and true binding equality by pointer identity.
// This design makes substitution easier (`subst`), but elaboration must carefully
// align variables between the two levels to preserve correct correspondence.

use std::collections::HashMap;

use crate::syntax::*;
use either::Either;
use kernel::{
    calculus::{contains_as_freevar, subst_map},
    exp::*,
    inductive::{CtorBinder, InductiveTypeSpecs},
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
        module_name: kernel::exp::Var,
        import_name: kernel::exp::Var,
        args: Vec<(Var, Exp)>,
    },
}

// do type checking
pub struct GlobalEnvironment {
    module_templates: Vec<ModuleResolved>,
    elaborator: Elaborator,
    logger: Logger, // to pass to elaborator
}

impl GlobalEnvironment {
    pub fn logs(&self) -> &Vec<Either<Derivation, String>> {
        &self.logger.log
    }
}

pub struct Logger {
    log: Vec<Either<Derivation, String>>,
}

impl Logger {
    pub fn log_derivation(&mut self, der: Derivation) {
        self.log.push(Either::Left(der));
    }
    pub fn log(&mut self, msg: String) {
        self.log.push(Either::Right(msg));
    }
}

impl Default for GlobalEnvironment {
    fn default() -> Self {
        GlobalEnvironment {
            module_templates: vec![],
            elaborator: Elaborator {
                parameters: vec![],
                realized: HashMap::new(),
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
                realized: HashMap::new(),
                items: vec![],
            };

            // get elaborated parameters
            let parameteres_elab = self
                .elaborator
                .elab_telescope(&mut self.logger, parameters)?;

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

        // chek well-formedness of items
        {
            for item in declarations {
                let items_elab = self.elaborator.elab_item(&mut self.logger, item)?;
                match &items_elab {
                    Item::Definition { name, ty, body } => {
                        let der = kernel::derivation::check(&self.elaborator.parameters, body, ty);
                        self.logger.log_derivation(der.clone());
                        if !der.node().unwrap().is_success() {
                            return Err(format!(
                                "Definition {} type checking failed: body {} does not have type {}",
                                name.as_str(),
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
                                name.as_str(),
                                err
                            ));
                        }
                    }
                    Item::Import {
                        module_name,
                        import_name: _,
                        args,
                    } => {
                        let module_template = match self
                            .module_templates
                            .iter()
                            .rev()
                            .find(|m| m.name.as_str() == module_name.as_str())
                        {
                            Some(m) => m,
                            None => {
                                return Err(format!(
                                    "Imported module template {} not found",
                                    module_name.as_str()
                                ));
                            }
                        };

                        if module_template.parameters.len() != args.len() {
                            return Err(format!(
                                "Imported module expects {} arguments, but {} were provided",
                                module_template.parameters.len(),
                                args.len()
                            ));
                        }

                        // type check
                        {
                            let mut subst_maps = vec![];
                            for ((v0, arg), (v1, ty)) in
                                args.iter().zip(module_template.parameters.iter())
                            {
                                // we need to check name string match and subst with it
                                if v0.as_str() != v1.as_str() {
                                    return Err(format!(
                                        "Imported module argument name {} does not match parameter name {}",
                                        v0.as_str(),
                                        v1.as_str()
                                    ));
                                }

                                let ty_substed = subst_map(ty, &subst_maps);
                                let der =
                                    kernel::derivation::check(&self.elaborator.parameters, arg, ty);
                                self.logger.log_derivation(der.clone());
                                if !der.node().unwrap().is_success() {
                                    return Err(format!(
                                        "Imported module argument type checking failed: argument {} does not have type {}",
                                        arg, ty_substed
                                    ));
                                }
                                subst_maps.push((v1.clone(), arg.clone()));
                            }
                        }
                    }
                }
                self.elaborator.items.push(items_elab);
            }
        }

        self.module_templates.push(ModuleResolved {
            name: Var::new(name.0.as_str()),
            parameters: self.elaborator.parameters.clone(),
            items: self.elaborator.items.clone(),
        });

        Ok(())
    }
}

// elaborator does not type check
pub struct Elaborator {
    parameters: Vec<(Var, Exp)>,
    realized: HashMap<Var, ModuleRealized>,
    items: Vec<Item>, // previously elaborated items
}

// resolve path
// len == 1 => locally binded variable | current module defined item (definition, inductive type name) | module parameter
// len == 2 => current module's inductive type constructor access | named module's item access
// len == 3 => named module's inductive type constructor access
// in the case of inductive type of constructors, we need to uncurry with tails
// the other cases, elaborate with tails
impl Elaborator {
    fn module_item_definition_name(&self, name: &Identifier) -> Option<&Exp> {
        for item in self.items.iter().rev() {
            if let Item::Definition {
                name: def_name,
                ty: _,
                body,
            } = item
                && def_name.as_str() == name.0.as_str()
            {
                return Some(body);
            }
        }
        None
    }
    fn module_item_indtype_name(
        &self,
        name: &Identifier,
    ) -> Option<std::rc::Rc<InductiveTypeSpecs>> {
        for item in self.items.iter().rev() {
            if let Item::Inductive {
                name: ind_name,
                ctor_names: _,
                ind_defs,
            } = item
                && ind_name.as_str() == name.0.as_str()
            {
                return Some(ind_defs.clone());
            }
        }
        None
    }
    fn module_item_indctor(
        &self,
        indtype_name: &Identifier,
        ctor_name: &Identifier,
    ) -> Option<(std::rc::Rc<InductiveTypeSpecs>, usize)> {
        for item in self.items.iter().rev() {
            if let Item::Inductive {
                name: ind_name,
                ctor_names,
                ind_defs,
            } = item
                && ind_name.as_str() == indtype_name.0.as_str()
            {
                for (idx, ctor_name_item) in ctor_names.iter().enumerate() {
                    if ctor_name_item.as_str() == ctor_name.0.as_str() {
                        return Some((ind_defs.clone(), idx));
                    }
                }
            }
        }
        None
    }
    fn named_module_definition_name(
        &self,
        module_name: &Identifier,
        item_name: &Identifier,
    ) -> Option<&Exp> {
        let module_realized = self.realized.get(&Var::new(module_name.0.as_str()))?;
        for item in module_realized.items.iter().rev() {
            if let Item::Definition {
                name: def_name,
                ty: _,
                body,
            } = item
                && def_name.as_str() == item_name.0.as_str()
            {
                return Some(body);
            }
        }
        None
    }
    fn named_module_indtype_name(
        &self,
        module_name: &Identifier,
        indtype_name: &Identifier,
    ) -> Option<std::rc::Rc<InductiveTypeSpecs>> {
        let module_realized = self.realized.get(&Var::new(module_name.0.as_str()))?;
        for item in module_realized.items.iter().rev() {
            if let Item::Inductive {
                name: ind_name,
                ctor_names: _,
                ind_defs,
            } = item
                && ind_name.as_str() == indtype_name.0.as_str()
            {
                return Some(ind_defs.clone());
            }
        }
        None
    }
    fn named_module_indctor(
        &self,
        module_name: &Identifier,
        indtype_name: &Identifier,
        ctor_name: &Identifier,
    ) -> Option<(std::rc::Rc<InductiveTypeSpecs>, usize)> {
        let module_realized = self.realized.get(&Var::new(module_name.0.as_str()))?;
        for item in module_realized.items.iter().rev() {
            if let Item::Inductive {
                name: ind_name,
                ctor_names,
                ind_defs,
            } = item
                && ind_name.as_str() == indtype_name.0.as_str()
            {
                for (idx, ctor_name_item) in ctor_names.iter().enumerate() {
                    if ctor_name_item.as_str() == ctor_name.0.as_str() {
                        return Some((ind_defs.clone(), idx));
                    }
                }
            }
        }
        None
    }
}

impl Elaborator {
    fn elab_item(
        &mut self,
        logger: &mut Logger,
        item: &crate::syntax::ModuleItem,
    ) -> Result<Item, String> {
        match item {
            ModuleItem::Definition { var, ty, body } => {
                let var: Var = var.into();
                let ty_elab = self.elab_exp(logger, ty, &[])?;
                let body_elab = self.elab_exp(logger, body, &[])?;
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
                let parameter_elab = self.elab_telescope(logger, parameter)?;

                // elaborate arity and decompose to (x[0]: A[0]) -> ... -> (x[n]: A[n]) -> Sort
                let arity_elab = self.elab_exp(logger, arity, &[])?;
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
                    let ctor_type_elab = self.elab_exp(logger, ctor_args, &[type_name.clone()])?;
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
                        module_name, // will be not yet realized ... deligate every thing to global
                        arguments,
                    },
                import_name,
            } => {
                let args_elab = arguments
                    .iter()
                    .map(|(v, e)| {
                        let v: Var = v.into();
                        let e_elab = self.elab_exp(logger, e, &[])?;
                        Ok((v, e_elab))
                    })
                    .collect::<Result<Vec<_>, String>>()?;

                Ok(Item::Import {
                    module_name: Var::new(module_name.0.as_str()),
                    import_name: Var::new(import_name.0.as_str()),
                    args: args_elab,
                })
            }
            ModuleItem::MathMacro { .. } | ModuleItem::UserMacro { .. } => todo!(),
        }
    }
    fn elab_exp(
        &mut self,
        logger: &mut Logger,
        sexp: &crate::syntax::SExp,
        reference_var: &[Var],
    ) -> Result<Exp, String> {
        self.elab_exp_rec(logger, sexp, reference_var, vec![])
    }
    fn elab_telescope(
        &mut self,
        logger: &mut Logger,
        telescope: &Vec<(Identifier, crate::syntax::SExp)>,
    ) -> Result<Vec<(Var, Exp)>, String> {
        let mut result = vec![];
        let mut reference_var = vec![];
        for (v, ty) in telescope {
            let v: Var = v.into();
            let ty_elab = self.elab_exp(logger, ty, &reference_var)?;
            reference_var.push(v.clone());
            result.push((v, ty_elab));
        }
        Ok(result)
    }
    fn elab_exp_rec(
        &mut self,
        logger: &mut Logger,
        mut sexp: &crate::syntax::SExp,
        reference_var: &[Var],
        bind_var: Vec<(Var, Exp)>,
    ) -> Result<Exp, String> {
        // we need to uncurry with parameters if it's an ind_type or ind_ctor
        let mut tails = vec![];
        while let SExp::App {
            func,
            arg,
            piped: _,
        } = sexp
        {
            tails.push(arg.as_ref().clone());
            sexp = func.as_ref();
        }

        let tails_elab = tails
            .iter()
            .rev()
            .map(|arg| self.elab_exp_rec(logger, arg, reference_var, bind_var.clone()))
            .collect::<Result<Vec<Exp>, String>>()?;

        let left_most: Exp = 'l: {
            match sexp {
                SExp::App { .. } => {
                    unreachable!("why ?")
                }
                SExp::AccessPath(idents) => {
                    // case len == 1
                    if let [ident] = &idents[..] {
                        // case: binded in expression
                        for (v, _) in bind_var.iter().rev() {
                            // apply tails here
                            if v.as_str() == ident.0.as_str() {
                                // return Ok(kernel::utils::assoc_apply(Exp::Var(v.clone()), tails_elab));
                                break 'l Exp::Var(v.clone());
                            }
                        }
                        // case: binded in reference_var
                        for v in reference_var.iter().rev() {
                            if v.as_str() == ident.0.as_str() {
                                break 'l Exp::Var(v.clone());
                            }
                        }

                        // case: current module's defined items
                        if let Some(body) = self.module_item_definition_name(ident) {
                            break 'l body.clone();
                        }
                        if let Some(indspec) = self.module_item_indtype_name(ident) {
                            return Ok(Exp::IndType {
                                indspec,
                                parameters: tails_elab,
                            });
                        }

                        // case: current module's parameters
                        for (v, _) in self.parameters.iter().rev() {
                            if v.as_str() == ident.0.as_str() {
                                break 'l Exp::Var(v.clone());
                            }
                        }

                        return Err(format!("Unbound identifier: {}", ident));
                    }

                    // case len == 2
                    if let [path0, path1] = &idents[..] {
                        // case: path0 is type name in current module, path1 is constructor name
                        if let Some((indspec, ctor_idx)) = self.module_item_indctor(path0, path1) {
                            return Ok(Exp::IndCtor {
                                indspec,
                                idx: ctor_idx,
                                parameters: tails_elab,
                            });
                        }

                        // case: path0 is module named path1 is item name
                        if let Some(body) = self.named_module_definition_name(path0, path1) {
                            break 'l body.clone();
                        }
                        if let Some(indpecs) = self.named_module_indtype_name(path0, path1) {
                            return Ok(Exp::IndType {
                                indspec: indpecs,
                                parameters: tails_elab,
                            });
                        }

                        return Err(format!(
                            "Unbound identifier: {}.{}",
                            path0.0.as_str(),
                            path1.0.as_str()
                        ));
                    }

                    // case len == 3
                    if let [path0, path1, path2] = &idents[..] {
                        // case: path0 is module name, path1 is inductive type name, path2 is constructor name
                        if let Some((ind_defs, ctor_idx)) =
                            self.named_module_indctor(path0, path1, path2)
                        {
                            return Ok(Exp::IndCtor {
                                indspec: ind_defs,
                                idx: ctor_idx,
                                parameters: tails_elab,
                            });
                        }

                        return Err(format!(
                            "Unbound identifier: {}.{}.{}",
                            path0.0.as_str(),
                            path1.0.as_str(),
                            path2.0.as_str()
                        ));
                    }

                    return Err(format!("too long"));
                }
                SExp::MathMacro { .. } | SExp::NamedMacro { .. } => todo!(),
                SExp::Where { exp, clauses } => todo!(),
                SExp::WithProof { exp, proofs } => todo!(),
                SExp::Sort(sort) => todo!(),
                SExp::Prod { bind, body } => todo!(),
                SExp::Lam { bind, body } => todo!(),
                SExp::Annotation { exp, ty } => todo!(),
                SExp::IndElim {
                    ind_type_name,
                    eliminated_exp,
                    return_type,
                    cases,
                } => todo!(),
                SExp::Proof { term } => todo!(),
                SExp::Pow { power } => todo!(),
                SExp::Sub { var, ty, predicate } => todo!(),
                SExp::Pred {
                    superset,
                    subset,
                    elem,
                } => todo!(),
                SExp::TypeLift { superset, subset } => todo!(),
                SExp::Equal { left, right } => todo!(),
                SExp::Exists { bind } => todo!(),
                SExp::Take { bind, body } => todo!(),
                SExp::ProofBy(proof_by) => todo!(),
                SExp::Block(block) => todo!(),
            }
        };

        Ok(kernel::utils::assoc_apply(left_most, tails_elab))
    }
}

// for templates
#[derive(Debug, Clone)]
pub struct ModuleResolved {
    pub name: Var,
    pub parameters: Vec<(Var, Exp)>, // v: ty
    pub items: Vec<Item>,
}

pub struct ModuleRealized {
    pub name: Var,
    pub arguments: Vec<Exp>, // v := arg
    pub items: Vec<Item>,
}
