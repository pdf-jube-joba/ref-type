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

impl Item {
    fn subst(&self, subst_mapping: &[(Var, Exp)]) -> Item {
        match self {
            Item::Definition { name, ty, body } => Item::Definition {
                name: name.clone(),
                ty: subst_map(ty, subst_mapping),
                body: subst_map(body, subst_mapping),
            },
            Item::Inductive {
                name,
                ctor_names,
                ind_defs,
            } => Item::Inductive {
                name: name.clone(),
                ctor_names: ctor_names.clone(),
                ind_defs: std::rc::Rc::new(ind_defs.subst(subst_mapping)),
            },
            Item::Import {
                module_name,
                import_name,
                args,
            } => Item::Import {
                module_name: module_name.clone(),
                import_name: import_name.clone(),
                args: args
                    .iter()
                    .map(|(v, e)| (v.clone(), subst_map(e, subst_mapping)))
                    .collect(),
            },
        }
    }
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
            let parameters_elab = self
                .elaborator
                .elab_telescope(&mut self.logger, parameters)?;

            // sort check parameter's ty
            for (v, ty) in parameters_elab.iter() {
                self.logger
                    .log(format!("Checking parameter {} : {}", v.as_str(), ty));
                let der = kernel::derivation::infer_sort(&self.elaborator.parameters, ty);
                self.logger.log_derivation(der.clone());

                // a parameter may depends on previous parameters
                self.elaborator.parameters.push((v.clone(), ty.clone()));

                if !der.node().unwrap().is_success() {
                    return Err(format!(
                        "Parameter type checking failed: type {ty} is not a valid type",
                    ));
                }
            }
        }

        // chek well-formedness of items
        {
            for item in declarations {
                self.logger.log(format!("Checking item {:?}", item));
                let item_elab = self.elaborator.elab_item(&mut self.logger, item)?;
                match &item_elab {
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
                        import_name,
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
                        let realized = module_template
                            .realize(args.iter().map(|(_, e)| e.clone()).collect::<Vec<_>>());
                        self.elaborator
                            .realized
                            .insert(import_name.as_str().into(), realized);
                    }
                }
                self.elaborator.items.push(item_elab);
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
    realized: HashMap<Identifier, ModuleRealized>,
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
        ind_type_name: &Identifier,
        ctor_name: &Identifier,
    ) -> Option<(std::rc::Rc<InductiveTypeSpecs>, usize)> {
        for item in self.items.iter().rev() {
            if let Item::Inductive {
                name: ind_name,
                ctor_names,
                ind_defs,
            } = item
                && ind_name.as_str() == ind_type_name.0.as_str()
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
        let module_realized = self.realized.get(module_name)?;
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
        let module_realized = self.realized.get(module_name)?;
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
        let module_realized = self.realized.get(module_name)?;
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
            ModuleItem::Definition { name: var, ty, body } => {
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
                parameters: parameter,
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
                    let ctor_type_elab =
                        self.elab_exp(logger, ctor_args, std::slice::from_ref(&type_name))?;
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
        bind_var: Vec<Var>,
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

        let mut tails_elab = tails
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
                        for v in bind_var.iter().rev() {
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
                            let len = indspec.param_args_len();
                            if tails_elab.len() < len {
                                return Err(format!(
                                    "Inductive type {} expects {} parameters, but only {} were provided",
                                    ident.0.as_str(),
                                    len,
                                    tails_elab.len()
                                ));
                            }
                            let pass_parameter = tails_elab.split_off(indspec.param_args_len());
                            break 'l Exp::IndType {
                                indspec,
                                parameters: pass_parameter,
                            };
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
                            let len = indspec.param_args_len();
                            if tails_elab.len() < len {
                                return Err(format!(
                                    "Inductive type {} expects {} parameters, but only {} were provided",
                                    path0.0.as_str(),
                                    len,
                                    tails_elab.len()
                                ));
                            }
                            let pass_parameter = tails_elab.split_off(indspec.param_args_len());
                            break 'l Exp::IndCtor {
                                indspec,
                                idx: ctor_idx,
                                parameters: pass_parameter,
                            };
                        }

                        // case: path0 is module named path1 is item name
                        if let Some(body) = self.named_module_definition_name(path0, path1) {
                            break 'l body.clone();
                        }
                        if let Some(indpecs) = self.named_module_indtype_name(path0, path1) {
                            let len = indpecs.param_args_len();
                            if tails_elab.len() < len {
                                return Err(format!(
                                    "Inductive type {}.{} expects {} parameters, but only {} were provided",
                                    path0.0.as_str(),
                                    path1.0.as_str(),
                                    len,
                                    tails_elab.len()
                                ));
                            }
                            let pass_parameter = tails_elab.split_off(indpecs.param_args_len());
                            break 'l Exp::IndType {
                                indspec: indpecs,
                                parameters: pass_parameter,
                            };
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
                            let len = ind_defs.param_args_len();
                            if tails_elab.len() < len {
                                return Err(format!(
                                    "Inductive type {}.{} expects {} parameters, but only {} were provided",
                                    path1.0.as_str(),
                                    path2.0.as_str(),
                                    len,
                                    tails_elab.len()
                                ));
                            }
                            let pass_parameter = tails_elab.split_off(ind_defs.param_args_len());
                            break 'l Exp::IndCtor {
                                indspec: ind_defs,
                                idx: ctor_idx,
                                parameters: pass_parameter,
                            };
                        }

                        return Err(format!(
                            "Unbound identifier: {}.{}.{}",
                            path0.0.as_str(),
                            path1.0.as_str(),
                            path2.0.as_str()
                        ));
                    }

                    return Err("too long".to_string());
                }
                SExp::MathMacro { .. } | SExp::NamedMacro { .. } => {
                    todo!("macro elaboration not implemented")
                }
                SExp::Where { exp, clauses } => {
                    let mut bind_var = bind_var.clone();
                    let mut clauses_elab = vec![];
                    for (v, ty, body) in clauses {
                        let v: Var = v.into();
                        bind_var.push(v.clone());
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                        clauses_elab.push((v, ty_elab, body_elab));
                    }
                    let mut exp_elab =
                        self.elab_exp_rec(logger, exp, reference_var, bind_var.clone())?;
                    for (v, ty, body) in clauses_elab {
                        exp_elab = Exp::App {
                            func: Box::new(Exp::Lam {
                                var: v,
                                ty: Box::new(ty),
                                body: Box::new(exp_elab),
                            }),
                            arg: Box::new(body),
                        }
                    }
                    exp_elab
                }
                SExp::WithProof { exp, proofs } => {
                    let exp_elab =
                        self.elab_exp_rec(logger, exp, reference_var, bind_var.clone())?;
                    let mut proof_goals: Vec<kernel::exp::ProveGoal> = vec![];
                    for proof in proofs {
                        let WithGoal {
                            extended_ctx,
                            goal,
                            proof_term,
                        } = proof;
                        let mut bind_var = bind_var.clone();
                        let extended_ctx_elab = self.elab_telescope(logger, extended_ctx)?;
                        for (v, _) in extended_ctx_elab.iter() {
                            bind_var.push(v.clone());
                        }
                        let goal_elab =
                            self.elab_exp_rec(logger, goal, reference_var, bind_var.clone())?;
                        let proof_term_elab =
                            self.elab_exp_rec(logger, proof_term, reference_var, bind_var.clone())?;
                        proof_goals.push(ProveGoal {
                            extended_ctx: extended_ctx_elab,
                            goal_prop: goal_elab,
                            proof_term: proof_term_elab,
                        });
                    }
                    Exp::ProveHere {
                        exp: exp_elab.into(),
                        goals: proof_goals,
                    }
                }
                SExp::Sort(sort) => Exp::Sort(*sort),
                SExp::Prod { bind, body } => match bind {
                    // A -> B ... (_: A) -> B
                    Bind::Anonymous { ty } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                        Exp::Prod {
                            var: Var::dummy(),
                            ty: Box::new(ty_elab),
                            body: Box::new(body_elab),
                        }
                    }
                    // (x: A) -> B ... (x: A) -> B
                    Bind::Named { var, ty } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let var: Var = var.into();
                        let mut bind_var = bind_var.clone();
                        bind_var.push(var.clone());
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                        Exp::Prod {
                            var,
                            ty: Box::new(ty_elab),
                            body: Box::new(body_elab),
                        }
                    }
                    // (x: A | P) -> B ... (x: Lift(A, {x: A | P})) -> B
                    Bind::Subset { var, ty, predicate } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let var: Var = var.into();
                        let mut bind_var = bind_var.clone();
                        bind_var.push(var.clone());
                        let predicate_elab =
                            self.elab_exp_rec(logger, predicate, reference_var, bind_var.clone())?;
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;

                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        Exp::Prod {
                            var: var.clone(),
                            ty: Box::new(Exp::TypeLift {
                                superset: Box::new(ty_elab.clone()),
                                subset: Box::new(subset),
                            }),
                            body: Box::new(body_elab),
                        }
                    }
                    // (x: A | h: P) -> B ... (x: Lift(A, {x: A | P})) -> (h: P) -> B
                    Bind::SubsetWithProof {
                        var,
                        ty,
                        predicate,
                        proof,
                    } => {
                        let ty_elab =
                            self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                        let var: Var = var.into();
                        let mut bind_var = bind_var.clone();
                        bind_var.push(var.clone());
                        let predicate_elab =
                            self.elab_exp_rec(logger, predicate, reference_var, bind_var.clone())?;
                        let proof: Var = proof.into();
                        bind_var.push(proof.clone());
                        let body_elab =
                            self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                        let subset = Exp::SubSet {
                            var: var.clone(),
                            set: Box::new(ty_elab.clone()),
                            predicate: Box::new(predicate_elab.clone()),
                        };

                        Exp::Prod {
                            var: var.clone(),
                            ty: Box::new(Exp::TypeLift {
                                superset: Box::new(ty_elab.clone()),
                                subset: Box::new(subset),
                            }),
                            body: Box::new(Exp::Prod {
                                var: proof,
                                ty: Box::new(predicate_elab),
                                body: Box::new(body_elab),
                            }),
                        }
                    }
                },
                SExp::Lam { bind, body } => {
                    // same as Prod
                    match bind {
                        // A => B ... (_: A) => B
                        Bind::Anonymous { ty } => {
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            let body_elab =
                                self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                            Exp::Lam {
                                var: Var::dummy(),
                                ty: Box::new(ty_elab),
                                body: Box::new(body_elab),
                            }
                        }
                        // (x: A) => B ... (x: A) => B
                        Bind::Named { var, ty } => {
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            let var: Var = var.into();
                            let mut bind_var = bind_var.clone();
                            bind_var.push(var.clone());
                            let body_elab =
                                self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                            Exp::Lam {
                                var,
                                ty: Box::new(ty_elab),
                                body: Box::new(body_elab),
                            }
                        }
                        // (x: A | P) => B ... (x: Lift(A, {x: A | P})) => B
                        Bind::Subset { var, ty, predicate } => {
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            let var: Var = var.into();
                            let mut bind_var = bind_var.clone();
                            bind_var.push(var.clone());
                            let predicate_elab = self.elab_exp_rec(
                                logger,
                                predicate,
                                reference_var,
                                bind_var.clone(),
                            )?;
                            let body_elab =
                                self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;

                            let subset = Exp::SubSet {
                                var: var.clone(),
                                set: Box::new(ty_elab.clone()),
                                predicate: Box::new(predicate_elab.clone()),
                            };

                            Exp::Lam {
                                var: var.clone(),
                                ty: Box::new(Exp::TypeLift {
                                    superset: Box::new(ty_elab.clone()),
                                    subset: Box::new(subset),
                                }),
                                body: Box::new(body_elab),
                            }
                        }
                        // (x: A | h: P) => B ... (x: Lift(A, {x: A | P})) => (h: P) => B
                        Bind::SubsetWithProof {
                            var,
                            ty,
                            predicate,
                            proof,
                        } => {
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            let var: Var = var.into();
                            let mut bind_var = bind_var.clone();
                            bind_var.push(var.clone());
                            let predicate_elab = self.elab_exp_rec(
                                logger,
                                predicate,
                                reference_var,
                                bind_var.clone(),
                            )?;
                            let proof: Var = proof.into();
                            bind_var.push(proof.clone());
                            let body_elab =
                                self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                            let subset = Exp::SubSet {
                                var: var.clone(),
                                set: Box::new(ty_elab.clone()),
                                predicate: Box::new(predicate_elab.clone()),
                            };

                            Exp::Lam {
                                var: var.clone(),
                                ty: Box::new(Exp::TypeLift {
                                    superset: Box::new(ty_elab.clone()),
                                    subset: Box::new(subset),
                                }),
                                body: Box::new(Exp::Lam {
                                    var: proof,
                                    ty: Box::new(predicate_elab),
                                    body: Box::new(body_elab),
                                }),
                            }
                        }
                    }
                }
                SExp::Cast { exp, to } => {
                    let exp_elab =
                        self.elab_exp_rec(logger, exp, reference_var, bind_var.clone())?;
                    let to_elab = self.elab_exp_rec(logger, to, reference_var, bind_var.clone())?;
                    Exp::Cast {
                        exp: Box::new(exp_elab),
                        to: Box::new(to_elab),
                    }
                }
                SExp::IndElim {
                    ind_type_name,
                    elim,
                    return_type,
                    sort,
                    cases,
                } => {
                    let ind_defs = match self.module_item_indtype_name(ind_type_name) {
                        Some(indspecs) => indspecs,
                        None => {
                            return Err(format!(
                                "Inductive type {} not found for elimination",
                                ind_type_name.0.as_str()
                            ));
                        }
                    };
                    let eliminated_exp_elab =
                        self.elab_exp_rec(logger, elim, reference_var, bind_var.clone())?;
                    let return_type_elab =
                        self.elab_exp_rec(logger, return_type, reference_var, bind_var.clone())?;
                    let mut cases_elab = vec![];
                    for (ctor_name, case_exp) in cases {
                        let ctor_idx = self
                            .module_item_indctor(ind_type_name, ctor_name)
                            .ok_or(format!(
                                "Constructor {} not found in inductive type {} for elimination",
                                ctor_name.0.as_str(),
                                ind_type_name.0.as_str()
                            ))?
                            .1;
                        let case_exp_elab =
                            self.elab_exp_rec(logger, case_exp, reference_var, bind_var.clone())?;
                        cases_elab.push((ctor_idx, case_exp_elab));
                    }

                    cases_elab.sort_by_key(|(idx, _)| *idx);

                    let cases_elab = cases_elab
                        .into_iter()
                        .map(|(_, case_exp)| case_exp)
                        .collect::<Vec<Exp>>();

                    Exp::IndElim {
                        indty: ind_defs,
                        elim: Box::new(eliminated_exp_elab),
                        return_type: Box::new(return_type_elab),
                        sort: *sort,
                        cases: cases_elab,
                    }
                }
                SExp::ProveLater { term } => {
                    let term_elab =
                        self.elab_exp_rec(logger, term, reference_var, bind_var.clone())?;
                    Exp::ProveLater {
                        prop: Box::new(term_elab),
                    }
                }
                SExp::PowerSet { set } => {
                    let power_elab =
                        self.elab_exp_rec(logger, set, reference_var, bind_var.clone())?;
                    Exp::PowerSet {
                        set: Box::new(power_elab),
                    }
                }
                SExp::SubSet {
                    var,
                    set,
                    predicate,
                } => {
                    let set_elab =
                        self.elab_exp_rec(logger, set, reference_var, bind_var.clone())?;
                    let var: Var = var.into();
                    let mut bind_var = bind_var.clone();
                    bind_var.push(var.clone());
                    let predicate_elab =
                        self.elab_exp_rec(logger, predicate, reference_var, bind_var.clone())?;
                    Exp::SubSet {
                        var,
                        set: Box::new(set_elab),
                        predicate: Box::new(predicate_elab),
                    }
                }
                SExp::Pred {
                    superset,
                    subset,
                    element,
                } => {
                    let superset_elab =
                        self.elab_exp_rec(logger, superset, reference_var, bind_var.clone())?;
                    let subset_elab =
                        self.elab_exp_rec(logger, subset, reference_var, bind_var.clone())?;
                    let elem_elab =
                        self.elab_exp_rec(logger, element, reference_var, bind_var.clone())?;
                    Exp::Pred {
                        superset: Box::new(superset_elab),
                        subset: Box::new(subset_elab),
                        element: Box::new(elem_elab),
                    }
                }
                SExp::TypeLift { superset, subset } => {
                    let superset_elab =
                        self.elab_exp_rec(logger, superset, reference_var, bind_var.clone())?;
                    let subset_elab =
                        self.elab_exp_rec(logger, subset, reference_var, bind_var.clone())?;
                    Exp::TypeLift {
                        superset: Box::new(superset_elab),
                        subset: Box::new(subset_elab),
                    }
                }
                SExp::Equal { left, right } => {
                    let left_elab =
                        self.elab_exp_rec(logger, left, reference_var, bind_var.clone())?;
                    let right_elab =
                        self.elab_exp_rec(logger, right, reference_var, bind_var.clone())?;
                    Exp::Equal {
                        left: Box::new(left_elab),
                        right: Box::new(right_elab),
                    }
                }
                // this is non emptyness of type
                SExp::Exists { bind } => {
                    match bind {
                        // \exists A ... \exists A
                        Bind::Anonymous { ty } => {
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            Exp::Exists {
                                set: Box::new(ty_elab),
                            }
                        }
                        // \exists x: A ... same as Anonymous
                        Bind::Named { var: _, ty } => {
                            // may be we should warning?
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            Exp::Exists {
                                set: Box::new(ty_elab),
                            }
                        }
                        // \exists (x: A | P) ... \exists Lift(A, {x: A | P})
                        Bind::Subset { var, ty, predicate } => {
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            let var: Var = var.into();
                            let mut bind_var = bind_var.clone();
                            bind_var.push(var.clone());
                            let predicate_elab = self.elab_exp_rec(
                                logger,
                                predicate,
                                reference_var,
                                bind_var.clone(),
                            )?;

                            let subset = Exp::SubSet {
                                var: var.clone(),
                                set: Box::new(ty_elab.clone()),
                                predicate: Box::new(predicate_elab.clone()),
                            };

                            Exp::Exists {
                                set: Box::new(Exp::TypeLift {
                                    superset: Box::new(ty_elab.clone()),
                                    subset: Box::new(subset),
                                }),
                            }
                        }
                        // \exists (x: A | h: P) ... invalid
                        Bind::SubsetWithProof { .. } => {
                            return Err(
                                "Invalid binding in Exists: only Anonymous and Named are allowed"
                                    .to_string(),
                            );
                        }
                    }
                }
                SExp::Take { bind, body } => {
                    let map = match bind {
                        Bind::Anonymous { ty } => {
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            let body_elab =
                                self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                            Exp::Prod {
                                var: Var::dummy(),
                                ty: Box::new(ty_elab),
                                body: Box::new(body_elab),
                            }
                        }
                        Bind::Named { var, ty } => {
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            let var: Var = var.into();
                            let mut bind_var = bind_var.clone();
                            bind_var.push(var.clone());
                            let body_elab =
                                self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                            Exp::Prod {
                                var,
                                ty: Box::new(ty_elab),
                                body: Box::new(body_elab),
                            }
                        }
                        Bind::Subset { var, ty, predicate } => {
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            let var: Var = var.into();
                            let mut bind_var = bind_var.clone();
                            bind_var.push(var.clone());
                            let predicate_elab = self.elab_exp_rec(
                                logger,
                                predicate,
                                reference_var,
                                bind_var.clone(),
                            )?;
                            let body_elab =
                                self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;

                            let subset = Exp::SubSet {
                                var: var.clone(),
                                set: Box::new(ty_elab.clone()),
                                predicate: Box::new(predicate_elab.clone()),
                            };

                            Exp::Prod {
                                var: var.clone(),
                                ty: Box::new(Exp::TypeLift {
                                    superset: Box::new(ty_elab.clone()),
                                    subset: Box::new(subset),
                                }),
                                body: Box::new(body_elab),
                            }
                        }
                        Bind::SubsetWithProof {
                            var,
                            ty,
                            predicate,
                            proof,
                        } => {
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            let var: Var = var.into();
                            let mut bind_var = bind_var.clone();
                            bind_var.push(var.clone());
                            let predicate_elab = self.elab_exp_rec(
                                logger,
                                predicate,
                                reference_var,
                                bind_var.clone(),
                            )?;
                            let proof: Var = proof.into();
                            bind_var.push(proof.clone());
                            let body_elab =
                                self.elab_exp_rec(logger, body, reference_var, bind_var.clone())?;
                            let subset = Exp::SubSet {
                                var: var.clone(),
                                set: Box::new(ty_elab.clone()),
                                predicate: Box::new(predicate_elab.clone()),
                            };

                            Exp::Prod {
                                var: var.clone(),
                                ty: Box::new(Exp::TypeLift {
                                    superset: Box::new(ty_elab.clone()),
                                    subset: Box::new(subset),
                                }),
                                body: Box::new(Exp::Prod {
                                    var: proof,
                                    ty: Box::new(predicate_elab),
                                    body: Box::new(body_elab),
                                }),
                            }
                        }
                    };
                    Exp::Take { map: Box::new(map) }
                }
                SExp::ProofBy(proof_by) => {
                    use kernel::exp::ProveCommandBy;
                    let command: ProveCommandBy = match proof_by {
                        ProofBy::Construct { term } => {
                            let term_elab =
                                self.elab_exp_rec(logger, term, reference_var, bind_var.clone())?;
                            ProveCommandBy::Construct {
                                proof_term: term_elab,
                            }
                        }
                        ProofBy::Exact { term, set } => {
                            let term_elab =
                                self.elab_exp_rec(logger, term, reference_var, bind_var.clone())?;
                            let set_elab =
                                self.elab_exp_rec(logger, set, reference_var, bind_var.clone())?;
                            ProveCommandBy::ExactElem {
                                elem: term_elab,
                                ty: set_elab,
                            }
                        }
                        ProofBy::SubsetElim {
                            superset,
                            subset,
                            elem,
                        } => {
                            let superset_elab = self.elab_exp_rec(
                                logger,
                                superset,
                                reference_var,
                                bind_var.clone(),
                            )?;
                            let subset_elab =
                                self.elab_exp_rec(logger, subset, reference_var, bind_var.clone())?;
                            let elem_elab =
                                self.elab_exp_rec(logger, elem, reference_var, bind_var.clone())?;
                            ProveCommandBy::SubsetElim {
                                superset: superset_elab,
                                subset: subset_elab,
                                elem: elem_elab,
                            }
                        }
                        ProofBy::IdRefl { term } => {
                            let term_elab =
                                self.elab_exp_rec(logger, term, reference_var, bind_var.clone())?;
                            ProveCommandBy::IdRefl { elem: term_elab }
                        }
                        ProofBy::IdElim {
                            left,
                            right,
                            var,
                            ty,
                            predicate,
                        } => {
                            let left_elab =
                                self.elab_exp_rec(logger, left, reference_var, bind_var.clone())?;
                            let right_elab =
                                self.elab_exp_rec(logger, right, reference_var, bind_var.clone())?;
                            let var: Var = var.into();
                            let mut bind_var = bind_var.clone();
                            bind_var.push(var.clone());
                            let ty_elab =
                                self.elab_exp_rec(logger, ty, reference_var, bind_var.clone())?;
                            let predicate_elab = self.elab_exp_rec(
                                logger,
                                predicate,
                                reference_var,
                                bind_var.clone(),
                            )?;
                            ProveCommandBy::IdElim {
                                left: left_elab,
                                right: right_elab,
                                var,
                                ty: ty_elab,
                                predicate: predicate_elab,
                            }
                        }
                        ProofBy::TakeEq {
                            func,
                            domain,
                            codomain,
                            elem,
                        } => {
                            let func_elab =
                                self.elab_exp_rec(logger, func, reference_var, bind_var.clone())?;
                            let domain_elab =
                                self.elab_exp_rec(logger, domain, reference_var, bind_var.clone())?;
                            let codomain_elab = self.elab_exp_rec(
                                logger,
                                codomain,
                                reference_var,
                                bind_var.clone(),
                            )?;
                            let elem_elab =
                                self.elab_exp_rec(logger, elem, reference_var, bind_var.clone())?;
                            ProveCommandBy::TakeEq {
                                func: func_elab,
                                domain: domain_elab,
                                codomain: codomain_elab,
                                elem: elem_elab,
                            }
                        }
                        ProofBy::Axiom(_) => {
                            todo!()
                        }
                    };
                    Exp::ProofTermRaw {
                        command: Box::new(command),
                    }
                }
                SExp::Block(block) => {
                    let Block { declarations, term } = block;
                    let mut term = term.as_ref().clone();
                    for decl in declarations.iter().rev() {
                        match decl {
                            Statement::Fix(items) => {
                                for (var, ty) in items.iter().rev() {
                                    term = SExp::Lam {
                                        bind: Bind::Named {
                                            var: var.clone(),
                                            ty: Box::new(ty.clone()),
                                        },
                                        body: Box::new(term),
                                    };
                                }
                            }
                            Statement::Let { var, ty, body } => {
                                term = SExp::App {
                                    func: Box::new(SExp::Lam {
                                        bind: Bind::Named {
                                            var: var.clone(),
                                            ty: Box::new(ty.clone()),
                                        },
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
                    self.elab_exp_rec(logger, &term, reference_var, bind_var.clone())?
                }
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

impl ModuleResolved {
    fn realize(&self, args: Vec<Exp>) -> ModuleRealized {
        // we need to subst variables in items
        let subst_map: Vec<(Var, Exp)> = self
            .parameters
            .iter()
            .map(|(v, _)| v.clone())
            .zip(args)
            .collect();
        let mut realized_items = vec![];
        for item in self.items.iter() {
            realized_items.push(item.subst(&subst_map));
        }
        ModuleRealized {
            name: self.name.clone(),
            arguments: subst_map.into_iter().map(|(_, e)| e).collect(),
            items: realized_items,
        }
    }
}

pub struct ModuleRealized {
    pub name: Var,
    pub arguments: Vec<Exp>, // v := arg
    pub items: Vec<Item>,
}
