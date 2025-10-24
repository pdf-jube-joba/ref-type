use std::collections::HashMap;

use either::Either;
// elaborator's state
// - name resolution (binding variables and bindee)
// - macro expansion
use kernel::{
    calculus::{subst, subst_map},
    checker::Checker,
    exp::{Derivation, Exp, Var},
    inductive::InductiveTypeSpecs,
};

use crate::syntax::{self, Identifier, MacroToken, ModuleInstantiated};

#[derive(Debug)]
pub struct Elaborator {
    mod_infos: Vec<ModInfo>,
    current_processing_mod: usize, // index of elaborator's mod_infos
    contexts_stack: Vec<Vec<(Var, Exp)>>,
    history: Vec<Either<String, Derivation>>, // logger
}

impl Elaborator {
    pub fn new() -> Self {
        Self {
            mod_infos: Vec::new(),
            current_processing_mod: 0,
            contexts_stack: Vec::new(),
            history: Vec::new(),
        }
    }
    pub fn find_mod_from_name(&self, name: &Identifier) -> Option<usize> {
        self.mod_infos
            .iter()
            .position(|mod_info| mod_info.name == *name)
    }
    pub fn entry_str(&mut self, action: String) {
        self.history.push(Either::Left(action));
    }
    pub fn push_derivation(&mut self, derivation: Derivation) {
        self.history.push(Either::Right(derivation));
    }
    pub fn push_derivations(&mut self, derivations: Vec<Derivation>) {
        for derivation in derivations {
            self.push_derivation(derivation);
        }
    }

    pub fn resolve_mod_path(
        &mut self,
        path: &syntax::ModPath,
    ) -> Result<AbsModInstantiation, String> {
        self.entry_str(format!("resolve_mod_path {:?}", path));

        // prepare a checker with the current contexts
        let mut new_checker = kernel::checker::Checker::default();
        for (v, t) in self.contexts_stack.iter().flatten() {
            new_checker.push(v.clone(), t.clone()).unwrap();
        }
        match path {
            syntax::ModPath::Root(module_instantiateds) => {
                if module_instantiateds.is_empty() {
                    return Err("empty module path".to_string());
                }

                // current parameters to checker
                let mut checker = Checker::default();
                for (v, t) in self.contexts_stack.iter().flatten() {
                    checker.push(v.clone(), t.clone()).unwrap();
                }

                let mut idx = 0; // guard value (will be overwritten)
                let mut arguments_substmap = vec![];

                for module_instantiated in module_instantiateds {
                    let ModuleInstantiated {
                        module_name,
                        arguments,
                    } = module_instantiated;

                    let Some(modidx) = self.find_mod_from_name(module_name) else {
                        return Err(format!("module {} not found", module_name));
                    };

                    for (name, v, ty_not_substed) in self.mod_infos[modidx].parameters.clone() {
                        let mut derivations = vec![];

                        let Some((_, subst_exp)) =
                            arguments.iter().find(|(arg_name, _)| *arg_name == name)
                        else {
                            return Err(format!(
                                "missing argument for parameter {} of module {}",
                                name, module_name
                            ));
                        };

                        let Ok(subst_exp) = self.surface_to_exp(subst_exp) else {
                            return Err(format!(
                                "failed to elaborate argument for parameter {} of module {}",
                                name, module_name
                            ));
                        };

                        let ty_substed = subst_map(&ty_not_substed, &arguments_substmap);

                        match checker.check(&subst_exp, &ty_substed) {
                            Ok(derivation) => {
                                derivations.push(derivation);
                                arguments_substmap.push((v.clone(), subst_exp.clone()));
                            }
                            Err(derivation) => {
                                derivations.push(derivation);
                                self.push_derivations(derivations);
                                return Err(format!(
                                    "argument for parameter {} of module {} has incorrect type",
                                    name, module_name
                                ));
                            }
                        }

                        idx = modidx;
                    }
                }

                Ok(AbsModInstantiation {
                    idx,
                    arguments_substmap,
                })
            }
        }
    }
    pub fn surface_to_exp(&mut self, surface: &syntax::SExp) -> Result<Exp, String> {
        let mut current_bind: HashMap<Identifier, Var> = HashMap::new();
        self.surface_to_exp_rec(surface, &mut current_bind)
    }
    pub fn surface_to_exp_rec(
        &mut self,
        surface: &syntax::SExp,
        current_bind: &mut HashMap<Identifier, Var>, // local to expression, not module
    ) -> Result<Exp, String> {
        self.entry_str(format!("surface_to_exp {:?}", surface));
        match surface {
            syntax::SExp::ModAccessDef { path, name } => {
                let Ok(absmod) = self.resolve_mod_path(path) else {
                    return Err(format!("failed to resolve module path {:?}", path));
                };
                let mod_info = &self.mod_infos[absmod.idx];

                let Some((_, body)) = mod_info.find_definition(name) else {
                    return Err(format!(
                        "definition {} not found in module {:?}",
                        name, path
                    ));
                };

                let body_substed = subst_map(body, &absmod.arguments_substmap);

                Ok(body_substed)
            }
            syntax::SExp::MathMacro { tokens } => todo!("currently unimplemented"),
            syntax::SExp::NamedMacro { path, name, tokens } => todo!("currently unimplemented"),
            syntax::SExp::Where { exp, clauses } => todo!("currently unimplemented"),
            syntax::SExp::WithProof { exp, proofs } => todo!("currently unimplemented"),
            syntax::SExp::Sort(sort) => Ok(Exp::Sort(sort.clone())),
            syntax::SExp::Var(identifier) => {
                if let Some(var) = current_bind.get(identifier) {
                    Ok(Exp::Var(var.clone()))
                } else {
                    Err(format!("unbound variable {}", identifier))
                }
            }
            syntax::SExp::Prod { bind, body } => {
                let syntax::Bind { var, ty, predicate } = bind;

                let elab_ty = self.surface_to_exp_rec(ty, current_bind)?;

                match var {
                    Some(name) => {
                        let new_var = Var::new(&name.0);
                        current_bind.insert(name.clone(), new_var.clone());
                    }
                    None => {}
                };

                let elab_body = self.surface_to_exp_rec(body, current_bind)?;

                todo!()
            }
            syntax::SExp::Lam { bind, body } => todo!(),
            syntax::SExp::App { func, arg, piped } => todo!(),
            syntax::SExp::Annotation { exp, ty } => todo!(),
            syntax::SExp::IndType {
                path,
                ind_type_name,
            } => todo!(),
            syntax::SExp::IndCtor {
                path,
                ind_type_name,
                constructor_name,
            } => todo!(),
            syntax::SExp::IndElim {
                path,
                ind_type_name,
                eliminated_exp,
                return_type,
                cases,
            } => todo!(),
            syntax::SExp::Proof { term } => todo!(),
            syntax::SExp::Pow { power } => todo!(),
            syntax::SExp::Sub { var, ty, predicate } => todo!(),
            syntax::SExp::Pred {
                superset,
                subset,
                elem,
            } => todo!(),
            syntax::SExp::TypeLift { superset, subset } => todo!(),
            syntax::SExp::Equal { left, right } => todo!(),
            syntax::SExp::Exists { bind } => todo!(),
            syntax::SExp::Take { bind, body } => todo!(),
            syntax::SExp::ProofBy(proof_by) => todo!(),
            syntax::SExp::Block(block) => todo!(),
        }
    }
}

#[derive(Debug)]
pub struct AbsModInstantiation {
    idx: usize,
    arguments_substmap: Vec<(Var, Exp)>,
}

#[derive(Debug)]
pub struct ModInfo {
    name: Identifier,
    // parent of this module
    parent_module: Option<usize>, // index of elaborator's mod_infos
    // name and type of parameter
    parameters: Vec<(Identifier, Var, Exp)>,
    // included declarations
    definitions: HashMap<Identifier, (Exp, Exp)>,
    inductive_types: HashMap<Identifier, (Vec<Identifier>, std::rc::Rc<InductiveTypeSpecs>)>, // name of inductive type => (names of constructors, specs)
    child_modules: Vec<usize>, // module name to index of elaborator's mod_infos
    imports: HashMap<Identifier, Vec<Vec<Exp>>>, // module name to index of elaborator's mod_infos
    math_macro_decls: Vec<(
        Vec<Either<MacroToken, Identifier>>,
        Vec<Either<Exp, Identifier>>,
    )>,
    use_macro_decls: HashMap<Identifier, (Vec<Either<MacroToken, Identifier>>, Vec<Identifier>)>,
}

impl ModInfo {
    pub fn find_definition(&self, name: &Identifier) -> Option<&(Exp, Exp)> {
        self.definitions.get(name)
    }
}
