use std::collections::HashMap;

use either::Either;
// elaborator's state
// - name resolution (binding variables and bindee)
// - macro expansion
use kernel::{
    exp::{Exp, Var},
    inductive::InductiveTypeSpecs,
};

use crate::syntax::{self, Identifier, MacroToken};

pub struct ElaborationResult {
    pub derivations: Vec<kernel::exp::Derivation>,
}

#[derive(Debug)]
pub struct Elaborator {
    mod_infos: Vec<ModInfo>,
    current_processing_mod: usize, // index of elaborator's mod_infos
    checker: kernel::checker::Checker,
    contexts_stack: Vec<Vec<(Var, Exp)>>,
}

impl Elaborator {
    pub fn new() -> Self {
        Self {
            mod_infos: Vec::new(),
            checker: kernel::checker::Checker::default(),
            current_processing_mod: 0,
            contexts_stack: Vec::new(),
        }
    }
    pub fn find_mod_from_name(&self, name: &Identifier) -> Option<&ModInfo> {
        self.mod_infos
            .iter()
            .find(|mod_info| mod_info.name == *name)
    }
    pub fn resolve_mod_path(
        &self,
        path: &syntax::ModPath,
    ) -> (ElaborationResult, Result<AbsModInstantiation, String>) {
        let mut arguments_substmap = vec![];
        let mut derivations = vec![];
        match path {
            syntax::ModPath::Root(module_instantiateds) => {
                for mod_inst in module_instantiateds {
                    let syntax::ModuleInstantiated {
                        module_name,
                        arguments,
                    } = mod_inst;
                    let Some(modinfo) = self.find_mod_from_name(module_name) else {
                        return (
                            ElaborationResult { derivations },
                            Err(format!("module not found {module_name}")),
                        );
                    };
                    for (name, v, ty) in &modinfo.parameters {
                        let Some((_, arg_exp)) =
                            arguments.iter().find(|(arg_name, _)| arg_name == name)
                        else {
                            return (
                                ElaborationResult { derivations },
                                Err(format!("argument not provided for parameter {name}")),
                            );
                        };
                        // self.checker.check(arg_exp, ty);
                        arguments_substmap.push((v, arg_exp.clone()));
                    }
                }

                todo!()
            }
            syntax::ModPath::Current(_, module_instantiateds) => todo!(),
            syntax::ModPath::Name(identifier, module_instantiateds) => todo!(),
        }
    }
    pub fn resolve_mod_path_def(
        &self,
        path: &syntax::ModPath,
        item: &Identifier,
    ) -> (ElaborationResult, Result<Exp, String>) {
        todo!()
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
    definitions: HashMap<String, (Exp, Exp)>,
    inductive_types: HashMap<Identifier, (Vec<String>, std::rc::Rc<InductiveTypeSpecs>)>, // name of inductive type => (names of constructors, specs)
    child_modules: HashMap<Identifier, usize>, // module name to index of elaborator's mod_infos
    imports: HashMap<String, Vec<Vec<Exp>>>,   // module name to index of elaborator's mod_infos
    math_macro_decls: Vec<(
        Vec<Either<MacroToken, Identifier>>,
        Vec<Either<Exp, Identifier>>,
    )>,
    use_macro_decls: HashMap<String, (Vec<Either<MacroToken, Identifier>>, Vec<Identifier>)>,
}
