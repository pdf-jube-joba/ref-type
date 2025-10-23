use std::collections::HashMap;

use either::Either;
// elaborator's state
// - name resolution (binding variables and bindee)
// - macro expansion
use kernel::{
    exp::{Exp, Var},
    inductive::InductiveTypeSpecs,
};

use crate::syntax::{Identifier, MacroToken};

#[derive(Debug)]
pub struct Elaborator {
    mod_infos: Vec<ModInfo>,
    current_processing_mod: usize, // index of elaborator's mod_infos
}

impl Elaborator {
    pub fn new() -> Self {
        Self {
            mod_infos: Vec::new(),
            current_processing_mod: 0,
        }
    }
}

#[derive(Debug)]
pub struct AbsModInstantiation {
    idx: usize,
    arguments: Vec<Exp>,
}

#[derive(Debug)]
pub struct ModInfo {
    name: String,
    parameters: Vec<(String, Exp)>,
    definitions: HashMap<String, (Exp, Exp)>,
    inductive_types: HashMap<String, (Vec<String>, std::rc::Rc<InductiveTypeSpecs>)>, // name of inductive type => (names of constructors, specs)
    imports: HashMap<String, Vec<Vec<Exp>>>, // module name to index of elaborator's mod_infos
    parent_module: Option<usize>,            // index of elaborator's mod_infos
    child_modules: HashMap<String, usize>,   // module name to index of elaborator's mod_infos
    math_macro_decls: Vec<(
        Vec<Either<MacroToken, Identifier>>,
        Vec<Either<Exp, Identifier>>,
    )>,
    use_macro_decls: HashMap<String, (Vec<Either<MacroToken, Identifier>>, Vec<Identifier>)>,
}
