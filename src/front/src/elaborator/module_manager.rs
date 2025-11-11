use crate::syntax::{self, Identifier};
use kernel::exp::{DefinedConstant, Exp, Var};

pub enum ModuleItemAccessible {
    Definition {
        rc: std::rc::Rc<kernel::exp::DefinedConstant>,
    },
    Inductive {
        ind_defs: std::rc::Rc<kernel::inductive::InductiveTypeSpecs>,
    },
}

pub struct ModuleElaborated {
    pub name: String,
    pub parameters: Vec<(Var, Exp)>,
    pub items: Vec<ModuleItemAccessible>,
    // index of modules in ModuleManager.modules
    pub child_modules: Vec<usize>,
    // index of parent module in ModuleManager.modules
    // only None for the root module
    pub parent_module: Option<usize>,
}

pub struct ModuleInstantiated {
    pub name: String,
    pub items: Vec<ModuleItemAccessible>,
}

pub enum AccessPath {
    FromCurrent {
        back_parent: usize,
        children_args: Vec<(Identifier, Vec<(Identifier, Exp)>)>,
    },
    FromRoot {
        children_args: Vec<(Identifier, Vec<(Identifier, Exp)>)>,
    },
}

pub struct AccessResult {
    pub module_index: usize,
    pub instantiated_module: ModuleInstantiated,
    pub need_to_type_check: Vec<(String, Vec<(String, Exp, Exp)>)>,
}

pub struct ModuleManager {
    modules: Vec<ModuleElaborated>,
    current: usize,
}

impl ModuleManager {
    pub fn new() -> Self {
        let root_module = ModuleElaborated {
            name: "root".to_string(),
            parameters: vec![],
            items: vec![],
            child_modules: vec![],
            parent_module: None,
        };
        ModuleManager {
            modules: vec![root_module],
            current: 0,
        }
    }
    pub fn add_child_and_moveto(&mut self, module_name: String, parameters: Vec<(Var, Exp)>) {
        let parent_index = self.current;
        let new_module = ModuleElaborated {
            name: module_name,
            parameters,
            items: vec![],
            child_modules: vec![],
            parent_module: Some(parent_index),
        };
        self.modules.push(new_module);
        let new_index = self.modules.len() - 1;
        self.modules[parent_index].child_modules.push(new_index);
        self.current = new_index;
    }
    pub fn moveto_parent(&mut self) {
        if let Some(parent_index) = self.modules[self.current].parent_module {
            self.current = parent_index;
        }
    }
    pub fn add_def(&mut self, def: DefinedConstant) {
        let rc = std::rc::Rc::new(def);
        let item = ModuleItemAccessible::Definition { rc };
        self.modules[self.current].items.push(item);
    }
    pub fn add_inductive(&mut self, ind_defs: kernel::inductive::InductiveTypeSpecs) {
        let rc = std::rc::Rc::new(ind_defs);
        let item = ModuleItemAccessible::Inductive { ind_defs: rc };
        self.modules[self.current].items.push(item);
    }
    pub fn access_module(&self, access_path: &AccessPath) -> Result<AccessResult, String> {
        let (mut start, children_args) = match access_path {
            AccessPath::FromCurrent {
                back_parent,
                children_args,
            } => {
                let mut index = self.current;
                for _ in 0..*back_parent {
                    if let Some(parent_index) = self.modules[index].parent_module {
                        index = parent_index;
                    } else {
                        return Err("Invalid back_parent in AccessPath::FromCurrent".to_string());
                    }
                }
                (index, children_args)
            }
            AccessPath::FromRoot { children_args } => (0, children_args),
        };
        let mut need_to_type_check = vec![];
        let mut subst_mapping_accum = vec![];

        for (child_name, args) in children_args {
            let child_idx = self.modules[start]
                .child_modules
                .iter()
                .find(|&&idx| self.modules[idx].name == *child_name.0)
                .ok_or_else(|| {
                    format!(
                        "Child module '{}' not found in module '{}'",
                        child_name, self.modules[start].name
                    )
                })?;
            let child_module = &self.modules[*child_idx];
            // check arguments length and name
            if args.len() != child_module.parameters.len() {
                return Err(format!(
                    "Argument length mismatch for module '{}': expected {}, got {}",
                    child_module.name,
                    child_module.parameters.len(),
                    args.len()
                ));
            }
            let mut need_to_type_check_child = vec![];
            for ((arg_name, ty), (param_var, arg)) in
                args.iter().zip(child_module.parameters.iter())
            {
                if arg_name.0 != param_var.as_str() {
                    return Err(format!(
                        "Argument name mismatch for module '{}': expected '{}', got '{}'",
                        child_module.name,
                        param_var.as_str(),
                        arg_name.0
                    ));
                }

                let ty_subst = ty.subst(&subst_mapping_accum);

                need_to_type_check_child.push((
                    param_var.to_string(),
                    arg.clone(),
                    ty_subst.clone(),
                ));
                subst_mapping_accum.push((param_var.clone(), arg.clone()));
            }
            need_to_type_check.push((child_module.name.clone(), need_to_type_check_child));

            start = *child_idx;
        }

        // instantiate with accumulated substitutions
        let instantiated_items = self.modules[start]
            .items
            .iter()
            .map(|item| match item {
                ModuleItemAccessible::Definition { rc } => {
                    let DefinedConstant { name, ty, inner } = rc.as_ref().clone();
                    let instantiated_ty = ty.subst(&subst_mapping_accum);
                    let instantiated_inner = inner.subst(&subst_mapping_accum);
                    let instantiated_def = DefinedConstant {
                        name,
                        ty: instantiated_ty,
                        inner: instantiated_inner,
                    };
                    ModuleItemAccessible::Definition {
                        rc: std::rc::Rc::new(instantiated_def),
                    }
                }
                ModuleItemAccessible::Inductive { ind_defs } => {
                    let ind = ind_defs.as_ref().clone();
                    let instantiated_ind_defs = ind.subst(&subst_mapping_accum);
                    ModuleItemAccessible::Inductive {
                        ind_defs: std::rc::Rc::new(instantiated_ind_defs),
                    }
                }
            })
            .collect();

        let module_instantiated = ModuleInstantiated {
            name: self.modules[start].name.clone(),
            items: instantiated_items,
        };

        Ok(AccessResult {
            module_index: start,
            instantiated_module: module_instantiated,
            need_to_type_check,
        })
    }
}
