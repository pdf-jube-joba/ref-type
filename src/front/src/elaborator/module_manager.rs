use crate::syntax::Identifier;
use kernel::exp::{DefinedConstant, Exp, Var};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct RecordSpecs {
    pub name: Identifier,
    pub field_names: Vec<Identifier>,
    pub rc_spec_as_indtype: Rc<kernel::inductive::InductiveTypeSpecs>,
}

#[derive(Debug, Clone)]
pub enum ModuleItemAccessible {
    Definition {
        rc: Rc<kernel::exp::DefinedConstant>,
    },
    Inductive {
        type_name: Identifier,
        ctor_names: Vec<Identifier>,
        ind_defs: Rc<kernel::inductive::InductiveTypeSpecs>,
    },
    // we use inductive type to represent record type
    Record(RecordSpecs),
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

#[derive(Debug, Clone)]
pub struct InstantiatedModule {
    // what is substituted for parameters
    pub parameters_instantiated: Vec<(Var, Exp)>,
    pub items: Vec<ModuleItemAccessible>,
}

pub enum ItemAccessResult {
    Definition {
        rc: Rc<DefinedConstant>,
    },
    Inductive {
        ind_defs: Rc<kernel::inductive::InductiveTypeSpecs>,
    },
    Record(RecordSpecs),
    Expression {
        exp: Exp,
    },
}

impl InstantiatedModule {
    pub fn get_item(&self, name: &Identifier) -> Option<ItemAccessResult> {
        for item in self.items.iter() {
            match item {
                ModuleItemAccessible::Definition { rc } => {
                    if rc.as_ref().name.as_str() == name.0.as_str() {
                        return Some(ItemAccessResult::Definition { rc: Rc::clone(rc) });
                    }
                }
                ModuleItemAccessible::Inductive {
                    ind_defs,
                    type_name,
                    ctor_names: _,
                } => {
                    if type_name.as_str() == name.0.as_str() {
                        return Some(ItemAccessResult::Inductive {
                            ind_defs: Rc::clone(ind_defs),
                        });
                    }
                }
                ModuleItemAccessible::Record(record_specs) => {
                    if record_specs.name.as_str() == name.0.as_str() {
                        return Some(ItemAccessResult::Record(record_specs.clone()));
                    }
                }
            }
        }
        for (var, exp) in self.parameters_instantiated.iter() {
            if var.as_str() == name.0.as_str() {
                return Some(ItemAccessResult::Expression { exp: exp.clone() });
            }
        }
        None
    }
}

pub struct InstantiateResult {
    pub instantiated_module: InstantiatedModule,
    pub need_to_type_check: Vec<(String, Exp, Exp)>,
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
    pub fn moveto_root(&mut self) {
        self.current = 0;
    }

    pub fn current_module_as_instantiated(&self) -> InstantiatedModule {
        let ModuleElaborated {
            name: _,
            parameters: _,
            items,
            child_modules: _,
            parent_module: _,
        } = self.modules.get(self.current).unwrap();

        // reflective setting of parameters
        // instance : v := "v it self"
        let pms = self
            .current_context()
            .into_iter()
            .flat_map(|(_, params)| {
                params
                    .into_iter()
                    .map(|(v, _)| (v.clone(), Exp::Var(v.clone())))
            })
            .collect();

        InstantiatedModule {
            parameters_instantiated: pms,
            items: items.clone(),
        }
    }

    pub fn current_context(&self) -> Vec<(String, Vec<(Var, Exp)>)> {
        let mut context = vec![];
        let mut index = self.current;
        loop {
            let module = &self.modules[index];
            let params = module
                .parameters
                .iter()
                .map(|(var, ty)| (var.clone(), ty.clone()))
                .collect();
            context.push((module.name.clone(), params));
            if let Some(parent_index) = module.parent_module {
                index = parent_index;
            } else {
                break;
            }
        }
        context.reverse();
        context
    }
    pub fn current_path(&self) -> Vec<String> {
        let mut path = vec![];
        let mut index = self.current;
        loop {
            let module = &self.modules[index];
            path.push(module.name.clone());
            if let Some(parent_index) = module.parent_module {
                index = parent_index;
            } else {
                break;
            }
        }
        path.reverse();
        path
    }

    pub fn add_def(&mut self, def: DefinedConstant) {
        let rc = Rc::new(def);
        let item = ModuleItemAccessible::Definition { rc };
        self.modules[self.current].items.push(item);
    }
    pub fn add_inductive(&mut self, ind_defs: kernel::inductive::InductiveTypeSpecs) {
        let rc = Rc::new(ind_defs);
        let item = ModuleItemAccessible::Inductive { ind_defs: rc };
        self.modules[self.current].items.push(item);
    }
    pub fn add_record(&mut self, record_specs: RecordSpecs) {
        let item = ModuleItemAccessible::Record(record_specs);
        self.modules[self.current].items.push(item);
    }

    fn access_module(
        &self,
        mut from: usize,
        args: Vec<(Identifier, Vec<(Identifier, Exp)>)>,
    ) -> Result<InstantiateResult, String> {
        // we delegate "type checking" of arguments to the caller
        let mut need_to_type_check = vec![];
        // to instantiate, we need to subst items in instantiated module
        let mut subst_mapping_accum = vec![];

        for (child_name, args) in args {
            let child_idx = self.modules[from]
                .child_modules
                .iter()
                .find(|&&idx| self.modules[idx].name == child_name.0)
                .ok_or_else(|| {
                    format!(
                        "Child module '{}' not found in module '{}'",
                        child_name, self.modules[from].name
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
            for ((arg_name, arg), (param_var, ty)) in
                args.iter().zip(child_module.parameters.iter())
            {
                if arg_name.as_str() != param_var.as_str() {
                    return Err(format!(
                        "Argument name mismatch for module '{}': expected '{}', got '{}'",
                        child_module.name,
                        param_var.as_str(),
                        arg_name.as_str()
                    ));
                }
                let ty_subst = ty.subst(&subst_mapping_accum);
                need_to_type_check.push((param_var.to_string(), arg.clone(), ty_subst));
                subst_mapping_accum.push((param_var.clone(), arg.clone()));
            }

            from = *child_idx;
        }
        // instantiate with accumulated substitutions
        let instantiated_items = self.modules[from]
            .items
            .iter()
            .map(|item| match item {
                ModuleItemAccessible::Definition { rc } => {
                    let DefinedConstant {
                        name,
                        ty,
                        body: inner,
                    } = rc.as_ref().clone();
                    let instantiated_ty = ty.subst(&subst_mapping_accum);
                    let instantiated_inner = inner.subst(&subst_mapping_accum);
                    let instantiated_def = DefinedConstant {
                        name,
                        ty: instantiated_ty,
                        body: instantiated_inner,
                    };
                    ModuleItemAccessible::Definition {
                        rc: Rc::new(instantiated_def),
                    }
                }
                ModuleItemAccessible::Inductive { ind_defs } => {
                    let ind = ind_defs.as_ref().clone();
                    let instantiated_ind_defs = ind.subst(&subst_mapping_accum);
                    ModuleItemAccessible::Inductive {
                        ind_defs: Rc::new(instantiated_ind_defs),
                    }
                }
                _ => {
                    todo!()
                }
            })
            .collect();

        let module_instantiated = InstantiatedModule {
            parameters_instantiated: subst_mapping_accum,
            items: instantiated_items,
        };

        Ok(InstantiateResult {
            instantiated_module: module_instantiated,
            need_to_type_check,
        })
    }

    pub fn access_from_root(
        &self,
        args: Vec<(Identifier, Vec<(Identifier, Exp)>)>,
    ) -> Result<InstantiateResult, String> {
        self.access_module(0, args)
    }
    pub fn access_from_current(
        &self,
        back_parent: usize,
        args: Vec<(Identifier, Vec<(Identifier, Exp)>)>,
    ) -> Result<InstantiateResult, String> {
        let mut index = self.current;
        for _ in 0..back_parent {
            if let Some(parent_index) = self.modules[index].parent_module {
                index = parent_index;
            } else {
                return Err("Cannot go back parent: already at root module".to_string());
            }
        }
        self.access_module(index, args)
    }
}
