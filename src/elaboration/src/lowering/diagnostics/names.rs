use crate::raw::{
    environment::{CrateEnv, DefinedConstant, ModuleItem},
    ids::{DefId, ModuleId},
    printing::format_module,
};
use rustc_hash::FxHashMap;

pub(super) struct Names {
    pub definitions: FxHashMap<kernel::ids::DefinitionId, String>,
    pub contextual_parameters: FxHashMap<kernel::ids::DefinitionId, usize>,
    pub inductives: FxHashMap<kernel::ids::InductiveId, (String, Vec<String>)>,
    pub datatypes: FxHashMap<kernel::ids::ProgramInductiveId, (String, Vec<String>)>,
}

impl Names {
    pub fn new(env: &CrateEnv) -> Self {
        let mut names = Self {
            definitions: FxHashMap::default(),
            contextual_parameters: FxHashMap::default(),
            inductives: FxHashMap::default(),
            datatypes: FxHashMap::default(),
        };
        let mut modules: Vec<_> = env
            .definition_ids()
            .into_iter()
            .map(|id| id.module)
            .chain(env.inductive_ids().into_iter().map(|id| id.module))
            .chain(env.datatype_ids().into_iter().map(|id| id.module))
            .collect();
        modules.sort_by_key(|id| id.0);
        modules.dedup();
        for module in modules {
            names.module(env, module);
        }
        names
    }

    fn module(&mut self, env: &CrateEnv, module: ModuleId) {
        let path = format!("\\{}", format_module(env, module));
        for item in env.module(module).items() {
            let name = format!("{path}.{}", item.name());
            let associated = match item {
                ModuleItem::Definition { definition, .. } => {
                    if definition.module != module {
                        continue;
                    }
                    self.definition(env, *definition, name);
                    continue;
                }
                ModuleItem::Inductive {
                    inductive,
                    constructor_names,
                    associated_definitions,
                    ..
                } => {
                    if inductive.module != module {
                        continue;
                    }
                    self.inductives.insert(
                        (*inductive).into(),
                        (name.clone(), constructor_names.clone()),
                    );
                    associated_definitions
                }
                ModuleItem::Record {
                    inductive,
                    associated_definitions,
                    ..
                } => {
                    if inductive.module != module {
                        continue;
                    }
                    self.inductives
                        .insert((*inductive).into(), (name.clone(), vec![]));
                    associated_definitions
                }
                ModuleItem::ProgramInductive {
                    inductive,
                    reflected,
                    constructor_names,
                    associated_definitions,
                    ..
                } => {
                    if inductive.module != module {
                        continue;
                    }
                    self.datatypes.insert(
                        (*inductive).into(),
                        (name.clone(), constructor_names.clone()),
                    );
                    self.inductives.insert(
                        (*reflected).into(),
                        (format!("{name}^"), constructor_names.clone()),
                    );
                    associated_definitions
                }
            };
            for (field, id) in associated {
                self.definition(env, *id, format!("{name}::{field}"));
            }
        }
    }

    fn definition(&mut self, env: &CrateEnv, definition: DefId, name: String) {
        if let Some(&id) = env.kernel_definitions.borrow().get(&definition) {
            self.definitions.insert(id, name);
            if let DefinedConstant::Contextual { parameters, .. } = env.definition(definition) {
                self.contextual_parameters.insert(id, parameters.len());
            }
        }
    }
}
