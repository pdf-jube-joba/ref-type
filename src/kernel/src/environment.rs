use crate::{
    exp::{Arena, DefId, DefinedConstant, Exp, InductiveId, ModuleId, ModuleInstanceId, Var},
    inductive::InductiveTypeSpecs,
};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleItem {
    Definition {
        name: String,
        definition: DefId,
    },
    Inductive {
        name: String,
        constructor_names: Vec<String>,
        inductive: InductiveId,
    },
    Record {
        name: String,
        inductive: InductiveId,
    },
}

impl ModuleItem {
    pub fn name(&self) -> &str {
        match self {
            Self::Definition { name, .. }
            | Self::Inductive { name, .. }
            | Self::Record { name, .. } => name,
        }
    }
}

#[derive(Debug)]
pub struct ModuleInstance {
    pub id: ModuleInstanceId,
    pub source: ModuleId,
    pub materialized: ModuleId,
    pub arguments: Vec<(Var, Exp)>,
}

#[derive(Debug)]
pub struct ModuleEnv {
    id: ModuleId,
    name: String,
    parent: Option<ModuleId>,
    children: Vec<ModuleId>,
    parameters: Vec<(Var, Exp)>,
    definitions: Vec<DefinedConstant>,
    inductives: Vec<InductiveTypeSpecs>,
    items: Vec<ModuleItem>,
    names: HashMap<String, usize>,
    instances: Vec<ModuleInstance>,
    imports: HashMap<String, ModuleInstanceId>,
}

impl ModuleEnv {
    fn new(
        id: ModuleId,
        name: String,
        parent: Option<ModuleId>,
        parameters: Vec<(Var, Exp)>,
    ) -> Self {
        Self {
            id,
            name,
            parent,
            children: Vec::new(),
            parameters,
            definitions: Vec::new(),
            inductives: Vec::new(),
            items: Vec::new(),
            names: HashMap::new(),
            instances: Vec::new(),
            imports: HashMap::new(),
        }
    }

    pub fn id(&self) -> ModuleId {
        self.id
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parent(&self) -> Option<ModuleId> {
        self.parent
    }

    pub fn children(&self) -> &[ModuleId] {
        &self.children
    }

    pub fn parameters(&self) -> &[(Var, Exp)] {
        &self.parameters
    }

    pub fn definitions(&self) -> &[DefinedConstant] {
        &self.definitions
    }

    pub fn inductives(&self) -> &[InductiveTypeSpecs] {
        &self.inductives
    }

    pub fn items(&self) -> &[ModuleItem] {
        &self.items
    }

    pub fn item(&self, name: &str) -> Option<&ModuleItem> {
        self.names.get(name).map(|index| &self.items[*index])
    }

    pub fn instances(&self) -> &[ModuleInstance] {
        &self.instances
    }

    pub fn import(&self, name: &str) -> Option<ModuleInstanceId> {
        self.imports.get(name).copied()
    }
}

#[derive(Debug)]
pub struct CrateEnv {
    arena: Arena,
    modules: Vec<ModuleEnv>,
}

impl Default for CrateEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl CrateEnv {
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            modules: vec![ModuleEnv::new(ModuleId(0), "root".into(), None, vec![])],
        }
    }

    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    pub fn arena_mut(&mut self) -> &mut Arena {
        &mut self.arena
    }

    pub fn root_module(&self) -> ModuleId {
        ModuleId(0)
    }

    pub fn add_module(&mut self) -> ModuleId {
        self.add_module_entry("<instance>".into(), None, vec![])
    }

    pub fn add_child_module(
        &mut self,
        parent: ModuleId,
        name: String,
        parameters: Vec<(Var, Exp)>,
    ) -> Result<ModuleId, String> {
        Ok(self.add_module_entry(name, Some(parent), parameters))
    }

    pub fn publish_child_module(&mut self, child: ModuleId) -> Result<(), String> {
        let parent = self.module(child).parent.ok_or_else(|| {
            "Root or materialized module cannot be published as a child".to_string()
        })?;
        self.module_mut(parent).children.push(child);
        Ok(())
    }

    fn add_module_entry(
        &mut self,
        name: String,
        parent: Option<ModuleId>,
        parameters: Vec<(Var, Exp)>,
    ) -> ModuleId {
        let index = u32::try_from(self.modules.len()).expect("module table exceeded u32::MAX");
        let id = ModuleId(index);
        self.modules
            .push(ModuleEnv::new(id, name, parent, parameters));
        id
    }

    pub fn module(&self, id: ModuleId) -> &ModuleEnv {
        &self.modules[id.index()]
    }

    pub fn module_mut(&mut self, id: ModuleId) -> &mut ModuleEnv {
        &mut self.modules[id.index()]
    }

    pub fn add_definition(&mut self, module: ModuleId, definition: DefinedConstant) -> DefId {
        let module_env = self.module_mut(module);
        let index = u32::try_from(module_env.definitions.len())
            .expect("module definition table exceeded u32::MAX");
        module_env.definitions.push(definition);
        DefId { module, index }
    }

    pub fn definition(&self, id: DefId) -> &DefinedConstant {
        &self.module(id.module).definitions[id.index as usize]
    }

    pub fn add_inductive(
        &mut self,
        module: ModuleId,
        inductive: InductiveTypeSpecs,
    ) -> InductiveId {
        let module_env = self.module_mut(module);
        let index = u32::try_from(module_env.inductives.len())
            .expect("module inductive table exceeded u32::MAX");
        module_env.inductives.push(inductive);
        InductiveId { module, index }
    }

    pub fn inductive(&self, id: InductiveId) -> &InductiveTypeSpecs {
        &self.module(id.module).inductives[id.index as usize]
    }

    pub fn add_instance(
        &mut self,
        owner: ModuleId,
        source: ModuleId,
        materialized: ModuleId,
        arguments: Vec<(Var, Exp)>,
    ) -> ModuleInstanceId {
        let owner_env = self.module_mut(owner);
        let local = u32::try_from(owner_env.instances.len())
            .expect("module instance table exceeded u32::MAX");
        let id = ModuleInstanceId { owner, local };
        owner_env.instances.push(ModuleInstance {
            id,
            source,
            materialized,
            arguments,
        });
        id
    }

    pub fn instance(&self, id: ModuleInstanceId) -> &ModuleInstance {
        &self.module(id.owner).instances[id.local as usize]
    }

    pub fn publish_item(&mut self, module: ModuleId, item: ModuleItem) -> Result<(), String> {
        let module = self.module_mut(module);
        let name = item.name().to_owned();
        if module.names.contains_key(&name) {
            return Err(format!("Module item '{name}' is already defined"));
        }
        let index = module.items.len();
        module.items.push(item);
        module.names.insert(name, index);
        Ok(())
    }

    pub fn publish_import(
        &mut self,
        module: ModuleId,
        name: String,
        instance: ModuleInstanceId,
    ) -> Result<(), String> {
        let module = self.module_mut(module);
        if module.imports.contains_key(&name) {
            return Err(format!("Module import '{name}' is already defined"));
        }
        module.imports.insert(name, instance);
        Ok(())
    }

    pub fn record_for_inductive(&self, inductive: InductiveId) -> Option<&ModuleItem> {
        self.modules.iter().flat_map(ModuleEnv::items).find(|item| {
            matches!(item, ModuleItem::Record { inductive: candidate, .. } if *candidate == inductive)
        })
    }
}
