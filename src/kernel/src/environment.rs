use crate::{
    exp::{
        Arena, DefId, DefinedConstant, Exp, InductiveId, ModuleId, ModuleInstanceId, ModuleParamId,
        SymbolId,
    },
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

#[derive(Debug, Clone)]
pub struct ModuleParameter {
    pub name: SymbolId,
    pub ty: Exp,
}

impl ModuleParameter {
    pub fn id(&self, module: ModuleId, position: u32) -> ModuleParamId {
        ModuleParamId { module, position }
    }
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
    pub arguments: Vec<(ModuleParamId, Exp)>,
}

#[derive(Debug)]
pub struct ModuleEnv {
    id: ModuleId,
    name: String,
    parent: Option<ModuleId>,
    children: Vec<ModuleId>,
    parameters: Vec<ModuleParameter>,
    definitions: Vec<DefinedConstant>,
    inductives: Vec<Option<InductiveTypeSpecs>>,
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
        parameters: Vec<ModuleParameter>,
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

    pub fn parameters(&self) -> &[ModuleParameter] {
        &self.parameters
    }

    pub fn definitions(&self) -> &[DefinedConstant] {
        &self.definitions
    }

    pub fn inductives(&self) -> &[Option<InductiveTypeSpecs>] {
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
    symbols: Vec<String>,
    symbol_ids: HashMap<String, SymbolId>,
    modules: Vec<ModuleEnv>,
}

impl Default for CrateEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl CrateEnv {
    pub fn new() -> Self {
        let anonymous = "_".to_string();
        let root = "root".to_string();
        let mut symbol_ids = HashMap::new();
        symbol_ids.insert(anonymous.clone(), SymbolId::ANONYMOUS);
        symbol_ids.insert(root.clone(), SymbolId(1));
        Self {
            arena: Arena::new(),
            symbols: vec![anonymous, root],
            symbol_ids,
            modules: vec![ModuleEnv::new(ModuleId(0), "root".into(), None, vec![])],
        }
    }

    pub fn intern(&mut self, name: &str) -> SymbolId {
        if let Some(symbol) = self.symbol_ids.get(name) {
            return *symbol;
        }
        let index = u32::try_from(self.symbols.len()).expect("symbol table exceeded u32::MAX");
        let symbol = SymbolId(index);
        let name = name.to_string();
        self.symbols.push(name.clone());
        self.symbol_ids.insert(name, symbol);
        symbol
    }

    pub fn symbol(&self, symbol: SymbolId) -> &str {
        &self.symbols[symbol.index()]
    }

    pub fn find_symbol(&self, name: &str) -> Option<SymbolId> {
        self.symbol_ids.get(name).copied()
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
        parameters: Vec<ModuleParameter>,
    ) -> Result<ModuleId, String> {
        Ok(self.add_module_entry(name, Some(parent), parameters))
    }

    pub fn reserve_child_module(&mut self, parent: ModuleId, name: String) -> ModuleId {
        self.add_module_entry(name, Some(parent), vec![])
    }

    pub fn add_module_parameter(&mut self, module: ModuleId, parameter: ModuleParameter) {
        self.module_mut(module).parameters.push(parameter);
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
        parameters: Vec<ModuleParameter>,
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

    pub fn module_parameter_opt(&self, id: ModuleParamId) -> Option<&ModuleParameter> {
        self.module(id.module).parameters.get(id.position as usize)
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
        let id = self.reserve_inductive(module);
        self.define_inductive(id, inductive);
        id
    }

    pub fn reserve_inductive(&mut self, module: ModuleId) -> InductiveId {
        let module_env = self.module_mut(module);
        let index = u32::try_from(module_env.inductives.len())
            .expect("module inductive table exceeded u32::MAX");
        module_env.inductives.push(None);
        InductiveId { module, index }
    }

    pub fn define_inductive(&mut self, id: InductiveId, inductive: InductiveTypeSpecs) {
        let slot = &mut self.module_mut(id.module).inductives[id.index as usize];
        assert!(slot.is_none(), "inductive ID was already defined");
        *slot = Some(inductive);
    }

    pub fn inductive(&self, id: InductiveId) -> &InductiveTypeSpecs {
        self.module(id.module).inductives[id.index as usize]
            .as_ref()
            .expect("reserved inductive ID was used before definition")
    }

    pub fn add_instance(
        &mut self,
        owner: ModuleId,
        source: ModuleId,
        materialized: ModuleId,
        arguments: Vec<(ModuleParamId, Exp)>,
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
