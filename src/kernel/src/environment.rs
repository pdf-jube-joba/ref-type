//! Crate/module declarations and materialized-instance provenance.

use crate::{
    exp::{Arena, Exp},
    ids::{
        DefId, InductiveId, ModuleId, ModuleInstanceId, ModuleParamId, ProgramInductiveId, SymbolId,
    },
    inductive::InductiveTypeSpecs,
    program::{Computation, ComputationType, Value, ValueType},
    program_inductive::ProgramInductiveTypeSpecs,
};
use serde::Serialize;
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize)]
pub enum DefinedConstant {
    Pts {
        ty: Exp,
        body: Exp,
    },
    ProgramValue {
        ty: ValueType,
        body: Value,
    },
    ProgramComputation {
        ty: ComputationType,
        body: Computation,
    },
}

impl DefinedConstant {
    pub fn kind(&self) -> DefinitionKind {
        match self {
            Self::Pts { .. } => DefinitionKind::Pts,
            Self::ProgramValue { .. } => DefinitionKind::ProgramValue,
            Self::ProgramComputation { .. } => DefinitionKind::ProgramComputation,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum DefinitionKind {
    Pts,
    ProgramValue,
    ProgramComputation,
}

#[derive(Debug, Clone)]
pub struct ModuleParameter {
    pub name: SymbolId,
    pub kind: ModuleParameterKind,
}

#[derive(Debug, Clone, Copy)]
pub enum ModuleParameterKind {
    Pts { ty: Exp },
    ProgramType,
    ProgramValue { ty: ValueType },
}

impl ModuleParameter {
    pub fn id(&self, module: ModuleId, position: u32) -> ModuleParamId {
        ModuleParamId { module, position }
    }

    pub fn pts_ty(&self) -> Option<Exp> {
        match self.kind {
            ModuleParameterKind::Pts { ty } => Some(ty),
            ModuleParameterKind::ProgramType | ModuleParameterKind::ProgramValue { .. } => None,
        }
    }

    pub fn value_ty(&self) -> Option<ValueType> {
        match self.kind {
            ModuleParameterKind::ProgramValue { ty } => Some(ty),
            ModuleParameterKind::Pts { .. } | ModuleParameterKind::ProgramType => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleArgument {
    Pts(Exp),
    ProgramType(ValueType),
    ProgramValue(Value),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleItem {
    Definition {
        name: String,
        definition: DefId,
    },
    Inductive {
        name: String,
        constructor_names: Vec<String>,
        associated_definitions: Vec<(String, DefId)>,
        inductive: InductiveId,
    },
    Record {
        name: String,
        associated_definitions: Vec<(String, DefId)>,
        inductive: InductiveId,
    },
    ProgramInductive {
        name: String,
        constructor_names: Vec<String>,
        associated_definitions: Vec<(String, DefId)>,
        inductive: ProgramInductiveId,
        reflected: InductiveId,
    },
}

impl ModuleItem {
    pub fn name(&self) -> &str {
        match self {
            Self::Definition { name, .. }
            | Self::Inductive { name, .. }
            | Self::Record { name, .. }
            | Self::ProgramInductive { name, .. } => name,
        }
    }
}

#[derive(Debug)]
pub struct ModuleInstance {
    pub id: ModuleInstanceId,
    pub source: ModuleId,
    pub materialized: ModuleId,
    pub arguments: Vec<(ModuleParamId, ModuleArgument)>,
    /// Maps definitions in `materialized` back to definitions in `source`.
    pub definition_origins: HashMap<DefId, DefId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefinitionOrigin {
    pub instance: ModuleInstanceId,
    pub source: DefId,
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
    program_inductives: Vec<Option<ProgramInductiveTypeSpecs>>,
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
            program_inductives: Vec::new(),
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

    pub fn program_inductives(&self) -> &[Option<ProgramInductiveTypeSpecs>] {
        &self.program_inductives
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
    materialized_instances: HashMap<ModuleId, ModuleInstanceId>,
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
            materialized_instances: HashMap::new(),
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

    pub fn add_program_inductive(
        &mut self,
        module: ModuleId,
        inductive: ProgramInductiveTypeSpecs,
    ) -> ProgramInductiveId {
        let id = self.reserve_program_inductive(module);
        self.define_program_inductive(id, inductive);
        id
    }

    pub fn reserve_program_inductive(&mut self, module: ModuleId) -> ProgramInductiveId {
        let module_env = self.module_mut(module);
        let index = u32::try_from(module_env.program_inductives.len())
            .expect("module Program inductive table exceeded u32::MAX");
        module_env.program_inductives.push(None);
        ProgramInductiveId { module, index }
    }

    pub fn define_program_inductive(
        &mut self,
        id: ProgramInductiveId,
        inductive: ProgramInductiveTypeSpecs,
    ) {
        let slot = &mut self.module_mut(id.module).program_inductives[id.index as usize];
        assert!(slot.is_none(), "Program inductive ID was already defined");
        *slot = Some(inductive);
    }

    pub fn program_inductive(&self, id: ProgramInductiveId) -> &ProgramInductiveTypeSpecs {
        self.module(id.module).program_inductives[id.index as usize]
            .as_ref()
            .expect("reserved Program inductive ID was used before definition")
    }

    pub fn add_instance(
        &mut self,
        owner: ModuleId,
        source: ModuleId,
        materialized: ModuleId,
        arguments: Vec<(ModuleParamId, ModuleArgument)>,
        definition_origins: HashMap<DefId, DefId>,
    ) -> ModuleInstanceId {
        let local = u32::try_from(self.module(owner).instances.len())
            .expect("module instance table exceeded u32::MAX");
        let id = ModuleInstanceId { owner, local };
        let previous = self.materialized_instances.insert(materialized, id);
        assert!(
            previous.is_none(),
            "materialized module already has an origin"
        );
        self.module_mut(owner).instances.push(ModuleInstance {
            id,
            source,
            materialized,
            arguments,
            definition_origins,
        });
        id
    }

    pub fn instance(&self, id: ModuleInstanceId) -> &ModuleInstance {
        &self.module(id.owner).instances[id.local as usize]
    }

    pub fn materialized_instance(&self, module: ModuleId) -> Option<ModuleInstanceId> {
        self.materialized_instances.get(&module).copied()
    }

    pub fn definition_origin(&self, definition: DefId) -> Option<DefinitionOrigin> {
        let instance = self.materialized_instance(definition.module)?;
        let source = *self
            .instance(instance)
            .definition_origins
            .get(&definition)?;
        Some(DefinitionOrigin { instance, source })
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

    pub fn publish_associated_definition(
        &mut self,
        module: ModuleId,
        owner: &str,
        name: String,
        definition: DefId,
    ) -> Result<(), String> {
        let field_names = self
            .module(module)
            .item(owner)
            .map(|item| match item {
                ModuleItem::Record { inductive, .. } => self.inductive(*inductive).constructors()
                    [0]
                .telescope
                .iter()
                .filter_map(|binder| match binder {
                    crate::inductive::CtorBinder::Simple((name, _)) => {
                        Some(self.symbol(*name).to_string())
                    }
                    _ => None,
                })
                .collect::<Vec<_>>(),
                ModuleItem::ProgramInductive {
                    constructor_names,
                    inductive,
                    ..
                } if constructor_names.is_empty() => {
                    self.program_inductive(*inductive).constructors()[0]
                        .fields()
                        .iter()
                        .map(|(name, _)| self.symbol(*name).to_string())
                        .collect()
                }
                _ => Vec::new(),
            })
            .unwrap_or_default();
        let item = self
            .module_mut(module)
            .names
            .get(owner)
            .copied()
            .and_then(|index| self.module_mut(module).items.get_mut(index))
            .ok_or_else(|| format!("Associated item owner '{owner}' was not found"))?;
        let (reserved, definitions) = match item {
            ModuleItem::Inductive {
                constructor_names,
                associated_definitions,
                ..
            }
            | ModuleItem::ProgramInductive {
                constructor_names,
                associated_definitions,
                ..
            } => (constructor_names.as_slice(), associated_definitions),
            ModuleItem::Record {
                associated_definitions,
                ..
            } => (&[][..], associated_definitions),
            ModuleItem::Definition { .. } => {
                return Err(format!("Module item '{owner}' is not a type"));
            }
        };
        if reserved.iter().any(|candidate| candidate == &name)
            || field_names.iter().any(|candidate| candidate == &name)
            || definitions.iter().any(|(candidate, _)| candidate == &name)
        {
            return Err(format!(
                "Associated item '{owner}::{name}' is already defined"
            ));
        }
        definitions.push((name, definition));
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
