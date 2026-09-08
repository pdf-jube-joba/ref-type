//! Crate/module declarations and materialized-instance provenance.

use crate::raw::{
    exp::{Arena, Exp},
    ids::{
        DefId, InductiveId, ModuleId, ModuleInstanceId, ModuleParamId, ProgramInductiveId, SymbolId,
    },
    inductive::InductiveTypeSpecs,
    program::{Computation, ComputationType, Value, ValueType},
    program_inductive::ProgramInductiveTypeSpecs,
};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum DefinedConstant {
    Pts {
        ty: Exp,
        body: Exp,
    },
    ProgramValue {
        ty: ValueType,
        body: Value,
        certified_reflection: Option<Exp>,
    },
    ProgramComputation {
        ty: ComputationType,
        body: Computation,
        certified_reflection: Option<Exp>,
    },
}

impl DefinedConstant {
    fn kind_name(&self) -> &'static str {
        match self {
            Self::Pts { .. } => "Set/Prop",
            Self::ProgramValue { .. } => "Program value",
            Self::ProgramComputation { .. } => "Program computation",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

impl From<Exp> for ModuleArgument {
    fn from(value: Exp) -> Self {
        Self::Pts(value)
    }
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
    fn new(name: String, parent: Option<ModuleId>, parameters: Vec<ModuleParameter>) -> Self {
        Self {
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
    pub(crate) inference_cache:
        std::cell::RefCell<HashMap<(Exp, Vec<(SymbolId, Exp)>, ModuleId), Exp>>,
    symbols: Vec<String>,
    symbol_ids: HashMap<String, SymbolId>,
    modules: Vec<ModuleEnv>,
    materialized_instances: HashMap<ModuleId, ModuleInstanceId>,
    checking_scopes: HashMap<ModuleId, ModuleId>,
    checking_contexts: HashMap<ModuleId, crate::raw::exp::ExpContext>,
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
            inference_cache: Default::default(),
            symbols: vec![anonymous, root],
            symbol_ids,
            modules: vec![ModuleEnv::new("root".into(), None, vec![])],
            materialized_instances: HashMap::new(),
            checking_scopes: HashMap::new(),
            checking_contexts: HashMap::new(),
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

    pub fn arena(&self) -> &Arena {
        &self.arena
    }

    pub fn root_module(&self) -> ModuleId {
        ModuleId(0)
    }

    pub fn add_module(&mut self) -> ModuleId {
        self.add_module_entry("<instance>".into(), None, vec![])
    }

    /// An unpublished instance inherits the importing module's checking scope.
    pub fn add_module_in_scope(
        &mut self,
        owner: ModuleId,
        mut context: crate::raw::exp::ExpContext,
    ) -> Result<ModuleId, String> {
        crate::raw::derivation::CheckSession::new(self, owner, &mut context)
            .check_wellformed_context()
            .map_err(|error| error.to_string())?;
        let module = self.add_module();
        self.checking_scopes.insert(module, owner);
        self.checking_contexts.insert(module, context);
        Ok(module)
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
        self.modules.push(ModuleEnv::new(name, parent, parameters));
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

    /// Check a declaration in its owning module before making it available.
    /// Ordinary declarations use module parameters. Instances retain the checked
    /// context supplied at instantiation, including any local binders.
    /// A failed check never inserts a definition.
    pub fn add_definition(
        &mut self,
        module: ModuleId,
        definition: DefinedConstant,
    ) -> Result<DefId, String> {
        let span = tracing::debug_span!(target: "ref_type::environment",
            "register_definition", ?module, kind = definition.kind_name());
        let _entered = span.enter();
        self.check_definition(module, &definition)
            .inspect_err(|error| {
                tracing::error!(target: "ref_type::environment", %error, "definition rejected");
            })?;
        let module_env = self.module_mut(module);
        let index = u32::try_from(module_env.definitions.len())
            .expect("module definition table exceeded u32::MAX");
        module_env.definitions.push(definition);
        let id = DefId { module, index };
        tracing::debug!(target: "ref_type::environment", ?id, "checked definition registered");
        Ok(id)
    }

    fn check_definition(
        &self,
        module: ModuleId,
        definition: &DefinedConstant,
    ) -> Result<(), String> {
        use crate::raw::{
            derivation::CheckSession, program_derivation::ProgramCheckSession, reflection,
        };
        let mut ancestors = Vec::new();
        let mut current = Some(module);
        while let Some(id) = current {
            ancestors.push(id);
            current = self
                .checking_scopes
                .get(&id)
                .copied()
                .or(self.module(id).parent());
        }
        ancestors.reverse();
        let parameters: Vec<_> = ancestors
            .iter()
            .flat_map(|id| self.module(*id).parameters())
            .collect();
        let mut pts_context = parameters
            .iter()
            .filter_map(|parameter| match parameter.kind {
                ModuleParameterKind::Pts { ty } => Some(crate::raw::exp::ExpContextEntry {
                    var: parameter.name,
                    ty,
                }),
                _ => None,
            })
            .collect();
        if let Some(context) = self.checking_contexts.get(&module) {
            pts_context = context.clone();
        }
        let mut program_context = Vec::new();
        let certificate = match *definition {
            DefinedConstant::Pts { ty, body } => {
                CheckSession::new(self, module, &mut pts_context)
                    .check_pts(body, ty)
                    .map_err(|error| format!("definition check failed: {error:?}"))?;
                None
            }
            DefinedConstant::ProgramValue {
                ty,
                body,
                certified_reflection,
            } => {
                ProgramCheckSession::new(self, &mut program_context)
                    .check_value(body, ty)
                    .map_err(|error| format!("Program value definition check failed: {error:?}"))?;
                certified_reflection
                    .map(|term| reflection::reflect_value_type(self, ty).map(|ty| (term, ty)))
                    .transpose()
                    .map_err(|error| error.to_string())?
            }
            DefinedConstant::ProgramComputation {
                ty,
                body,
                certified_reflection,
            } => {
                ProgramCheckSession::new(self, &mut program_context)
                    .check_computation(body, ty)
                    .map_err(|error| {
                        format!("Program computation definition check failed: {error:?}")
                    })?;
                certified_reflection
                    .map(|term| reflection::reflect_computation_type(self, ty).map(|ty| (term, ty)))
                    .transpose()
                    .map_err(|error| error.to_string())?
            }
        };
        if let Some((term, ty)) = certificate {
            for parameter in parameters {
                let ty = match parameter.kind {
                    ModuleParameterKind::Pts { .. } => continue,
                    ModuleParameterKind::ProgramType => {
                        self.arena().sort(crate::raw::sort::Sort::Set(0))
                    }
                    ModuleParameterKind::ProgramValue { ty } => {
                        reflection::reflect_value_type(self, ty)
                            .map_err(|error| error.to_string())?
                    }
                };
                pts_context.push(crate::raw::exp::ExpContextEntry {
                    var: parameter.name,
                    ty,
                });
            }
            CheckSession::new(self, module, &mut pts_context)
                .check_pts(term, ty)
                .map_err(|error| format!("reflection certificate check failed: {error:?}"))?;
        }
        Ok(())
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

impl CrateEnv {
    pub(crate) fn definition_context(&self, module: ModuleId) -> crate::raw::exp::ExpContext {
        if let Some(context) = self.checking_contexts.get(&module) {
            return context.clone();
        }
        let mut ancestors = vec![];
        let mut current = Some(module);
        while let Some(id) = current {
            ancestors.push(id);
            current = self
                .checking_scopes
                .get(&id)
                .copied()
                .or(self.module(id).parent());
        }
        ancestors.reverse();
        ancestors
            .into_iter()
            .flat_map(|id| self.module(id).parameters())
            .filter_map(|p| match p.kind {
                ModuleParameterKind::Pts { ty } => {
                    Some(crate::raw::exp::ExpContextEntry { var: p.name, ty })
                }
                ModuleParameterKind::ProgramType => Some(crate::raw::exp::ExpContextEntry {
                    var: p.name,
                    ty: self.arena.sort(crate::raw::sort::Sort::Set(0)),
                }),
                ModuleParameterKind::ProgramValue { ty } => {
                    crate::raw::reflection::reflect_value_type(self, ty)
                        .ok()
                        .map(|ty| crate::raw::exp::ExpContextEntry { var: p.name, ty })
                }
            })
            .collect()
    }
    pub(crate) fn parameter_ids(&self) -> Vec<ModuleParamId> {
        self.modules
            .iter()
            .enumerate()
            .flat_map(|(m, module)| {
                (0..module.parameters.len()).map(move |i| ModuleParamId {
                    module: ModuleId(m as u32),
                    position: i as u32,
                })
            })
            .collect()
    }
    pub(crate) fn definition_ids(&self) -> Vec<DefId> {
        self.modules
            .iter()
            .enumerate()
            .flat_map(|(m, module)| {
                (0..module.definitions.len()).map(move |i| DefId {
                    module: ModuleId(m as u32),
                    index: i as u32,
                })
            })
            .collect()
    }
    pub(crate) fn inductive_ids(&self) -> Vec<InductiveId> {
        self.modules
            .iter()
            .enumerate()
            .flat_map(|(m, module)| {
                module
                    .inductives
                    .iter()
                    .enumerate()
                    .filter_map(move |(i, x)| {
                        x.as_ref().map(|_| InductiveId {
                            module: ModuleId(m as u32),
                            index: i as u32,
                        })
                    })
            })
            .collect()
    }
    pub(crate) fn datatype_ids(&self) -> Vec<ProgramInductiveId> {
        self.modules
            .iter()
            .enumerate()
            .flat_map(|(m, module)| {
                module
                    .program_inductives
                    .iter()
                    .enumerate()
                    .filter_map(move |(i, x)| {
                        x.as_ref().map(|_| ProgramInductiveId {
                            module: ModuleId(m as u32),
                            index: i as u32,
                        })
                    })
            })
            .collect()
    }
}
