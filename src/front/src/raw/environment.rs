//! Crate/module declarations and materialized-instance provenance.

use crate::raw::{
    exp::{Arena, Exp},
    ids::{
        DefId, InductiveId, ModuleId, ModuleInstanceId, ModuleParamId, ProgramInductiveId, SymbolId,
    },
    inductive::InductiveTypeSpecs,
    program::{ComputationTerm, ComputationType, ValueTerm, ValueType},
    program_inductive::ProgramInductiveTypeSpecs,
};
use std::{
    cell::{Cell, OnceCell, RefCell},
    collections::{HashMap, HashSet},
};

#[derive(Debug, Clone)]
pub enum DefinedConstant {
    Pts {
        ty: Exp,
        body: Exp,
    },
    ProgramValue {
        ty: ValueType,
        body: ValueTerm,
        certified_reflection: Option<Exp>,
    },
    ProgramComputation {
        ty: ComputationType,
        body: ComputationTerm,
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
    ProgramValue(ValueTerm),
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
        record_fields: Option<Vec<String>>,
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
    pub(crate) remapping: InstanceRemapping,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct InstanceRemapping {
    pub module_ids: HashMap<ModuleId, ModuleId>,
    pub definition_ids: HashMap<DefId, DefId>,
    pub inductive_ids: HashMap<InductiveId, InductiveId>,
    pub program_inductive_ids: HashMap<ProgramInductiveId, ProgramInductiveId>,
}

#[derive(Debug, Clone)]
struct LazyDefinition {
    source: DefId,
    substitutions: Vec<(ModuleParamId, ModuleArgument)>,
    reflected_substitutions: Vec<(ModuleParamId, Exp)>,
    remapping: InstanceRemapping,
}

#[derive(Debug, Clone)]
struct LazyInductive {
    source: InductiveId,
    substitutions: Vec<(ModuleParamId, Exp)>,
    remapping: InstanceRemapping,
}

#[derive(Debug, Clone)]
struct LazyProgramInductive {
    source: ProgramInductiveId,
    substitutions: Vec<(ModuleParamId, ModuleArgument)>,
    remapping: InstanceRemapping,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefinitionOrigin {
    pub instance: ModuleInstanceId,
    pub source: DefId,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct MaterializationStats {
    pub definitions: usize,
    pub inductives: usize,
    pub datatypes: usize,
}

#[derive(Debug)]
pub struct ModuleEnv {
    name: String,
    parent: Option<ModuleId>,
    children: Vec<ModuleId>,
    parameters: Vec<ModuleParameter>,
    definitions: Vec<OnceCell<DefinedConstant>>,
    inductives: Vec<OnceCell<InductiveTypeSpecs>>,
    program_inductives: Vec<OnceCell<ProgramInductiveTypeSpecs>>,
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

type InferenceCache = HashMap<(Exp, Vec<(SymbolId, Exp)>, ModuleId), Exp>;

#[derive(Debug)]
pub struct CrateEnv {
    definition_parameters: HashMap<DefId, Vec<SymbolId>>,
    arena: Arena,
    pub(crate) inference_cache: std::cell::RefCell<InferenceCache>,
    symbols: Vec<String>,
    symbol_ids: HashMap<String, SymbolId>,
    modules: Vec<ModuleEnv>,
    materialized_instances: HashMap<ModuleId, ModuleInstanceId>,
    checking_scopes: HashMap<ModuleId, ModuleId>,
    checking_contexts: HashMap<ModuleId, crate::raw::exp::ExpContext>,
    lazy_definitions: HashMap<DefId, LazyDefinition>,
    lazy_inductives: HashMap<InductiveId, LazyInductive>,
    lazy_program_inductives: HashMap<ProgramInductiveId, LazyProgramInductive>,
    materializing_definitions: RefCell<HashSet<DefId>>,
    failed_definitions: RefCell<HashMap<DefId, String>>,
    materialized_definitions: Cell<usize>,
    materialized_inductives: Cell<usize>,
    materialized_datatypes: Cell<usize>,
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
            definition_parameters: HashMap::new(),
            arena: Arena::new(),
            inference_cache: Default::default(),
            symbols: vec![anonymous, root],
            symbol_ids,
            modules: vec![ModuleEnv::new("root".into(), None, vec![])],
            materialized_instances: HashMap::new(),
            checking_scopes: HashMap::new(),
            checking_contexts: HashMap::new(),
            lazy_definitions: HashMap::new(),
            lazy_inductives: HashMap::new(),
            lazy_program_inductives: HashMap::new(),
            materializing_definitions: RefCell::new(HashSet::new()),
            failed_definitions: RefCell::new(HashMap::new()),
            materialized_definitions: Cell::new(0),
            materialized_inductives: Cell::new(0),
            materialized_datatypes: Cell::new(0),
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

    #[cfg(test)]
    pub(crate) fn add_child_module(
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
        self.add_parameterized_definition(module, definition, Vec::new())
    }

    pub fn definition_parameters(&self, id: DefId) -> &[SymbolId] {
        self.definition_parameters
            .get(&id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn add_parameterized_definition(
        &mut self,
        module: ModuleId,
        definition: DefinedConstant,
        parameters: Vec<SymbolId>,
    ) -> Result<DefId, String> {
        let span = tracing::debug_span!(target: "ref_type::environment",
            "register_definition", ?module, kind = definition.kind_name());
        let _entered = span.enter();
        self.check_definition(module, &definition, &parameters)
            .inspect_err(|error| {
                tracing::error!(target: "ref_type::environment", %error, "definition rejected");
            })?;
        let module_env = self.module_mut(module);
        let index = u32::try_from(module_env.definitions.len())
            .expect("module definition table exceeded u32::MAX");
        module_env.definitions.push(OnceCell::from(definition));
        let id = DefId { module, index };
        self.definition_parameters.insert(id, parameters);
        tracing::debug!(target: "ref_type::environment", ?id, "checked definition registered");
        Ok(id)
    }

    fn check_definition(
        &self,
        module: ModuleId,
        definition: &DefinedConstant,
        type_parameters: &[SymbolId],
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
        let mut program_context = type_parameters
            .iter()
            .map(|var| crate::raw::program::ProgramContextEntry::ValueType { var: *var })
            .collect();
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
                    .check_value_term(body, ty)
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
                    .check_computation_term(body, ty)
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
            pts_context.extend(type_parameters.iter().map(|var| {
                crate::raw::exp::ExpContextEntry {
                    var: *var,
                    ty: self.arena().sort(crate::raw::sort::Sort::Set(0)),
                }
            }));
            CheckSession::new(self, module, &mut pts_context)
                .check_pts(term, ty)
                .map_err(|error| format!("reflection certificate check failed: {error:?}"))?;
        }
        Ok(())
    }

    pub fn definition(&self, id: DefId) -> &DefinedConstant {
        self.resolve_definition(id)
            .unwrap_or_else(|error| panic!("failed to materialize definition {id:?}: {error}"))
    }

    pub fn resolve_definition(&self, id: DefId) -> Result<&DefinedConstant, String> {
        let slot = &self.module(id.module).definitions[id.index as usize];
        if let Some(definition) = slot.get() {
            return Ok(definition);
        }
        if let Some(error) = self.failed_definitions.borrow().get(&id) {
            return Err(error.clone());
        }
        let lazy = self
            .lazy_definitions
            .get(&id)
            .cloned()
            .ok_or_else(|| format!("reserved definition {id:?} was used before definition"))?;
        if !self.materializing_definitions.borrow_mut().insert(id) {
            return Err(format!("cyclic lazy definition dependency at {id:?}"));
        }
        let result: Result<&DefinedConstant, String> = (|| {
            let source = self.resolve_definition(lazy.source)?.clone();
            let definition = match source {
                DefinedConstant::Pts { ty, body } => DefinedConstant::Pts {
                    ty: crate::raw::calculus::remap_all_global_ids(
                        self.arena(),
                        crate::raw::calculus::exp_subst_map(
                            self.arena(),
                            ty,
                            &lazy.reflected_substitutions,
                        ),
                        &lazy.remapping.definition_ids,
                        &lazy.remapping.inductive_ids,
                        &lazy.remapping.program_inductive_ids,
                    ),
                    body: crate::raw::calculus::remap_all_global_ids(
                        self.arena(),
                        crate::raw::calculus::exp_subst_map(
                            self.arena(),
                            body,
                            &lazy.reflected_substitutions,
                        ),
                        &lazy.remapping.definition_ids,
                        &lazy.remapping.inductive_ids,
                        &lazy.remapping.program_inductive_ids,
                    ),
                },
                DefinedConstant::ProgramValue {
                    ty,
                    body,
                    certified_reflection,
                } => DefinedConstant::ProgramValue {
                    ty: crate::raw::program_calculus::remap_value_type_global_ids(
                        self.arena(),
                        crate::raw::program_calculus::subst_value_type_module_params(
                            self.arena(),
                            ty,
                            &lazy.substitutions,
                        ),
                        &lazy.remapping.definition_ids,
                        &lazy.remapping.program_inductive_ids,
                    ),
                    body: crate::raw::program_calculus::remap_value_global_ids(
                        self.arena(),
                        crate::raw::program_calculus::subst_value_module_params(
                            self.arena(),
                            body,
                            &lazy.substitutions,
                        ),
                        &lazy.remapping.definition_ids,
                        &lazy.remapping.program_inductive_ids,
                    ),
                    certified_reflection: certified_reflection.map(|term| {
                        crate::raw::calculus::remap_all_global_ids(
                            self.arena(),
                            crate::raw::calculus::exp_subst_map(
                                self.arena(),
                                term,
                                &lazy.reflected_substitutions,
                            ),
                            &lazy.remapping.definition_ids,
                            &lazy.remapping.inductive_ids,
                            &lazy.remapping.program_inductive_ids,
                        )
                    }),
                },
                DefinedConstant::ProgramComputation {
                    ty,
                    body,
                    certified_reflection,
                } => DefinedConstant::ProgramComputation {
                    ty: crate::raw::program_calculus::remap_computation_type_global_ids(
                        self.arena(),
                        crate::raw::program_calculus::subst_computation_type_module_params(
                            self.arena(),
                            ty,
                            &lazy.substitutions,
                        ),
                        &lazy.remapping.definition_ids,
                        &lazy.remapping.program_inductive_ids,
                    ),
                    body: crate::raw::program_calculus::remap_computation_global_ids(
                        self.arena(),
                        crate::raw::program_calculus::subst_computation_module_params(
                            self.arena(),
                            body,
                            &lazy.substitutions,
                        ),
                        &lazy.remapping.definition_ids,
                        &lazy.remapping.program_inductive_ids,
                    ),
                    certified_reflection: certified_reflection.map(|term| {
                        crate::raw::calculus::remap_all_global_ids(
                            self.arena(),
                            crate::raw::calculus::exp_subst_map(
                                self.arena(),
                                term,
                                &lazy.reflected_substitutions,
                            ),
                            &lazy.remapping.definition_ids,
                            &lazy.remapping.inductive_ids,
                            &lazy.remapping.program_inductive_ids,
                        )
                    }),
                },
            };
            self.check_definition(id.module, &definition, self.definition_parameters(id))?;
            slot.set(definition)
                .map_err(|_| format!("definition {id:?} was materialized twice"))?;
            Ok(slot.get().expect("definition was just initialized"))
        })();
        self.materializing_definitions.borrow_mut().remove(&id);
        match &result {
            Ok(_) => self
                .materialized_definitions
                .set(self.materialized_definitions.get() + 1),
            Err(error) => {
                self.failed_definitions
                    .borrow_mut()
                    .insert(id, error.clone());
            }
        }
        result
    }

    pub(crate) fn reserve_lazy_definition(
        &mut self,
        module: ModuleId,
        source: DefId,
        substitutions: Vec<(ModuleParamId, ModuleArgument)>,
        reflected_substitutions: Vec<(ModuleParamId, Exp)>,
    ) -> DefId {
        let parameters = self.definition_parameters(source).to_vec();
        let index = self.module(module).definitions.len() as u32;
        self.module_mut(module).definitions.push(OnceCell::new());
        let id = DefId { module, index };
        if !parameters.is_empty() {
            self.definition_parameters.insert(id, parameters);
        }
        self.lazy_definitions.insert(
            id,
            LazyDefinition {
                source,
                substitutions,
                reflected_substitutions,
                remapping: InstanceRemapping::default(),
            },
        );
        id
    }

    pub(crate) fn set_lazy_definition_remapping(
        &mut self,
        id: DefId,
        remapping: InstanceRemapping,
    ) {
        self.lazy_definitions
            .get_mut(&id)
            .expect("lazy definition")
            .remapping = remapping;
    }

    #[cfg(test)]
    pub(crate) fn add_inductive(
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
        module_env.inductives.push(OnceCell::new());
        InductiveId { module, index }
    }

    pub fn define_inductive(&mut self, id: InductiveId, inductive: InductiveTypeSpecs) {
        let slot = &self.module(id.module).inductives[id.index as usize];
        assert!(
            slot.set(inductive).is_ok(),
            "inductive ID was already defined"
        );
    }

    pub fn inductive(&self, id: InductiveId) -> &InductiveTypeSpecs {
        let slot = &self.module(id.module).inductives[id.index as usize];
        if slot.get().is_none() {
            let lazy = self
                .lazy_inductives
                .get(&id)
                .unwrap_or_else(|| panic!("reserved inductive ID was used before definition"));
            let spec = self
                .inductive(lazy.source)
                .clone()
                .instantiate(self.arena(), &lazy.substitutions)
                .remap_global_ids(
                    self.arena(),
                    &lazy.remapping.definition_ids,
                    &lazy.remapping.inductive_ids,
                );
            let _ = slot.set(spec);
            self.materialized_inductives
                .set(self.materialized_inductives.get() + 1);
        }
        slot.get().expect("lazy inductive initialized")
    }

    pub(crate) fn reserve_lazy_inductive(
        &mut self,
        module: ModuleId,
        source: InductiveId,
        substitutions: Vec<(ModuleParamId, Exp)>,
    ) -> InductiveId {
        let id = self.reserve_inductive(module);
        self.lazy_inductives.insert(
            id,
            LazyInductive {
                source,
                substitutions,
                remapping: InstanceRemapping::default(),
            },
        );
        id
    }

    pub(crate) fn set_lazy_inductive_remapping(
        &mut self,
        id: InductiveId,
        remapping: InstanceRemapping,
    ) {
        self.lazy_inductives
            .get_mut(&id)
            .expect("lazy inductive")
            .remapping = remapping;
    }

    pub fn reserve_program_inductive(&mut self, module: ModuleId) -> ProgramInductiveId {
        let module_env = self.module_mut(module);
        let index = u32::try_from(module_env.program_inductives.len())
            .expect("module Program inductive table exceeded u32::MAX");
        module_env.program_inductives.push(OnceCell::new());
        ProgramInductiveId { module, index }
    }

    pub fn define_program_inductive(
        &mut self,
        id: ProgramInductiveId,
        inductive: ProgramInductiveTypeSpecs,
    ) {
        let slot = &self.module(id.module).program_inductives[id.index as usize];
        assert!(
            slot.set(inductive).is_ok(),
            "Program inductive ID was already defined"
        );
    }

    pub fn program_inductive(&self, id: ProgramInductiveId) -> &ProgramInductiveTypeSpecs {
        let slot = &self.module(id.module).program_inductives[id.index as usize];
        if slot.get().is_none() {
            let lazy = self.lazy_program_inductives.get(&id).unwrap_or_else(|| {
                panic!("reserved Program inductive ID was used before definition")
            });
            let spec = self
                .program_inductive(lazy.source)
                .clone()
                .instantiate(self.arena(), &lazy.substitutions)
                .remap_global_ids(
                    self.arena(),
                    &lazy.remapping.definition_ids,
                    &lazy.remapping.inductive_ids,
                    &lazy.remapping.program_inductive_ids,
                );
            let _ = slot.set(spec);
            self.materialized_datatypes
                .set(self.materialized_datatypes.get() + 1);
        }
        slot.get().expect("lazy Program inductive initialized")
    }

    pub(crate) fn reserve_lazy_program_inductive(
        &mut self,
        module: ModuleId,
        source: ProgramInductiveId,
        substitutions: Vec<(ModuleParamId, ModuleArgument)>,
    ) -> ProgramInductiveId {
        let id = self.reserve_program_inductive(module);
        self.lazy_program_inductives.insert(
            id,
            LazyProgramInductive {
                source,
                substitutions,
                remapping: InstanceRemapping::default(),
            },
        );
        id
    }

    pub(crate) fn set_lazy_program_inductive_remapping(
        &mut self,
        id: ProgramInductiveId,
        remapping: InstanceRemapping,
    ) {
        self.lazy_program_inductives
            .get_mut(&id)
            .expect("lazy Program inductive")
            .remapping = remapping;
    }

    pub fn add_instance(
        &mut self,
        owner: ModuleId,
        source: ModuleId,
        materialized: ModuleId,
        arguments: Vec<(ModuleParamId, ModuleArgument)>,
        definition_origins: HashMap<DefId, DefId>,
    ) -> ModuleInstanceId {
        self.add_instance_with_remapping(
            owner,
            source,
            materialized,
            arguments,
            definition_origins,
            InstanceRemapping::default(),
        )
    }

    pub(crate) fn add_instance_with_remapping(
        &mut self,
        owner: ModuleId,
        source: ModuleId,
        materialized: ModuleId,
        arguments: Vec<(ModuleParamId, ModuleArgument)>,
        definition_origins: HashMap<DefId, DefId>,
        remapping: InstanceRemapping,
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
            remapping,
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

    pub fn materialization_stats(&self) -> MaterializationStats {
        MaterializationStats {
            definitions: self.materialized_definitions.get(),
            inductives: self.materialized_inductives.get(),
            datatypes: self.materialized_datatypes.get(),
        }
    }

    pub fn is_definition_materialized(&self, id: DefId) -> bool {
        self.module(id.module).definitions[id.index as usize]
            .get()
            .is_some()
    }

    pub fn is_inductive_materialized(&self, id: InductiveId) -> bool {
        self.module(id.module).inductives[id.index as usize]
            .get()
            .is_some()
    }

    pub fn is_program_inductive_materialized(&self, id: ProgramInductiveId) -> bool {
        self.module(id.module).program_inductives[id.index as usize]
            .get()
            .is_some()
    }
}

impl CrateEnv {
    /// Materialized modules retain the importing PTS context separately from
    /// the named Program parameters needed to classify reflection certificates.
    pub(crate) fn program_reflection_context(
        &self,
        module: ModuleId,
    ) -> crate::raw::exp::ExpContext {
        let mut context = self.definition_context(module);
        if !self.checking_contexts.contains_key(&module) {
            return context;
        }
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
        for id in ancestors.into_iter().rev() {
            for parameter in self.module(id).parameters() {
                let ty = match parameter.kind {
                    ModuleParameterKind::Pts { .. } => continue,
                    ModuleParameterKind::ProgramType => {
                        self.arena.sort(crate::raw::sort::Sort::Set(0))
                    }
                    ModuleParameterKind::ProgramValue { ty } => {
                        crate::raw::reflection::reflect_value_type(self, ty)
                            .expect("checked Program parameter")
                    }
                };
                context.push(crate::raw::exp::ExpContextEntry {
                    var: parameter.name,
                    ty,
                });
            }
        }
        context
    }

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
                module
                    .definitions
                    .iter()
                    .enumerate()
                    .filter_map(move |(i, slot)| {
                        slot.get().map(|_| DefId {
                            module: ModuleId(m as u32),
                            index: i as u32,
                        })
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
                        x.get().map(|_| InductiveId {
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
                        x.get().map(|_| ProgramInductiveId {
                            module: ModuleId(m as u32),
                            index: i as u32,
                        })
                    })
            })
            .collect()
    }
}
