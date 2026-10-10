//! Crate/module declarations and materialized-binding provenance.
use super::shared_map::SharedMap;
use crate::raw::{
    exp::{Arena, Exp},
    ids::{DefId, InductiveId, ModuleId, ModuleParamId, ProgramInductiveId, SymbolId},
    inductive::InductiveTypeSpecs,
    program::{ComputationTerm, ComputationType, ValueTerm, ValueType},
    program_inductive::ProgramInductiveTypeSpecs,
};
use kernel::sharing::{ContextId, ContextInterner};
use rustc_hash::FxHashMap;
use std::{
    cell::{Cell, OnceCell, RefCell},
    collections::{HashMap, HashSet},
    sync::Arc,
};

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub enum DefinedConstant {
    Contextual {
        parameters: Vec<(SymbolId, Exp)>,
        ty: Exp,
        body: Exp,
    },
    Pts {
        ty: Exp,
        body: Exp,
    },
    ProgramValue {
        ty: ValueType,
        body: ValueTerm,
    },
    ProgramComputation {
        ty: ComputationType,
        body: ComputationTerm,
    },
}

impl DefinedConstant {
    fn kind_name(&self) -> &'static str {
        match self {
            Self::Contextual { .. } => "contextual definition",
            Self::Pts { .. } => "Set/Prop",
            Self::ProgramValue { .. } => "Program value",
            Self::ProgramComputation { .. } => "Program computation",
        }
    }
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct ModuleParameter {
    pub name: SymbolId,
    pub kind: ModuleParameterKind,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy)]
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(serde::Serialize, serde::Deserialize, Debug)]
pub struct NamespaceBinding {
    pub source: ModuleId,
    pub materialized: ModuleId,
    pub arguments: Vec<(ModuleParamId, ModuleArgument)>,
    /// Maps definitions in `materialized` back to definitions in `source`.
    pub definition_origins: HashMap<DefId, DefId>,
    pub(crate) remapping: RemappingId,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct RemappingId(usize);

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Default)]
pub(crate) struct DeclarationRemapping {
    pub module_ids: SharedMap<ModuleId>,
    pub definition_ids: SharedMap<DefId>,
    pub inductive_ids: SharedMap<InductiveId>,
    pub program_inductive_ids: SharedMap<ProgramInductiveId>,
}

impl DeclarationRemapping {
    /// Retain source identities across another specialization of an import.
    pub(crate) fn after(&self, previous: &Self) -> Self {
        Self {
            module_ids: self.module_ids.after(&previous.module_ids),
            definition_ids: self.definition_ids.after(&previous.definition_ids),
            inductive_ids: self.inductive_ids.after(&previous.inductive_ids),
            program_inductive_ids: self
                .program_inductive_ids
                .after(&previous.program_inductive_ids),
        }
    }
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
struct LazyDefinition {
    source: DefId,
    substitutions: Arc<[(ModuleParamId, ModuleArgument)]>,
    reflected_substitutions: Arc<[(ModuleParamId, Exp)]>,
    remapping: RemappingId,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
struct LazyInductive {
    source: InductiveId,
    substitutions: Arc<[(ModuleParamId, Exp)]>,
    remapping: RemappingId,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
struct LazyProgramInductive {
    source: ProgramInductiveId,
    substitutions: Arc<[(ModuleParamId, ModuleArgument)]>,
    remapping: RemappingId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefinitionOrigin {
    pub binding: ModuleId,
    pub source: DefId,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct MaterializationStats {
    pub definitions: usize,
    pub inductives: usize,
    pub datatypes: usize,
}

#[derive(serde::Serialize, serde::Deserialize, Debug)]
pub struct ModuleEnv {
    name: String,
    parent: Option<ModuleId>,
    children: Vec<ModuleId>,
    parameters: Vec<ModuleParameter>,
    #[serde(with = "cells")]
    definitions: Vec<OnceCell<DefinedConstant>>,
    #[serde(with = "cells")]
    inductives: Vec<OnceCell<InductiveTypeSpecs>>,
    #[serde(with = "cells")]
    program_inductives: Vec<OnceCell<ProgramInductiveTypeSpecs>>,
    items: Vec<ModuleItem>,
    names: HashMap<String, usize>,
    hir_names: HashMap<String, resolve::hir::BindingId>,
    hir_items: HashMap<resolve::hir::BindingId, usize>,
    bindings: Vec<ModuleId>,
    imports: HashMap<String, ModuleId>,
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
            hir_names: HashMap::new(),
            hir_items: HashMap::new(),
            bindings: Vec::new(),
            imports: HashMap::new(),
        }
    }

    pub fn hir_item(&self, binding: resolve::hir::BindingId) -> Option<&ModuleItem> {
        self.hir_items
            .get(&binding)
            .map(|index| &self.items[*index])
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

    pub fn bindings(&self) -> &[ModuleId] {
        &self.bindings
    }

    pub fn import(&self, name: &str) -> Option<ModuleId> {
        self.imports.get(name).copied()
    }
}

type InferenceCache = FxHashMap<(Exp, ContextId), Exp>;
// ArgumentCache owns each telescope once, across all declaration kinds.
type ExactSpecializations<I> = HashMap<(I, usize), I>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ClosedNamespaceKey {
    pub base: Option<ModuleId>,
    pub route: Vec<(ModuleId, usize, usize)>,
    pub arguments: Vec<(ModuleParamId, ModuleArgument)>,
}

#[derive(serde::Serialize, serde::Deserialize, Debug)]
pub struct CrateEnv {
    pub(crate) kernel: RefCell<kernel::environment::Environment>,
    pub(crate) kernel_definitions: RefCell<HashMap<DefId, kernel::ids::DefinitionId>>,
    hir_symbols: HashMap<resolve::hir::BindingId, SymbolId>,
    definition_parameters: HashMap<DefId, Vec<SymbolId>>,
    arena: Arena,
    #[serde(skip)]
    pub(crate) inference_cache: std::cell::RefCell<InferenceCache>,
    #[serde(skip)]
    pub(crate) contexts: RefCell<ContextInterner<Exp>>,
    // Raw nodes and registered declarations are immutable. Weak-head reduction
    // depends only on those, not on the elaborator's context or meta assignments.
    #[serde(skip)]
    pub(crate) whnf_cache: RefCell<FxHashMap<Exp, Exp>>,
    // Structural translation always uses nominal base zero, the root module,
    // and a synthetic telescope determined by the immutable expression and its
    // captures. Successful translations without metas can share their result.
    #[serde(skip)]
    pub(crate) structural_expressions: RefCell<FxHashMap<Exp, kernel::syntax::Expression>>,
    // Repeated declarations in an imported scope compare the same immutable
    // arguments. Retain resolved comparisons after ordinary conversion.
    #[serde(skip)]
    pub(crate) namespace_shareability: RefCell<FxHashMap<Exp, bool>>,
    #[serde(skip)]
    pub(crate) namespace_conversion_cache: RefCell<FxHashMap<(Exp, Exp), bool>>,
    #[serde(skip)]
    pub(crate) namespace_substitution_cache: RefCell<super::namespaces::SubstitutionCache>,
    #[serde(skip)]
    pub(crate) namespace_argument_cache: RefCell<super::namespaces::ArgumentCache>,
    symbols: Vec<String>,
    symbol_ids: HashMap<String, SymbolId>,
    modules: Vec<ModuleEnv>,
    namespace_bindings: HashMap<ModuleId, NamespaceBinding>,
    #[serde(skip)]
    pub(crate) closed_namespaces: HashMap<ClosedNamespaceKey, (ModuleId, Vec<ModuleId>)>,
    remappings: Vec<DeclarationRemapping>,
    checking_scopes: HashMap<ModuleId, ModuleId>,
    checking_contexts: HashMap<ModuleId, crate::raw::exp::ExpContext>,
    checking_program_contexts: HashMap<ModuleId, crate::raw::program::ProgramContext>,
    lazy_definitions: HashMap<DefId, LazyDefinition>,
    lazy_inductives: HashMap<InductiveId, LazyInductive>,
    nominal_definitions: HashMap<DefId, super::namespaces::Specialization<DefId>>,
    nominal_inductives: HashMap<InductiveId, super::namespaces::Specialization<InductiveId>>,
    prospective_inductives: HashMap<InductiveId, super::namespaces::Specialization<InductiveId>>,
    nominal_datatypes:
        HashMap<ProgramInductiveId, super::namespaces::Specialization<ProgramInductiveId>>,
    // Search equivalent specializations only among the same source declaration.
    // Rebuild these indexes lazily after loading a semantic cache.
    #[serde(skip)]
    definition_specializations: Option<HashMap<DefId, Vec<DefId>>>,
    #[serde(skip)]
    exact_definition_specializations: ExactSpecializations<DefId>,
    #[serde(skip)]
    inductive_specializations: Option<HashMap<InductiveId, Vec<InductiveId>>>,
    #[serde(skip)]
    exact_inductive_specializations: ExactSpecializations<InductiveId>,
    #[serde(skip)]
    datatype_specializations: Option<HashMap<ProgramInductiveId, Vec<ProgramInductiveId>>>,
    #[serde(skip)]
    exact_datatype_specializations: ExactSpecializations<ProgramInductiveId>,
    lazy_program_inductives: HashMap<ProgramInductiveId, LazyProgramInductive>,
    #[serde(skip)]
    materializing_definitions: RefCell<HashSet<DefId>>,
    #[serde(skip)]
    failed_definitions: RefCell<HashMap<DefId, crate::error::Error>>,
    #[serde(skip)]
    materialized_definitions: Cell<usize>,
    #[serde(skip)]
    materialized_inductives: Cell<usize>,
    #[serde(skip)]
    materialized_datatypes: Cell<usize>,
}

impl Default for CrateEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl CrateEnv {
    /// Retained cache entries and distinct shared context extensions.
    pub fn cache_counts(&self) -> [(&'static str, usize); 4] {
        let inference = self.inference_cache.borrow();
        [
            ("inference", inference.len()),
            ("context bindings", self.contexts.borrow().len()),
            ("weak heads", self.whnf_cache.borrow().len()),
            (
                "structural expressions",
                self.structural_expressions.borrow().len(),
            ),
        ]
    }

    pub(crate) fn context_id(&self, context: &super::exp::ExpContext) -> ContextId {
        self.contexts
            .borrow_mut()
            .intern(context.iter().map(|b| b.ty))
    }

    pub fn new() -> Self {
        let anonymous = "_".to_string();
        let root = "root".to_string();
        let mut symbol_ids = HashMap::new();
        symbol_ids.insert(anonymous.clone(), SymbolId::ANONYMOUS);
        symbol_ids.insert(root.clone(), SymbolId(1));
        let arena = Arena::new();
        let kernel = RefCell::new(kernel::environment::Environment::with_arena(
            arena.core.clone(),
        ));
        Self {
            kernel,
            kernel_definitions: Default::default(),
            hir_symbols: HashMap::new(),
            definition_parameters: HashMap::new(),
            arena,
            inference_cache: Default::default(),
            contexts: Default::default(),
            whnf_cache: Default::default(),
            structural_expressions: Default::default(),
            namespace_shareability: Default::default(),
            namespace_conversion_cache: Default::default(),
            namespace_substitution_cache: Default::default(),
            namespace_argument_cache: Default::default(),
            symbols: vec![anonymous, root],
            symbol_ids,
            modules: vec![ModuleEnv::new("root".into(), None, vec![])],
            namespace_bindings: HashMap::new(),
            closed_namespaces: HashMap::new(),
            remappings: vec![DeclarationRemapping::default()],
            checking_scopes: HashMap::new(),
            checking_contexts: HashMap::new(),
            checking_program_contexts: HashMap::new(),
            lazy_definitions: HashMap::new(),
            lazy_inductives: HashMap::new(),
            nominal_definitions: HashMap::new(),
            nominal_inductives: HashMap::new(),
            prospective_inductives: HashMap::new(),
            nominal_datatypes: HashMap::new(),
            definition_specializations: None,
            exact_definition_specializations: HashMap::new(),
            inductive_specializations: None,
            exact_inductive_specializations: HashMap::new(),
            datatype_specializations: None,
            exact_datatype_specializations: HashMap::new(),
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

    pub fn intern_name(&mut self, name: &crate::hir::Identifier) -> SymbolId {
        let Some(id) = name.1 else {
            return self.intern(name.as_str());
        };
        if let Some(symbol) = self.hir_symbols.get(&id) {
            return *symbol;
        }
        let symbol =
            SymbolId(u32::try_from(self.symbols.len()).expect("symbol table exceeded u32::MAX"));
        self.symbols.push(name.0.clone());
        self.hir_symbols.insert(id, symbol);
        symbol
    }

    pub fn name_matches(&self, symbol: SymbolId, name: &crate::hir::Identifier) -> bool {
        name.1.map_or_else(
            || self.symbol(symbol) == name.as_str(),
            |id| self.hir_symbols.get(&id) == Some(&symbol),
        )
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
        self.add_module_entry("<binding>".into(), None, vec![])
    }

    /// An unpublished binding inherits the importing module's checking scope.
    #[cfg(test)]
    pub(crate) fn add_module_in_scope(
        &mut self,
        owner: ModuleId,
        context: crate::raw::exp::ExpContext,
    ) -> Result<ModuleId, crate::error::Error> {
        Ok(self.add_modules_in_scope(owner, context, 1)?.remove(0))
    }

    /// Validate a common context once before allocating one import graph.
    /// Every namespace receives exactly that immutable checking telescope.
    pub(crate) fn add_modules_in_scope(
        &mut self,
        owner: ModuleId,
        mut context: crate::raw::exp::ExpContext,
        count: usize,
    ) -> Result<Vec<ModuleId>, crate::error::Error> {
        if count == 0 {
            return Ok(Vec::new());
        }
        crate::raw::derivation::CheckSession::new(self, &mut context)
            .check_wellformed_context()
            .map_err(crate::error::Error::from)?;
        let mut modules = Vec::with_capacity(count);
        for _ in 0..count {
            let module = self.add_module();
            self.checking_scopes.insert(module, owner);
            self.checking_contexts.insert(module, context.clone());
            modules.push(module);
        }
        Ok(modules)
    }

    #[cfg(test)]
    pub(crate) fn add_child_module(
        &mut self,
        parent: ModuleId,
        name: String,
        parameters: Vec<ModuleParameter>,
    ) -> Result<ModuleId, crate::error::Error> {
        Ok(self.add_module_entry(name, Some(parent), parameters))
    }

    pub fn reserve_child_module(&mut self, parent: ModuleId, name: String) -> ModuleId {
        self.add_module_entry(name, Some(parent), vec![])
    }

    pub fn add_module_parameter(&mut self, module: ModuleId, parameter: ModuleParameter) {
        self.module_mut(module).parameters.push(parameter);
    }

    pub fn publish_child_module(&mut self, child: ModuleId) -> Result<(), crate::error::Error> {
        let parent = self.module(child).parent.ok_or_else(|| {
            crate::error::Error::Invalid(
                crate::error::Invalid::RootOrMaterializedModuleCannotBePublishedAsAChild,
            )
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

    /// Resolve an import alias in the module's lexical scope.
    ///
    /// Child modules inherit aliases from their parents.  An alias declared in
    /// the child shadows an alias with the same name in an enclosing module.
    pub fn resolve_import(&self, mut module: ModuleId, name: &str) -> Option<ModuleId> {
        loop {
            if let Some(binding) = self.module(module).import(name) {
                return Some(binding);
            }
            module = self.module(module).parent()?;
        }
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
    ) -> Result<DefId, crate::error::Error> {
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
    ) -> Result<DefId, crate::error::Error> {
        let span = tracing::debug_span!(target: "ref_type::environment",
            "register_definition", ?module, kind = definition.kind_name());
        let _entered = span.enter();
        let definition = self
            .check_definition(module, &definition, &parameters)
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
    ) -> Result<DefinedConstant, crate::error::Error> {
        use crate::raw::{derivation::CheckSession, program_derivation::ProgramCheckSession};
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
        let mut program_context = self.program_definition_context(module);
        program_context.extend(
            type_parameters
                .iter()
                .map(|var| crate::raw::program::ProgramContextEntry::ValueType { var: *var }),
        );
        match *definition {
            DefinedConstant::Contextual {
                ref parameters,
                ty,
                body,
            } => {
                let mut resolved_parameters = Vec::new();
                for &(var, ty) in parameters {
                    CheckSession::new(self, &mut pts_context)
                        .infer_sort(ty)
                        .map_err(|error| {
                            crate::error::Error::from(error)
                                .context(crate::error::Context::DefinitionParameterCheckFailed)
                        })?;
                    let ty =
                        crate::kernel_bridge::logical(self, &pts_context, &[ty], |_, _, terms| {
                            Ok(Exp(terms[0]))
                        })?;
                    resolved_parameters.push((var, ty));
                    pts_context.push(crate::raw::exp::ExpContextEntry { var, ty });
                }
                let (body, ty) = CheckSession::new(self, &mut pts_context)
                    .check_pts_resolved(body, ty)
                    .map_err(|error| {
                        crate::error::Error::from(error)
                            .context(crate::error::Context::DefinitionBodyCheckFailed)
                    })?;
                return Ok(DefinedConstant::Contextual {
                    parameters: resolved_parameters,
                    ty,
                    body,
                });
            }
            DefinedConstant::Pts { ty, body } => {
                let (body, ty) = CheckSession::new(self, &mut pts_context)
                    .check_pts_resolved(body, ty)
                    .map_err(|error| {
                        crate::error::Error::from(error)
                            .context(crate::error::Context::DefinitionCheckFailed)
                    })?;
                return Ok(DefinedConstant::Pts { ty, body });
            }
            DefinedConstant::ProgramValue { ty, body } => {
                ProgramCheckSession::new(self, &mut program_context)
                    .check_value_term(body, ty)
                    .map_err(|error| {
                        crate::error::Error::from(error)
                            .context(crate::error::Context::ProgramValueDefinitionCheckFailed)
                    })?;
            }
            DefinedConstant::ProgramComputation { ty, body } => {
                ProgramCheckSession::new(self, &mut program_context)
                    .check_computation_term(body, ty)
                    .map_err(|error| {
                        crate::error::Error::from(error)
                            .context(crate::error::Context::ProgramComputationDefinitionCheckFailed)
                    })?;
            }
        }
        Ok(definition.clone())
    }

    pub(crate) fn materialized_definition(&self, id: DefId) -> Option<&DefinedConstant> {
        self.module(id.module)
            .definitions
            .get(id.index as usize)?
            .get()
    }

    pub fn definition(&self, id: DefId) -> &DefinedConstant {
        self.resolve_definition(id)
            .unwrap_or_else(|error| panic!("failed to materialize definition {id:?}: {error}"))
    }

    pub fn resolve_definition(&self, id: DefId) -> Result<&DefinedConstant, crate::error::Error> {
        let _cost = timing::costs::Scope::enter("materialize.definition");
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
            .ok_or_else(|| crate::error::Error::ReservedDefinitionUsed { id })?;
        if !self.materializing_definitions.borrow_mut().insert(id) {
            return Err(crate::error::Error::CyclicDefinition { id });
        }
        let result: Result<&DefinedConstant, crate::error::Error> = (|| {
            let source = self.resolve_definition(lazy.source)?.clone();
            let count = self.definition_parameters(id).len();
            let shifted_substitutions = lazy
                .substitutions
                .iter()
                .map(|(p, a)| {
                    use super::traversal::Term;
                    let a = match *a {
                        ModuleArgument::Pts(e) => {
                            let Term::Logical(e) = Term::Logical(e).shift(self.arena(), count, 0)
                            else {
                                unreachable!()
                            };
                            ModuleArgument::Pts(e)
                        }
                        ModuleArgument::ProgramType(t) => {
                            let Term::ValueType(t) =
                                Term::ValueType(t).shift(self.arena(), count, 0)
                            else {
                                unreachable!()
                            };
                            ModuleArgument::ProgramType(t)
                        }
                        ModuleArgument::ProgramValue(v) => {
                            let Term::Value(v) = Term::Value(v).shift(self.arena(), count, 0)
                            else {
                                unreachable!()
                            };
                            ModuleArgument::ProgramValue(v)
                        }
                    };
                    (*p, a)
                })
                .collect::<Vec<_>>();
            let reflected = lazy
                .reflected_substitutions
                .iter()
                .map(|(p, e)| {
                    (
                        *p,
                        crate::kernel_bridge::shift_bound_indices(self.arena(), *e, count, 0),
                    )
                })
                .collect::<Vec<_>>();
            let remap = self.remapping(lazy.remapping);
            let logical_at = |e, depth| {
                let shifted;
                let substitutions = if depth == 0 {
                    &reflected
                } else {
                    // Alias parameters bind outside each stored expression.
                    shifted = reflected
                        .iter()
                        .map(|&(p, value)| {
                            (
                                p,
                                crate::kernel_bridge::shift_bound_indices(
                                    self.arena(),
                                    value,
                                    depth,
                                    0,
                                ),
                            )
                        })
                        .collect::<Vec<_>>();
                    &shifted
                };
                crate::raw::remapping::exp_subst_map(
                    self.arena(),
                    crate::raw::remapping::remap_all_global_ids(
                        self.arena(),
                        e,
                        &remap.definition_ids,
                        &remap.inductive_ids,
                        &remap.program_inductive_ids,
                    ),
                    substitutions,
                )
            };
            let logical = |e| logical_at(e, 0);
            let value_ty = |t| {
                crate::raw::remapping::subst_value_type_module_params(
                    self.arena(),
                    crate::raw::remapping::remap_value_type_global_ids(
                        self.arena(),
                        t,
                        &remap.definition_ids,
                        &remap.program_inductive_ids,
                    ),
                    &shifted_substitutions,
                )
            };
            let comp_ty = |t| {
                crate::raw::remapping::subst_computation_type_module_params(
                    self.arena(),
                    crate::raw::remapping::remap_computation_type_global_ids(
                        self.arena(),
                        t,
                        &remap.definition_ids,
                        &remap.program_inductive_ids,
                    ),
                    &shifted_substitutions,
                )
            };
            let definition = match source {
                DefinedConstant::Contextual {
                    parameters,
                    ty,
                    body,
                } => {
                    let depth = parameters.len();
                    DefinedConstant::Contextual {
                        parameters: parameters
                            .into_iter()
                            .enumerate()
                            .map(|(depth, (var, ty))| (var, logical_at(ty, depth)))
                            .collect(),
                        ty: logical_at(ty, depth),
                        body: logical_at(body, depth),
                    }
                }
                DefinedConstant::Pts { ty, body } => DefinedConstant::Pts {
                    ty: logical(ty),
                    body: logical(body),
                },
                DefinedConstant::ProgramValue { ty, body } => DefinedConstant::ProgramValue {
                    ty: value_ty(ty),
                    body: crate::raw::remapping::subst_value_module_params(
                        self.arena(),
                        crate::raw::remapping::remap_value_global_ids(
                            self.arena(),
                            body,
                            &remap.definition_ids,
                            &remap.program_inductive_ids,
                            &remap.inductive_ids,
                        ),
                        &shifted_substitutions,
                        &reflected,
                    ),
                },
                DefinedConstant::ProgramComputation { ty, body } => {
                    DefinedConstant::ProgramComputation {
                        ty: comp_ty(ty),
                        body: crate::raw::remapping::subst_computation_module_params(
                            self.arena(),
                            crate::raw::remapping::remap_computation_global_ids(
                                self.arena(),
                                body,
                                &remap.definition_ids,
                                &remap.program_inductive_ids,
                                &remap.inductive_ids,
                            ),
                            &shifted_substitutions,
                            &reflected,
                        ),
                    }
                }
            };
            let definition = self
                .check_definition(id.module, &definition, self.definition_parameters(id))
                .map_err(|error| {
                    error.context(crate::error::Context::SpecializingDefinition {
                        name: (super::printing::definition_name(self, lazy.source)).to_owned(),
                    })
                })?;
            slot.set(definition)
                .map_err(|_| crate::error::Error::DuplicateMaterialization { id })?;
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
        substitutions: impl Into<Arc<[(ModuleParamId, ModuleArgument)]>>,
        reflected_substitutions: impl Into<Arc<[(ModuleParamId, Exp)]>>,
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
                substitutions: substitutions.into(),
                reflected_substitutions: reflected_substitutions.into(),
                remapping: RemappingId(0),
            },
        );
        id
    }

    pub(crate) fn reuse_lazy_definition(
        &mut self,
        id: DefId,
        substitutions: &[(ModuleParamId, ModuleArgument)],
        reflected_substitutions: &[(ModuleParamId, Exp)],
        remapping: &DeclarationRemapping,
    ) -> (DefId, DefId, bool) {
        let _cost = timing::costs::Scope::enter("namespace.reuse-definition");
        let source = self.lazy_definitions[&id].source;
        let origin = self
            .nominal_definitions
            .get(&source)
            .cloned()
            .unwrap_or_else(|| super::namespaces::Specialization {
                source,
                arguments: self.namespace_arguments(source.module),
            });
        let arguments = self.substitute_namespace_arguments(
            &origin.arguments,
            substitutions,
            reflected_substitutions,
            remapping,
        );
        let shareable = self.namespace_arguments_shareable(&arguments);
        let exact_key = (
            origin.source,
            self.namespace_argument_cache
                .borrow_mut()
                .intern(&arguments),
        );
        if shareable && let Some(&canonical) = self.exact_definition_specializations.get(&exact_key)
        {
            return (source, canonical, false);
        }
        if self
            .namespace_arguments_equal(&arguments, &self.namespace_arguments(origin.source.module))
        {
            if shareable {
                self.exact_definition_specializations
                    .insert(exact_key, origin.source);
            }
            return (source, origin.source, false);
        }
        if shareable {
            if self.definition_specializations.is_none() {
                let mut index: HashMap<_, Vec<_>> = HashMap::new();
                for (&id, specialization) in &self.nominal_definitions {
                    if self.namespace_arguments_shareable(&specialization.arguments) {
                        index.entry(specialization.source).or_default().push(id);
                    }
                }
                self.definition_specializations = Some(index);
            }
            let candidates = self
                .definition_specializations
                .as_ref()
                .unwrap()
                .get(&origin.source)
                .cloned()
                .unwrap_or_default();
            if let Some(id) = candidates.into_iter().find(|id| {
                let candidate = &self.nominal_definitions[id].arguments;
                !self.namespace_arguments_rigidly_differ(&arguments, candidate)
                    && self.namespace_arguments_equal(&arguments, candidate)
            }) {
                self.exact_definition_specializations.insert(exact_key, id);
                return (source, id, false);
            }
        }
        if shareable && let Some(index) = &mut self.definition_specializations {
            index.entry(origin.source).or_default().push(id);
        }
        if shareable {
            self.exact_definition_specializations.insert(exact_key, id);
        }
        self.nominal_definitions.insert(
            id,
            super::namespaces::Specialization {
                source: origin.source,
                arguments,
            },
        );
        (source, id, true)
    }

    pub(crate) fn set_lazy_definition_remapping(&mut self, id: DefId, remapping: RemappingId) {
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
                .remap_global_ids(
                    self.arena(),
                    &self.remapping(lazy.remapping).definition_ids,
                    &self.remapping(lazy.remapping).inductive_ids,
                )
                .instantiate(self.arena(), &lazy.substitutions);
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
        reflected_substitutions: impl Into<Arc<[(ModuleParamId, Exp)]>>,
    ) -> InductiveId {
        let id = self.reserve_inductive(module);
        self.lazy_inductives.insert(
            id,
            LazyInductive {
                source,
                substitutions: reflected_substitutions.into(),
                remapping: RemappingId(0),
            },
        );
        id
    }

    pub(crate) fn definition_specialization_arguments(
        &self,
        id: DefId,
    ) -> Vec<(ModuleParamId, ModuleArgument)> {
        self.nominal_definitions.get(&id).map_or_else(
            || self.namespace_arguments(id.module),
            |origin| origin.arguments.clone(),
        )
    }

    pub(crate) fn definition_specialization_source(&self, id: DefId) -> DefId {
        self.nominal_definitions.get(&id).map_or_else(
            || {
                self.definition_origin(id)
                    .map_or(id, |origin| origin.source)
            },
            |origin| origin.source,
        )
    }

    pub(crate) fn inductive_specialization_arguments(
        &self,
        id: InductiveId,
    ) -> Vec<(ModuleParamId, ModuleArgument)> {
        self.inductive_specialization(id).map_or_else(
            || self.namespace_arguments(id.module),
            |origin| origin.arguments.clone(),
        )
    }

    pub(crate) fn datatype_specialization_arguments(
        &self,
        id: ProgramInductiveId,
    ) -> Vec<(ModuleParamId, ModuleArgument)> {
        self.nominal_datatypes.get(&id).map_or_else(
            || self.namespace_arguments(id.module),
            |origin| origin.arguments.clone(),
        )
    }

    pub(crate) fn is_program_mirror(&self, id: InductiveId) -> bool {
        let source = self
            .inductive_specialization(id)
            .map_or(id, |origin| origin.source);
        self.module(source.module)
            .program_inductives
            .iter()
            .filter_map(OnceCell::get)
            .any(|spec| spec.reflected() == source)
    }

    pub(crate) fn inductive_specialization(
        &self,
        id: InductiveId,
    ) -> Option<&super::namespaces::Specialization<InductiveId>> {
        self.nominal_inductives
            .get(&id)
            .or_else(|| self.prospective_inductives.get(&id))
    }

    /// Conversion during namespace canonicalization may lower a referenced type
    /// before its own reuse pass. Its original identity and substituted captures
    /// must already be available; otherwise that lowering registers a provisional
    /// nominal type with the caller's captures instead of the source arguments.
    pub(crate) fn preview_lazy_inductive(
        &mut self,
        id: InductiveId,
        substitutions: &[(ModuleParamId, ModuleArgument)],
        reflected_substitutions: &[(ModuleParamId, Exp)],
        remapping: &DeclarationRemapping,
    ) {
        let source = self.lazy_inductives[&id].source;
        let origin = self
            .inductive_specialization(source)
            .cloned()
            .unwrap_or_else(|| super::namespaces::Specialization {
                source,
                arguments: self.namespace_arguments(source.module),
            });
        let arguments = self.substitute_namespace_arguments(
            &origin.arguments,
            substitutions,
            reflected_substitutions,
            remapping,
        );
        self.prospective_inductives.insert(
            id,
            super::namespaces::Specialization {
                source: origin.source,
                arguments,
            },
        );
    }

    pub(crate) fn reuse_lazy_inductive(
        &mut self,
        id: InductiveId,
        substitutions: &[(ModuleParamId, ModuleArgument)],
        reflected_substitutions: &[(ModuleParamId, Exp)],
        remapping: &DeclarationRemapping,
    ) -> (InductiveId, InductiveId, bool) {
        let _cost = timing::costs::Scope::enter("namespace.reuse-inductive");
        let source = self.lazy_inductives[&id].source;
        let origin = self
            .nominal_inductives
            .get(&source)
            .cloned()
            .unwrap_or_else(|| super::namespaces::Specialization {
                source,
                arguments: self.namespace_arguments(source.module),
            });
        let arguments = self.substitute_namespace_arguments(
            &origin.arguments,
            substitutions,
            reflected_substitutions,
            remapping,
        );
        self.prospective_inductives.insert(
            id,
            super::namespaces::Specialization {
                source: origin.source,
                arguments: arguments.clone(),
            },
        );
        let shareable = self.namespace_arguments_shareable(&arguments);
        let exact_key = (
            origin.source,
            self.namespace_argument_cache
                .borrow_mut()
                .intern(&arguments),
        );
        if shareable && let Some(&canonical) = self.exact_inductive_specializations.get(&exact_key)
        {
            return (source, canonical, false);
        }
        if self
            .namespace_arguments_equal(&arguments, &self.namespace_arguments(origin.source.module))
        {
            if shareable {
                self.exact_inductive_specializations
                    .insert(exact_key, origin.source);
            }
            return (source, origin.source, false);
        }
        if shareable {
            let candidates = self.inductive_specializations.get_or_insert_with(|| {
                let mut index: HashMap<_, Vec<_>> = HashMap::new();
                for (&id, specialization) in &self.nominal_inductives {
                    index.entry(specialization.source).or_default().push(id);
                }
                index
            });
            let candidates = candidates.get(&origin.source).cloned().unwrap_or_default();
            if let Some(id) = candidates.into_iter().find(|id| {
                let candidate = &self.nominal_inductives[id].arguments;
                !self.namespace_arguments_rigidly_differ(&arguments, candidate)
                    && self.namespace_arguments_shareable(candidate)
                    && self.namespace_arguments_equal(&arguments, candidate)
            }) {
                self.exact_inductive_specializations.insert(exact_key, id);
                return (source, id, false);
            }
        }
        if let Some(index) = &mut self.inductive_specializations {
            index.entry(origin.source).or_default().push(id);
        }
        if shareable {
            self.exact_inductive_specializations.insert(exact_key, id);
        }
        self.nominal_inductives.insert(
            id,
            super::namespaces::Specialization {
                source: origin.source,
                arguments,
            },
        );
        (source, id, true)
    }

    pub(crate) fn set_lazy_inductive_remapping(&mut self, id: InductiveId, remapping: RemappingId) {
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

    pub(crate) fn has_program_inductive(&self, id: ProgramInductiveId) -> bool {
        self.module(id.module)
            .program_inductives
            .get(id.index as usize)
            .is_some_and(|slot| {
                slot.get().is_some() || self.lazy_program_inductives.contains_key(&id)
            })
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
                .remap_global_ids(
                    self.arena(),
                    &self.remapping(lazy.remapping).definition_ids,
                    &self.remapping(lazy.remapping).inductive_ids,
                    &self.remapping(lazy.remapping).program_inductive_ids,
                )
                .instantiate(self.arena(), &lazy.substitutions);
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
        substitutions: impl Into<Arc<[(ModuleParamId, ModuleArgument)]>>,
    ) -> ProgramInductiveId {
        let id = self.reserve_program_inductive(module);
        self.lazy_program_inductives.insert(
            id,
            LazyProgramInductive {
                source,
                substitutions: substitutions.into(),
                remapping: RemappingId(0),
            },
        );
        id
    }

    pub(crate) fn reuse_lazy_program_inductive(
        &mut self,
        id: ProgramInductiveId,
        substitutions: &[(ModuleParamId, ModuleArgument)],
        reflected_substitutions: &[(ModuleParamId, Exp)],
        remapping: &DeclarationRemapping,
    ) -> (ProgramInductiveId, ProgramInductiveId, bool) {
        let _cost = timing::costs::Scope::enter("namespace.reuse-datatype");
        let source = self.lazy_program_inductives[&id].source;
        let origin = self
            .nominal_datatypes
            .get(&source)
            .cloned()
            .unwrap_or_else(|| super::namespaces::Specialization {
                source,
                arguments: self.namespace_arguments(source.module),
            });
        let arguments = self.substitute_namespace_arguments(
            &origin.arguments,
            substitutions,
            reflected_substitutions,
            remapping,
        );
        let shareable = self.namespace_arguments_shareable(&arguments);
        let exact_key = (
            origin.source,
            self.namespace_argument_cache
                .borrow_mut()
                .intern(&arguments),
        );
        if shareable && let Some(&canonical) = self.exact_datatype_specializations.get(&exact_key) {
            return (source, canonical, false);
        }
        if self
            .namespace_arguments_equal(&arguments, &self.namespace_arguments(origin.source.module))
        {
            if shareable {
                self.exact_datatype_specializations
                    .insert(exact_key, origin.source);
            }
            return (source, origin.source, false);
        }
        if shareable {
            let candidates = self.datatype_specializations.get_or_insert_with(|| {
                let mut index: HashMap<_, Vec<_>> = HashMap::new();
                for (&id, specialization) in &self.nominal_datatypes {
                    index.entry(specialization.source).or_default().push(id);
                }
                index
            });
            let candidates = candidates.get(&origin.source).cloned().unwrap_or_default();
            if let Some(id) = candidates.into_iter().find(|id| {
                let candidate = &self.nominal_datatypes[id].arguments;
                !self.namespace_arguments_rigidly_differ(&arguments, candidate)
                    && self.namespace_arguments_shareable(candidate)
                    && self.namespace_arguments_equal(&arguments, candidate)
            }) {
                self.exact_datatype_specializations.insert(exact_key, id);
                return (source, id, false);
            }
        }
        if let Some(index) = &mut self.datatype_specializations {
            index.entry(origin.source).or_default().push(id);
        }
        if shareable {
            self.exact_datatype_specializations.insert(exact_key, id);
        }
        self.nominal_datatypes.insert(
            id,
            super::namespaces::Specialization {
                source: origin.source,
                arguments,
            },
        );
        (source, id, true)
    }

    pub(crate) fn set_lazy_program_inductive_remapping(
        &mut self,
        id: ProgramInductiveId,
        remapping: RemappingId,
    ) {
        self.lazy_program_inductives
            .get_mut(&id)
            .expect("lazy Program inductive")
            .remapping = remapping;
    }

    pub(crate) fn add_namespace_binding(
        &mut self,
        owner: ModuleId,
        source: ModuleId,
        materialized: ModuleId,
        arguments: Vec<(ModuleParamId, ModuleArgument)>,
        definition_origins: HashMap<DefId, DefId>,
        remapping: RemappingId,
    ) -> ModuleId {
        self.module_mut(owner).bindings.push(materialized);
        let previous = self.namespace_bindings.insert(
            materialized,
            NamespaceBinding {
                source,
                materialized,
                arguments,
                definition_origins,
                remapping,
            },
        );
        assert!(previous.is_none(), "namespace alias already bound");
        materialized
    }

    pub(crate) fn attach_namespace_binding(&mut self, owner: ModuleId, binding: ModuleId) {
        debug_assert!(self.namespace_bindings.contains_key(&binding));
        if !self.module(owner).bindings.contains(&binding) {
            self.module_mut(owner).bindings.push(binding);
        }
    }

    pub fn binding(&self, namespace: ModuleId) -> &NamespaceBinding {
        &self.namespace_bindings[&namespace]
    }

    pub fn namespace_binding_id(&self, module: ModuleId) -> Option<ModuleId> {
        self.namespace_bindings
            .contains_key(&module)
            .then_some(module)
    }

    pub fn definition_origin(&self, definition: DefId) -> Option<DefinitionOrigin> {
        let binding = self.namespace_binding_id(definition.module)?;
        let source = *self.binding(binding).definition_origins.get(&definition)?;
        Some(DefinitionOrigin { binding, source })
    }

    pub fn register_hir_name(
        &mut self,
        module: ModuleId,
        binding: resolve::hir::BindingId,
        name: String,
    ) {
        let module = self.module_mut(module);
        if let Some(index) = module.names.get(&name) {
            module.hir_items.insert(binding, *index);
        }
        module.hir_names.insert(name, binding);
    }

    pub fn copy_hir_names(&mut self, source: ModuleId, target: ModuleId) {
        self.module_mut(target).hir_names = self.module(source).hir_names.clone();
    }

    pub fn publish_item(
        &mut self,
        module: ModuleId,
        item: ModuleItem,
    ) -> Result<(), crate::error::Error> {
        let module = self.module_mut(module);
        let name = item.name().to_owned();
        if module.names.contains_key(&name) {
            return Err(crate::error::Error::DuplicateModuleItem {
                name: (name).to_string(),
            });
        }
        let index = module.items.len();
        module.items.push(item);
        if let Some(binding) = module.hir_names.get(&name) {
            module.hir_items.insert(*binding, index);
        }
        module.names.insert(name, index);
        Ok(())
    }

    pub fn publish_associated_definition(
        &mut self,
        module: ModuleId,
        owner: &str,
        name: String,
        definition: DefId,
    ) -> Result<(), crate::error::Error> {
        let item = self
            .module_mut(module)
            .names
            .get(owner)
            .copied()
            .and_then(|index| self.module_mut(module).items.get_mut(index))
            .ok_or_else(|| crate::error::Error::UnknownAssociatedOwner {
                owner: (owner).to_string(),
            })?;
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
                return Err(crate::error::Error::AssociatedOwnerNotAType {
                    owner: (owner).to_string(),
                });
            }
        };
        if reserved.iter().any(|candidate| candidate == &name)
            || definitions.iter().any(|(candidate, _)| candidate == &name)
        {
            return Err(crate::error::Error::DuplicateAssociatedItem {
                owner: (owner).to_string(),
                name: (name).to_string(),
            });
        }
        definitions.push((name, definition));
        Ok(())
    }

    pub fn publish_import(
        &mut self,
        module: ModuleId,
        name: String,
        binding: ModuleId,
    ) -> Result<(), crate::error::Error> {
        let module = self.module_mut(module);
        if module.imports.contains_key(&name) {
            return Err(crate::error::Error::DuplicateModuleImport {
                name: (name).to_string(),
            });
        }
        module.imports.insert(name, binding);
        Ok(())
    }

    pub(crate) fn item_for_inductive(&self, inductive: InductiveId) -> Option<&ModuleItem> {
        self.modules.iter().flat_map(ModuleEnv::items).find(|item| {
            matches!(item,
                ModuleItem::Inductive { inductive: candidate, .. }
                | ModuleItem::Record { inductive: candidate, .. }
                | ModuleItem::ProgramInductive { reflected: candidate, .. }
                if *candidate == inductive)
        })
    }

    pub fn record_for_inductive(&self, inductive: InductiveId) -> Option<&ModuleItem> {
        self.modules.iter().flat_map(ModuleEnv::items).find(|item| {
            matches!(item, ModuleItem::Record { inductive: candidate, .. } if *candidate == inductive)
        })
    }

    pub fn program_record_for_inductive(
        &self,
        inductive: ProgramInductiveId,
    ) -> Option<&ModuleItem> {
        self.modules.iter().flat_map(ModuleEnv::items).find(|item| {
            matches!(
                item,
                ModuleItem::ProgramInductive {
                    record_fields: Some(_),
                    inductive: candidate,
                    ..
                } if *candidate == inductive
            )
        })
    }

    pub fn materialization_stats(&self) -> MaterializationStats {
        MaterializationStats {
            definitions: self.materialized_definitions.get(),
            inductives: self.materialized_inductives.get(),
            datatypes: self.materialized_datatypes.get(),
        }
    }

    #[cfg(test)]
    pub fn is_definition_materialized(&self, id: DefId) -> bool {
        self.module(id.module).definitions[id.index as usize]
            .get()
            .is_some()
    }

    #[cfg(test)]
    pub fn is_inductive_materialized(&self, id: InductiveId) -> bool {
        self.module(id.module).inductives[id.index as usize]
            .get()
            .is_some()
    }
}

impl CrateEnv {
    pub(crate) fn set_program_context(
        &mut self,
        module: ModuleId,
        context: crate::raw::program::ProgramContext,
    ) {
        if !context.is_empty() {
            self.checking_program_contexts.insert(module, context);
        }
    }

    pub(crate) fn program_definition_context(
        &self,
        module: ModuleId,
    ) -> crate::raw::program::ProgramContext {
        self.checking_program_contexts
            .get(&module)
            .cloned()
            .unwrap_or_default()
    }

    pub(crate) fn namespace_has_local_context(&self, module: ModuleId) -> bool {
        self.checking_contexts
            .get(&module)
            .is_some_and(|context| !context.is_empty())
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

impl CrateEnv {
    pub(crate) fn store_remapping(&mut self, remapping: DeclarationRemapping) -> RemappingId {
        timing::costs::count("namespace.remapping-owned-capacity", || {
            (remapping.module_ids.capacity()
                + remapping.definition_ids.capacity()
                + remapping.inductive_ids.capacity()
                + remapping.program_inductive_ids.capacity()) as u64
        });
        let id = RemappingId(self.remappings.len());
        self.remappings.push(remapping);
        if self.remappings.len().is_multiple_of(1024)
            && std::env::var_os("REF_TYPE_PROFILE_REMAPPINGS").is_some()
        {
            let mut capacities = [0usize; 4];
            for map in &self.remappings {
                for (total, capacity) in capacities.iter_mut().zip([
                    map.module_ids.capacity(),
                    map.definition_ids.capacity(),
                    map.inductive_ids.capacity(),
                    map.program_inductive_ids.capacity(),
                ]) {
                    *total += capacity;
                }
            }
            eprintln!(
                "remappings={} capacities={capacities:?} arena_nodes={}",
                self.remappings.len(),
                self.arena.core.len()
            );
            eprintln!(
                "raw_caches={:?} kernel_caches={:?}",
                self.cache_counts(),
                self.kernel.try_borrow().map(|env| env.cache_counts())
            );
        }
        id
    }

    pub(crate) fn inherit_namespace_remappings(
        &mut self,
        next: RemappingId,
        bindings: &[(ModuleId, RemappingId)],
    ) {
        let _cost = timing::costs::Scope::enter("namespace.inherit-remappings");
        // Re-exported children use identities from their original namespace.
        // Compose only after all reused namespace redirects have been finalized,
        // and share the result among imports with the same previous context.
        let mut inherited = HashMap::new();
        for &(binding, previous) in bindings {
            let remapping = if let Some(id) = inherited.get(&previous) {
                *id
            } else {
                let composed = self.remapping(next).after(self.remapping(previous));
                let id = self.store_remapping(composed);
                inherited.insert(previous, id);
                id
            };
            self.namespace_bindings.get_mut(&binding).unwrap().remapping = remapping;
        }
    }

    /// Canonicalize a reserved graph before its namespace bindings are published.
    pub(crate) fn reserved_remapping_mut(&mut self, id: RemappingId) -> &mut DeclarationRemapping {
        &mut self.remappings[id.0]
    }

    /// An absent declaration mapping already means the original ID. Keep all
    /// redirects from provisional IDs, but discard redundant identity entries
    /// after canonicalization has finished.
    pub(crate) fn compact_remapping(&mut self, id: RemappingId) {
        let remapping = &mut self.remappings[id.0];
        remapping
            .definition_ids
            .retain(|source, target| source != target);
        remapping
            .inductive_ids
            .retain(|source, target| source != target);
        remapping
            .program_inductive_ids
            .retain(|source, target| source != target);
        remapping.definition_ids.shrink_to_fit();
        remapping.inductive_ids.shrink_to_fit();
        remapping.program_inductive_ids.shrink_to_fit();
    }

    pub(crate) fn remapping(&self, id: RemappingId) -> &DeclarationRemapping {
        &self.remappings[id.0]
    }

    pub(crate) fn restore_shared_arena(&mut self) {
        self.kernel.get_mut().arena = self.arena.core.clone();
    }

    pub(crate) fn refresh_hir_names(
        &mut self,
        modules: &HashMap<resolve::hir::ModuleId, ModuleId>,
        bindings: &HashMap<resolve::hir::BindingId, resolve::Binding>,
    ) {
        for &module in modules.values() {
            self.modules[module.index()].hir_names.clear();
        }
        for (&id, binding) in bindings {
            if binding.parameter.is_none()
                && let Some(&module) = modules.get(&binding.module)
            {
                self.register_hir_name(module, id, binding.name.clone());
            }
        }
    }
}

mod cells {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::cell::OnceCell;

    pub fn serialize<T: Serialize, S: Serializer>(
        cells: &[OnceCell<T>],
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serializer.collect_seq(cells.iter().map(OnceCell::get))
    }

    pub fn deserialize<'de, T: Deserialize<'de>, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<OnceCell<T>>, D::Error> {
        Ok(Vec::<Option<T>>::deserialize(deserializer)?
            .into_iter()
            .map(|value| value.map_or_else(OnceCell::new, OnceCell::from))
            .collect())
    }
}

#[cfg(test)]
mod specialization_tests {
    use super::*;
    use crate::raw::{exp::ExpNode, sort::Sort};

    #[test]
    fn nested_aliases_compare_by_their_original_specialization() {
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let source = env
            .add_definition(
                root,
                DefinedConstant::Pts {
                    ty: env.arena().sort(Sort::SetKind(0)),
                    body: env.arena().sort(Sort::Set(0)),
                },
            )
            .unwrap();
        let namespaces = env.add_modules_in_scope(root, vec![], 2).unwrap();
        let direct = env.reserve_lazy_definition(namespaces[0], source, vec![], vec![]);
        let nested = env.reserve_lazy_definition(namespaces[1], direct, vec![], vec![]);
        let remapping = env.store_remapping(DeclarationRemapping::default());
        env.add_namespace_binding(
            root,
            root,
            namespaces[0],
            vec![],
            HashMap::from([(direct, source)]),
            remapping,
        );
        env.add_namespace_binding(
            root,
            namespaces[0],
            namespaces[1],
            vec![],
            HashMap::from([(nested, direct)]),
            remapping,
        );
        // A serialized namespace graph can retain both a direct and a nested
        // spelling of the same closed specialization. Immediate bindings differ
        // even though the canonical declaration and arguments are identical.
        for id in [direct, nested] {
            env.nominal_definitions.insert(
                id,
                crate::raw::namespaces::Specialization {
                    source,
                    arguments: vec![],
                },
            );
        }
        assert_ne!(
            env.definition_origin(direct).unwrap().source,
            env.definition_origin(nested).unwrap().source
        );
        let registered = env.kernel_definitions.borrow().len();
        assert!(env.namespace_terms_equal(
            env.arena().alloc(ExpNode::DefinedConstant(direct)),
            env.arena().alloc(ExpNode::DefinedConstant(nested))
        ));
        assert_eq!(env.kernel_definitions.borrow().len(), registered);
        assert!(env.materialized_definition(direct).is_none());
        assert!(env.materialized_definition(nested).is_none());

        let different = env
            .add_definition(
                root,
                DefinedConstant::Pts {
                    ty: env.arena().sort(Sort::SetKind(1)),
                    body: env.arena().sort(Sort::Set(1)),
                },
            )
            .unwrap();
        assert!(!env.namespace_terms_equal(
            env.arena().alloc(ExpNode::DefinedConstant(direct)),
            env.arena().alloc(ExpNode::DefinedConstant(different))
        ));
    }
}
