//! Crate/module declarations and materialized-binding provenance.
#[path = "declaration_checkpoint.rs"]
mod declaration_checkpoint;
#[path = "exports.rs"]
pub(crate) mod exports;
#[path = "module_checkpoint.rs"]
mod module_checkpoint;
#[path = "namespace_views.rs"]
mod namespace_views;
#[path = "shared_vectors.rs"]
mod shared_vectors;
use super::definition_map::DefinitionMap;
use super::shared_map::SharedMap;
use crate::raw::{
    exp::{Arena, Exp},
    ids::{DefId, InductiveId, ModuleId, ModuleParamId, ProgramInductiveId, SymbolId},
    inductive::InductiveTypeSpecs,
    program::{ComputationTerm, ComputationType, ValueTerm, ValueType},
    program_inductive::ProgramInductiveTypeSpecs,
};
use kernel::sharing::{ContextId, ContextInterner};
pub use namespace_views::ModuleItems;
#[path = "slots.rs"]
mod slots;
use namespace_views::NamespaceView;
use rustc_hash::FxHashMap;
use slots::Slots;
use std::{
    cell::{Cell, OnceCell, RefCell},
    collections::{HashMap, HashSet},
    hash::{Hash, Hasher},
    rc::Rc,
    sync::Arc,
};

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
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

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct ModuleParameter {
    pub name: SymbolId,
    pub kind: ModuleParameterKind,
}

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone, Copy)]
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

#[derive(
    artifact::Relocate,
    serde::Serialize,
    serde::Deserialize,
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    Hash,
)]
pub enum ModuleArgument {
    Pts(Exp),
    ProgramType(ValueType),
    ProgramValue(ValueTerm),
}

impl ModuleArgument {
    fn shifted(self, arena: &Arena, amount: usize) -> Self {
        let shift = |e| kernel::calculus::shift(&arena.core, e, amount, 0).expect("valid shift");
        match self {
            Self::Pts(e) => Self::Pts(Exp(shift(e.0))),
            Self::ProgramType(t) => Self::ProgramType(ValueType(shift(t.0))),
            Self::ProgramValue(v) => Self::ProgramValue(ValueTerm(shift(v.0))),
        }
    }
}

impl From<Exp> for ModuleArgument {
    fn from(value: Exp) -> Self {
        Self::Pts(value)
    }
}

#[derive(
    artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Eq, Hash,
)]
// Keep the common definition variant small; constructor labels are immutable
// across imports, whereas associated definition identities are specialized.
#[allow(clippy::box_collection)]
pub enum ModuleItem {
    Definition {
        name: Arc<String>,
        definition: DefId,
    },
    Inductive {
        name: Arc<String>,
        constructor_names: Arc<Vec<String>>,
        associated_definitions: Box<Vec<(String, DefId)>>,
        inductive: InductiveId,
    },
    Record {
        name: Arc<String>,
        associated_definitions: Box<Vec<(String, DefId)>>,
        inductive: InductiveId,
    },
    ProgramInductive {
        record_fields: Option<Arc<Vec<String>>>,
        name: Arc<String>,
        constructor_names: Arc<Vec<String>>,
        associated_definitions: Box<Vec<(String, DefId)>>,
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

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct NamespaceBinding {
    pub source: ModuleId,
    pub materialized: ModuleId,
    pub arguments: Arc<[(ModuleParamId, ModuleArgument)]>,
    /// Maps definitions in `materialized` back to definitions in `source`.
    pub definition_origins: HashMap<DefId, DefId>,
    pub(crate) remapping: RemappingId,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct RemappingId(pub(crate) usize);
artifact::identity!(RemappingId, "raw.remapping");

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct RemappingSnapshotId(pub(crate) usize);
artifact::identity!(RemappingSnapshotId, "raw.remapping.snapshot");

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
pub(crate) enum RemappingOrigin {
    Namespace(ModuleId),
    Composition {
        next: RemappingId,
        previous: RemappingId,
    },
}

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone, Default)]
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

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
pub(crate) struct DefinitionEnvironment {
    pub(crate) substitutions: Arc<[(ModuleParamId, ModuleArgument)]>,
    pub(crate) reflected_substitutions: Arc<[(ModuleParamId, Exp)]>,
    pub(crate) remapping: Cell<RemappingId>,
}

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
struct LazyDefinition {
    source: DefId,
    environment: Rc<DefinitionEnvironment>,
}

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
struct LazyInductive {
    source: InductiveId,
    substitutions: Arc<[(ModuleParamId, Exp)]>,
    remapping: RemappingId,
}

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
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

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
struct SourceModule {
    package: String,
    file: Option<syntax::syntax::SourceId>,
    root: resolve::hir::ModuleId,
    ordinal: i64,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ParameterOrder<'a> {
    source: Option<(&'a str, Option<&'a std::path::Path>, i64)>,
    module: u32,
    position: u32,
}

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct ModuleEnv {
    name: String,
    source: Option<Arc<SourceModule>>,
    parent: Option<ModuleId>,
    children: Vec<ModuleId>,
    parameters: Vec<ModuleParameter>,
    #[serde(with = "cells")]
    definitions: Slots<Box<DefinedConstant>>,
    #[serde(with = "cells")]
    inductives: Slots<Box<InductiveTypeSpecs>>,
    #[serde(with = "cells")]
    program_inductives: Slots<Box<ProgramInductiveTypeSpecs>>,
    items: Arc<Vec<ModuleItem>>,
    view: Option<NamespaceView>,
    #[serde(skip)]
    view_items: OnceCell<Slots<Box<ModuleItem>>>,
    names: Arc<HashMap<String, usize>>,
    hir_names: Arc<HashMap<String, resolve::hir::BindingId>>,
    hir_items: Arc<HashMap<resolve::hir::BindingId, usize>>,
    bindings: Vec<ModuleId>,
    imports: HashMap<String, ModuleId>,
}

impl ModuleEnv {
    fn new(name: String, parent: Option<ModuleId>, parameters: Vec<ModuleParameter>) -> Self {
        Self {
            name,
            source: None,
            parent,
            children: Vec::new(),
            parameters,
            definitions: Slots::default(),
            inductives: Slots::default(),
            program_inductives: Slots::default(),
            items: Arc::default(),
            view: None,
            view_items: OnceCell::new(),
            names: Arc::default(),
            hir_names: Arc::default(),
            hir_items: Arc::default(),
            bindings: Vec::new(),
            imports: HashMap::new(),
        }
    }

    pub fn hir_item(&self, binding: resolve::hir::BindingId) -> Option<&ModuleItem> {
        self.hir_items
            .get(&binding)
            .map(|index| self.item_at(*index))
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

    pub fn items(&self) -> ModuleItems<'_> {
        ModuleItems(self)
    }

    fn item_at(&self, index: usize) -> &ModuleItem {
        let Some(view) = &self.view else {
            return &self.items[index];
        };
        if view.identity == view.source {
            return &self.items[index];
        }
        let slots = self
            .view_items
            .get_or_init(|| Slots::reserved(self.items.len()));
        slots[index].get_or_init(|| {
            let mut item = self.items[index].clone();
            view.map_item(&mut item);
            Box::new(item)
        })
    }

    pub fn item(&self, name: &str) -> Option<&ModuleItem> {
        self.names.get(name).map(|index| self.item_at(*index))
    }

    pub fn bindings(&self) -> &[ModuleId] {
        &self.bindings
    }

    pub fn import(&self, name: &str) -> Option<ModuleId> {
        self.imports.get(name).copied()
    }

    pub(crate) fn names_binding(&self, binding: ModuleId) -> bool {
        self.imports.values().any(|&id| id == binding)
    }
}

type InferenceCache = FxHashMap<(Exp, ContextId), Exp>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct NamespaceInstanceKey {
    pub scope: Option<(ModuleId, crate::raw::exp::ExpContext)>,
    pub base: Option<ModuleId>,
    pub route: Vec<(ModuleId, usize, usize)>,
    pub arguments: Vec<(ModuleParamId, ModuleArgument)>,
}

impl NamespaceInstanceKey {
    fn route_hash(&self) -> u64 {
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        self.base.hash(&mut hash);
        self.route.hash(&mut hash);
        hash.finish()
    }
}

type NamespaceInstance = (ModuleId, Vec<ModuleId>);

#[derive(artifact::Relocate, serde::Serialize, serde::Deserialize, Debug)]
pub struct CrateEnv {
    pub(crate) kernel: RefCell<kernel::environment::Environment>,
    pub(crate) kernel_definitions: RefCell<HashMap<DefId, kernel::ids::DefinitionId>>,
    hir_symbols: HashMap<resolve::hir::BindingId, SymbolId>,
    // All imported spellings retain the same immutable declaration parameters.
    #[serde(deserialize_with = "shared_vectors::deserialize")]
    definition_parameters: HashMap<DefId, Arc<Vec<SymbolId>>>,
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
    pub(crate) namespace_conversion_cache:
        RefCell<kernel::sharing::Cache<(Exp, Exp), bool, { 1 << 18 }>>,
    #[serde(skip)]
    pub(crate) namespace_substitution_cache: RefCell<super::namespaces::SubstitutionCache>,
    #[serde(skip)]
    pub(crate) namespace_argument_cache: RefCell<super::namespaces::ArgumentCache>,
    #[serde(skip)]
    pub(crate) namespace_alias_cache: RefCell<super::namespaces::AliasCache>,
    symbols: Vec<String>,
    symbol_ids: HashMap<String, SymbolId>,
    // Import graphs can contain millions of namespaces. Growing their index
    // must not transiently duplicate every large module record.
    #[allow(clippy::vec_box)]
    #[serde(with = "module_checkpoint")]
    modules: Vec<Box<ModuleEnv>>,
    namespace_bindings: HashMap<ModuleId, NamespaceBinding>,
    #[serde(skip)]
    namespace_instances: HashMap<Arc<NamespaceInstanceKey>, NamespaceInstance>,
    #[serde(skip)]
    view_instances: HashMap<namespace_views::ViewKey, ModuleId>,
    #[serde(skip)]
    view_identities: HashMap<namespace_views::ViewIdentityKey, ModuleId>,
    #[serde(skip)]
    view_identities_indexed: bool,
    // Conversion only compares closed instances of the same import route.
    // Keep shared keys so unrelated and scoped graphs are never scanned.
    #[serde(skip)]
    closed_namespace_routes: HashMap<u64, Vec<Arc<NamespaceInstanceKey>>>,
    remappings: super::remapping_checkpoint::Tables,
    remapping_origins: HashMap<RemappingId, RemappingOrigin>,
    checking_scopes: HashMap<ModuleId, ModuleId>,
    // One validated capture is shared by every namespace in an import graph.
    #[serde(deserialize_with = "shared_vectors::deserialize")]
    checking_contexts: HashMap<ModuleId, Arc<crate::raw::exp::ExpContext>>,
    #[serde(deserialize_with = "shared_vectors::deserialize")]
    checking_program_contexts: HashMap<ModuleId, Arc<crate::raw::program::ProgramContext>>,
    #[serde(with = "declaration_checkpoint::definitions")]
    lazy_definitions: DefinitionMap<LazyDefinition>,
    #[serde(with = "declaration_checkpoint::inductives")]
    lazy_inductives: HashMap<InductiveId, LazyInductive>,
    #[serde(with = "declaration_checkpoint::specializations")]
    nominal_definitions: DefinitionMap<super::namespaces::Specialization<DefId>>,
    #[serde(with = "declaration_checkpoint::specializations")]
    nominal_inductives: HashMap<InductiveId, super::namespaces::Specialization<InductiveId>>,
    #[serde(with = "declaration_checkpoint::specializations")]
    prospective_inductives: HashMap<InductiveId, super::namespaces::Specialization<InductiveId>>,
    #[serde(with = "declaration_checkpoint::specializations")]
    nominal_datatypes:
        HashMap<ProgramInductiveId, super::namespaces::Specialization<ProgramInductiveId>>,
    #[serde(with = "declaration_checkpoint::datatypes")]
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
    pub fn storage_counts(&self) -> Vec<(&'static str, usize)> {
        let snapshots = self.remappings.snapshots.borrow();
        let maps = || self.remappings.iter().chain(snapshots.iter());
        let mut counts = vec![
            (
                "namespace metadata capacity bytes",
                self.modules.capacity() * std::mem::size_of::<Box<ModuleEnv>>()
                    + self.modules.len() * std::mem::size_of::<ModuleEnv>(),
            ),
            (
                "namespace binding capacity bytes",
                self.namespace_bindings.capacity()
                    * std::mem::size_of::<(ModuleId, NamespaceBinding)>(),
            ),
            (
                "namespace views",
                self.modules.iter().filter(|m| m.view.is_some()).count(),
            ),
            (
                "definition slots",
                self.modules.iter().map(|m| m.definitions.len()).sum(),
            ),
            (
                "allocated declaration cells",
                self.modules
                    .iter()
                    .map(|m| {
                        m.definitions.touched()
                            + m.inductives.touched()
                            + m.program_inductives.touched()
                    })
                    .sum(),
            ),
            (
                "binding edges",
                self.modules.iter().map(|m| m.bindings.len()).sum(),
            ),
            (
                "module remapping capacity",
                SharedMap::retained_capacity(maps().map(|m| &m.module_ids)),
            ),
            (
                "definition remapping capacity",
                SharedMap::retained_capacity(maps().map(|m| &m.definition_ids)),
            ),
            (
                "inductive remapping capacity",
                SharedMap::retained_capacity(maps().map(|m| &m.inductive_ids)),
            ),
            (
                "datatype remapping capacity",
                SharedMap::retained_capacity(maps().map(|m| &m.program_inductive_ids)),
            ),
        ];
        counts.extend(self.arena.storage_counts());
        counts.extend(self.namespace_argument_cache.borrow().storage_counts());
        counts
    }

    pub(crate) fn clear_judgements(&self) {
        self.kernel.borrow_mut().clear_caches();
        *self.inference_cache.borrow_mut() = Default::default();
        *self.contexts.borrow_mut() = Default::default();
        *self.whnf_cache.borrow_mut() = Default::default();
        *self.structural_expressions.borrow_mut() = Default::default();
        *self.namespace_shareability.borrow_mut() = Default::default();
        *self.namespace_conversion_cache.borrow_mut() = Default::default();
        *self.namespace_substitution_cache.borrow_mut() = Default::default();
        *self.namespace_alias_cache.borrow_mut() = Default::default();
    }

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
            namespace_alias_cache: Default::default(),
            symbols: vec![anonymous, root],
            symbol_ids,
            modules: vec![Box::new(ModuleEnv::new("root".into(), None, vec![]))],
            namespace_bindings: HashMap::new(),
            namespace_instances: HashMap::new(),
            view_instances: HashMap::new(),
            view_identities: HashMap::new(),
            view_identities_indexed: true,
            closed_namespace_routes: HashMap::new(),
            remappings: super::remapping_checkpoint::Tables::default(),
            remapping_origins: HashMap::new(),
            checking_scopes: HashMap::new(),
            checking_contexts: HashMap::new(),
            checking_program_contexts: HashMap::new(),
            lazy_definitions: DefinitionMap::default(),
            lazy_inductives: HashMap::new(),
            nominal_definitions: DefinitionMap::default(),
            nominal_inductives: HashMap::new(),
            prospective_inductives: HashMap::new(),
            nominal_datatypes: HashMap::new(),

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
        let context = Arc::new(context);
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

    pub(crate) fn record_source_module(&mut self, id: ModuleId, module: &resolve::hir::Module) {
        let parent = self.module(id).parent.unwrap_or(ModuleId(0));
        let inherited = self.module(parent).source.as_deref().or_else(|| {
            self.checking_scopes
                .get(&parent)
                .and_then(|owner| self.module(*owner).source.as_deref())
        });
        let source = match inherited {
            Some(parent) => SourceModule {
                package: parent.package.clone(),
                file: parent.file.clone(),
                root: parent.root,
                ordinal: i64::from(module.id.0) - i64::from(parent.root.0),
            },
            None => SourceModule {
                package: module.name.0.clone(),
                file: module
                    .header_source
                    .as_ref()
                    .or(module.source.as_ref())
                    .map(|s| s.id.clone()),
                root: module.id,
                ordinal: 0,
            },
        };
        self.module_mut(id).source = Some(Arc::new(source));
    }

    pub(crate) fn parameter_sort_key(&self, id: ModuleParamId) -> ParameterOrder<'_> {
        let source = self.module(id.module).source.as_deref();
        ParameterOrder {
            source: source.map(|s| {
                (
                    s.package.as_str(),
                    s.file.as_ref().map(|f| f.0.as_path()),
                    s.ordinal,
                )
            }),
            module: if source.is_some() { 0 } else { id.module.0 },
            position: id.position,
        }
    }

    pub fn add_module_parameter(&mut self, module: ModuleId, parameter: ModuleParameter) {
        self.module_mut(module).parameters.push(parameter);
        // A parent's telescope is also part of every descendant's arguments.
        self.namespace_argument_cache.get_mut().originals.clear();
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
        self.modules
            .push(Box::new(ModuleEnv::new(name, parent, parameters)));
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

    pub fn definition_parameters(&self, mut id: DefId) -> &[SymbolId] {
        if let Some(view) = &self.module(id.module).view {
            id.module = view.source;
        }
        self.definition_parameters
            .get(&id)
            .map(|parameters| parameters.as_slice())
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
        module_env
            .definitions
            .push(OnceCell::from(Box::new(definition)));
        let id = DefId { module, index };
        self.definition_parameters.insert(id, Arc::new(parameters));
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
            pts_context = context.as_ref().clone();
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
            .map(Box::as_ref)
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
            .or_else(|| {
                let view = self.module(id.module).view.as_ref()?;
                Some(LazyDefinition {
                    source: DefId {
                        module: view.source,
                        index: id.index,
                    },
                    environment: Rc::new(DefinitionEnvironment {
                        substitutions: view.arguments.as_arc().clone(),
                        reflected_substitutions: view.reflected.clone(),
                        remapping: Cell::new(self.binding(id.module).remapping),
                    }),
                })
            })
            .ok_or_else(|| crate::error::Error::ReservedDefinitionUsed { id })?;
        if !self.materializing_definitions.borrow_mut().insert(id) {
            return Err(crate::error::Error::CyclicDefinition { id });
        }
        let result: Result<&DefinedConstant, crate::error::Error> = (|| {
            let source = self.resolve_definition(lazy.source)?.clone();
            let count = self.definition_parameters(id).len();
            let shifted_substitutions = lazy
                .environment
                .substitutions
                .iter()
                .map(|(p, a)| (*p, a.shifted(self.arena(), count)))
                .collect::<Vec<_>>();
            let reflected = lazy
                .environment
                .reflected_substitutions
                .iter()
                .map(|(p, e)| {
                    (
                        *p,
                        crate::kernel_bridge::shift_bound_indices(self.arena(), *e, count, 0),
                    )
                })
                .collect::<Vec<_>>();
            let remap = self.remapping(lazy.environment.remapping.get());
            let logical_at = |e, depth| {
                use crate::raw::traversal::Term;
                let substitutions = shifted_substitutions
                    .iter()
                    .map(|(id, argument)| (*id, argument.shifted(self.arena(), depth)))
                    .collect::<Vec<_>>();
                let reflected = reflected
                    .iter()
                    .map(|&(id, e)| {
                        (
                            id,
                            crate::kernel_bridge::shift_bound_indices(self.arena(), e, depth, 0),
                        )
                    })
                    .collect::<Vec<_>>();
                let e = crate::raw::remapping::remap_all_global_ids(
                    self.arena(),
                    e,
                    &remap.definitions(self),
                    &remap.inductives(self),
                    &remap.datatypes(self),
                );
                let Term::Logical(e) =
                    Term::Logical(e).substitute(self.arena(), &substitutions, &reflected)
                else {
                    unreachable!()
                };
                e
            };
            let logical = |e| logical_at(e, 0);
            let value_ty = |t| {
                crate::raw::remapping::subst_value_type_module_params(
                    self.arena(),
                    crate::raw::remapping::remap_value_type_global_ids(
                        self.arena(),
                        t,
                        &remap.definitions(self),
                        &remap.datatypes(self),
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
                        &remap.definitions(self),
                        &remap.datatypes(self),
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
                            &remap.definitions(self),
                            &remap.datatypes(self),
                            &remap.inductives(self),
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
                                &remap.definitions(self),
                                &remap.datatypes(self),
                                &remap.inductives(self),
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
            slot.set(Box::new(definition))
                .map_err(|_| crate::error::Error::DuplicateMaterialization { id })?;
            Ok(slot
                .get()
                .expect("definition was just initialized")
                .as_ref())
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

    #[cfg(test)]
    pub(crate) fn reserve_lazy_definition(
        &mut self,
        module: ModuleId,
        source: DefId,
        substitutions: impl Into<Arc<[(ModuleParamId, ModuleArgument)]>>,
        reflected_substitutions: impl Into<Arc<[(ModuleParamId, Exp)]>>,
    ) -> DefId {
        self.reserve_lazy_definition_shared(
            module,
            source,
            Rc::new(DefinitionEnvironment {
                substitutions: substitutions.into(),
                reflected_substitutions: reflected_substitutions.into(),
                remapping: Cell::new(RemappingId(0)),
            }),
        )
    }

    #[cfg(test)]
    pub(crate) fn reserve_lazy_definition_shared(
        &mut self,
        module: ModuleId,
        source: DefId,
        environment: Rc<DefinitionEnvironment>,
    ) -> DefId {
        let parameters = self.definition_parameters.get(&source).cloned();
        let index = self.module(module).definitions.len() as u32;
        self.module_mut(module).definitions.push(OnceCell::new());
        let id = DefId { module, index };
        if let Some(parameters) = parameters.filter(|parameters| !parameters.is_empty()) {
            self.definition_parameters.insert(id, parameters);
        }
        self.lazy_definitions.insert(
            id,
            LazyDefinition {
                source,
                environment,
            },
        );
        id
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
            slot.set(Box::new(inductive)).is_ok(),
            "inductive ID was already defined"
        );
    }

    pub fn inductive(&self, id: InductiveId) -> &InductiveTypeSpecs {
        let slot = &self.module(id.module).inductives[id.index as usize];
        if slot.get().is_none() {
            let lazy = self
                .lazy_inductives
                .get(&id)
                .cloned()
                .or_else(|| {
                    let view = self.module(id.module).view.as_ref()?;
                    Some(LazyInductive {
                        source: InductiveId {
                            module: view.source,
                            index: id.index,
                        },
                        substitutions: view.reflected.clone(),
                        remapping: self.binding(id.module).remapping,
                    })
                })
                .unwrap_or_else(|| panic!("reserved inductive ID was used before definition"));
            let spec = self
                .inductive(lazy.source)
                .clone()
                .remap_global_ids(
                    self.arena(),
                    &self.remapping(lazy.remapping).definitions(self),
                    &self.remapping(lazy.remapping).inductives(self),
                )
                .instantiate(self.arena(), &lazy.substitutions);
            let _ = slot.set(Box::new(spec));
            self.materialized_inductives
                .set(self.materialized_inductives.get() + 1);
        }
        slot.get().expect("lazy inductive initialized")
    }

    pub(crate) fn definition_specialization_arguments(
        &self,
        id: DefId,
    ) -> std::borrow::Cow<'_, [(ModuleParamId, ModuleArgument)]> {
        if let Some(view) = &self.module(id.module).view {
            return std::borrow::Cow::Borrowed(&view.arguments);
        }
        self.nominal_definitions.get(&id).map_or_else(
            || self.namespace_arguments(id.module).into(),
            |origin| std::borrow::Cow::Borrowed(origin.arguments.as_ref()),
        )
    }

    pub(crate) fn definition_specialization(
        &self,
        id: DefId,
    ) -> Option<super::namespaces::Specialization<DefId>> {
        self.nominal_definitions.get(&id).cloned().or_else(|| {
            let view = self.module(id.module).view.as_ref()?;
            Some(super::namespaces::Specialization {
                source: DefId {
                    module: view.source,
                    index: id.index,
                },
                arguments: view.arguments.clone(),
            })
        })
    }

    pub(crate) fn generic_definition_specialization(
        &self,
        id: DefId,
    ) -> Option<super::namespaces::Specialization<DefId>> {
        let origin = self.definition_specialization(id)?;
        (!self.namespace_has_local_context(origin.source.module)
            && !self
                .checking_program_contexts
                .contains_key(&origin.source.module)
            && matches!(
                self.materialized_definition(origin.source)?,
                DefinedConstant::Pts { .. } | DefinedConstant::Contextual { .. }
            )
            && origin
                .arguments
                .iter()
                .all(|(_, a)| matches!(a, ModuleArgument::Pts(_))))
        .then_some(origin)
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
    ) -> Option<super::namespaces::Specialization<InductiveId>> {
        self.nominal_inductives
            .get(&id)
            .or_else(|| self.prospective_inductives.get(&id))
            .cloned()
            .or_else(|| {
                let view = self.module(id.module).view.as_ref()?;
                Some(super::namespaces::Specialization {
                    source: InductiveId {
                        module: view.source,
                        index: id.index,
                    },
                    arguments: view.arguments.clone(),
                })
            })
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
            slot.set(Box::new(inductive)).is_ok(),
            "Program inductive ID was already defined"
        );
    }

    pub(crate) fn has_program_inductive(&self, id: ProgramInductiveId) -> bool {
        let module = self.module(id.module);
        (id.index as usize) < module.program_inductives.len()
            && (module
                .program_inductives
                .get(id.index as usize)
                .is_some_and(|slot| slot.get().is_some())
                || self.lazy_program_inductives.contains_key(&id)
                || module.view.is_some())
    }
    pub fn program_inductive(&self, id: ProgramInductiveId) -> &ProgramInductiveTypeSpecs {
        let slot = &self.module(id.module).program_inductives[id.index as usize];
        if slot.get().is_none() {
            let lazy = self
                .lazy_program_inductives
                .get(&id)
                .cloned()
                .or_else(|| {
                    let view = self.module(id.module).view.as_ref()?;
                    Some(LazyProgramInductive {
                        source: ProgramInductiveId {
                            module: view.source,
                            index: id.index,
                        },
                        substitutions: view.arguments.as_arc().clone(),
                        remapping: self.binding(id.module).remapping,
                    })
                })
                .expect("reserved Program inductive ID was used before definition");
            let spec = self
                .program_inductive(lazy.source)
                .clone()
                .remap_global_ids(
                    self.arena(),
                    &self.remapping(lazy.remapping).definitions(self),
                    &self.remapping(lazy.remapping).inductives(self),
                    &self.remapping(lazy.remapping).datatypes(self),
                )
                .instantiate(self.arena(), &lazy.substitutions);
            let _ = slot.set(Box::new(spec));
            self.materialized_datatypes
                .set(self.materialized_datatypes.get() + 1);
        }
        slot.get().expect("lazy Program inductive initialized")
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
        let arguments = self.namespace_argument_cache.borrow_mut().share(&arguments);
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
        let source = if let Some(view) = &self.module(definition.module).view {
            DefId {
                module: view.source,
                index: definition.index,
            }
        } else {
            *self.binding(binding).definition_origins.get(&definition)?
        };
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
            Arc::make_mut(&mut module.hir_items).insert(binding, *index);
        }
        Arc::make_mut(&mut module.hir_names).insert(name, binding);
    }

    #[cfg(test)]
    pub(crate) fn publish_instantiated_items(
        &mut self,
        source: ModuleId,
        target: ModuleId,
        items: Vec<ModuleItem>,
    ) {
        let original = self.module(source);
        assert_eq!(original.items.len(), items.len());
        assert!(
            original
                .items
                .iter()
                .zip(&items)
                .all(|(a, b)| a.name() == b.name())
        );
        let names = original.names.clone();
        let hir_names = original.hir_names.clone();
        let current_hir_items = || {
            hir_names
                .iter()
                .filter_map(|(name, binding)| names.get(name).map(|index| (*binding, *index)))
        };
        let hir_items = if current_hir_items().count() == original.hir_items.len()
            && current_hir_items()
                .all(|(binding, index)| original.hir_items.get(&binding) == Some(&index))
        {
            original.hir_items.clone()
        } else {
            Arc::new(current_hir_items().collect())
        };
        let target = self.module_mut(target);
        assert!(target.items.is_empty());
        // Specialization changes declaration identities, but preserves their
        // order and names. Reuse those immutable indexes across namespaces.
        target.items = Arc::new(items);
        target.names = names;
        target.hir_names = hir_names;
        target.hir_items = hir_items;
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
        Arc::make_mut(&mut module.items).push(item);
        if let Some(binding) = module.hir_names.get(&name) {
            Arc::make_mut(&mut module.hir_items).insert(*binding, index);
        }
        Arc::make_mut(&mut module.names).insert(name, index);
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
            .and_then(|index| Arc::make_mut(&mut self.module_mut(module).items).get_mut(index))
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
        let find = |module: &ModuleEnv| {
            let source = module
                .view
                .as_ref()
                .filter(|view| view.identity == inductive.module)
                .map_or(inductive, |view| InductiveId {
                    module: view.source,
                    ..inductive
                });
            module.items.iter().position(|item| {
                matches!(item,
                ModuleItem::Inductive { inductive: candidate, .. }
                | ModuleItem::Record { inductive: candidate, .. }
                | ModuleItem::ProgramInductive { reflected: candidate, .. }
                if *candidate == source)
            })
        };
        let owner = self.module(inductive.module);
        if let Some(index) = find(owner) {
            return Some(owner.item_at(index));
        }
        // Older nominal imports can publish an identity in a re-exporting
        // namespace. Inspect source indices without materializing its members.
        self.modules
            .iter()
            .find_map(|module| find(module).map(|index| module.item_at(index)))
    }

    pub fn record_for_inductive(&self, inductive: InductiveId) -> Option<&ModuleItem> {
        self.item_for_inductive(inductive)
            .filter(|item| matches!(item, ModuleItem::Record { .. }))
    }

    pub fn program_record_for_inductive(
        &self,
        inductive: ProgramInductiveId,
    ) -> Option<&ModuleItem> {
        let find = |module: &ModuleEnv| {
            module.items.iter().position(|item| matches!(item,
            ModuleItem::ProgramInductive { record_fields: Some(_), inductive: candidate, .. } if *candidate == inductive))
        };
        let owner = self.module(inductive.module);
        if let Some(index) = find(owner) {
            return Some(owner.item_at(index));
        }
        self.modules
            .iter()
            .find_map(|module| find(module).map(|index| module.item_at(index)))
    }

    pub fn materialization_stats(&self) -> MaterializationStats {
        MaterializationStats {
            definitions: self.materialized_definitions.get(),
            inductives: self.materialized_inductives.get(),
            datatypes: self.materialized_datatypes.get(),
        }
    }

    pub(crate) fn namespace_entry_count(&self) -> usize {
        self.modules.len()
            + self.lazy_definitions.len()
            + self.lazy_inductives.len()
            + self.lazy_program_inductives.len()
            + self.nominal_definitions.len()
            + self.nominal_inductives.len()
            + self.nominal_datatypes.len()
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
        context: Arc<crate::raw::program::ProgramContext>,
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
            .map(|context| context.as_ref().clone())
            .unwrap_or_default()
    }

    pub(crate) fn namespace_has_local_context(&self, module: ModuleId) -> bool {
        self.checking_contexts
            .get(&module)
            .is_some_and(|context| !context.is_empty())
    }

    pub(crate) fn definition_context(&self, module: ModuleId) -> crate::raw::exp::ExpContext {
        if let Some(context) = self.checking_contexts.get(&module) {
            return context.as_ref().clone();
        }
        // Named module parameters are captured by identity when lowering.
        // Only local binders belong to the de Bruijn context.
        Vec::new()
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
                    .entries()
                    .into_iter()
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
                    .entries()
                    .into_iter()
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
                    .entries()
                    .into_iter()
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
    pub(crate) fn namespace_instance(
        &self,
        key: &NamespaceInstanceKey,
    ) -> Option<NamespaceInstance> {
        self.namespace_instances.get(key).cloned()
    }

    pub(crate) fn equivalent_namespace_instance(
        &self,
        key: &NamespaceInstanceKey,
    ) -> Option<NamespaceInstance> {
        if key.scope.is_some() {
            return None;
        }
        self.closed_namespace_routes
            .get(&key.route_hash())?
            .iter()
            .find_map(|candidate| {
                (candidate.base == key.base
                    && candidate.route == key.route
                    && self.namespace_arguments_equal(&candidate.arguments, &key.arguments))
                .then(|| self.namespace_instances.get(candidate).unwrap().clone())
            })
    }

    pub(crate) fn remember_namespace_instance(
        &mut self,
        key: NamespaceInstanceKey,
        value: NamespaceInstance,
    ) {
        let key = Arc::new(key);
        if key.scope.is_none() && !self.namespace_instances.contains_key(&key) {
            self.closed_namespace_routes
                .entry(key.route_hash())
                .or_default()
                .push(key.clone());
        }
        self.namespace_instances.insert(key, value);
    }

    pub(crate) fn store_namespace_remapping(
        &mut self,
        remapping: DeclarationRemapping,
        namespace: ModuleId,
    ) -> RemappingId {
        let id = self.store_remapping(remapping);
        self.remapping_origins
            .insert(id, RemappingOrigin::Namespace(namespace));
        id
    }

    pub(crate) fn store_remapping(&mut self, remapping: DeclarationRemapping) -> RemappingId {
        timing::costs::count("namespace.remapping-owned-capacity", || {
            (remapping.module_ids.capacity()
                + remapping.definition_ids.capacity()
                + remapping.inductive_ids.capacity()
                + remapping.program_inductive_ids.capacity()) as u64
        });
        let id = RemappingId(self.remappings.len());
        self.remappings.push(remapping);
        if self.remappings.len().is_multiple_of(16384)
            && std::env::var_os("REF_TYPE_PROFILE_STORAGE").is_some()
        {
            eprintln!(
                "storage remappings={} modules={} arena_nodes={} nominal_definitions={}/{} lazy_definitions={}/{} views={}/{} namespaces={}/{} instances={} closed_routes={}",
                self.remappings.len(),
                self.modules.len(),
                self.arena.core.len(),
                self.nominal_definitions.len(),
                self.nominal_definitions.capacity(),
                self.lazy_definitions.len(),
                self.lazy_definitions.capacity(),
                self.view_instances.len(),
                self.view_instances.capacity(),
                self.namespace_bindings.len(),
                self.namespace_bindings.capacity(),
                self.namespace_instances.len(),
                self.closed_namespace_routes.len(),
            );
        }
        if self.remappings.len().is_multiple_of(1024)
            && std::env::var_os("REF_TYPE_PROFILE_REMAPPINGS").is_some()
        {
            let mut capacities = [0usize; 4];
            for map in self.remappings.iter() {
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
                self.remapping_origins
                    .insert(id, RemappingOrigin::Composition { next, previous });
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

    /// Keep inherited tables shared when finalizing a namespace. Flattening
    /// each child duplicates the complete parent substitution graph.
    pub(crate) fn compact_remapping(&mut self, id: RemappingId) {
        let remapping = &mut self.remappings[id.0];
        remapping.definition_ids.compact();
        remapping.inductive_ids.compact();
        remapping.program_inductive_ids.compact();
    }

    pub(crate) fn remapping(&self, id: RemappingId) -> &DeclarationRemapping {
        &self.remappings[id.0]
    }

    pub(crate) fn restore_shared_arena(&mut self) {
        self.kernel.get_mut().arena = self.arena.core.clone();
        self.view_identities_indexed = false;
    }

    pub(crate) fn refresh_hir_names(
        &mut self,
        modules: &HashMap<resolve::hir::ModuleId, ModuleId>,
        bindings: &HashMap<resolve::hir::BindingId, resolve::Binding>,
    ) {
        for &module in modules.values() {
            Arc::make_mut(&mut self.modules[module.index()].hir_names).clear();
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
    use super::Slots;
    use serde::{Deserialize, Deserializer, Serialize, Serializer, de::Error};
    pub fn serialize<T: Serialize, S: Serializer>(
        cells: &Slots<T>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        let values: Vec<_> = cells
            .entries()
            .into_iter()
            .filter_map(|(index, cell)| cell.get().map(|value| (index, value)))
            .collect();
        (cells.len(), values).serialize(serializer)
    }
    pub fn deserialize<'de, T: Deserialize<'de>, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Slots<T>, D::Error> {
        let (length, values): (usize, Vec<(usize, T)>) = Deserialize::deserialize(deserializer)?;
        let cells = Slots::reserved(length);
        for (index, value) in values {
            if index >= length || cells[index].set(value).is_err() {
                return Err(D::Error::custom("invalid declaration slot"));
            }
        }
        Ok(cells)
    }
}

#[cfg(test)]
mod specialization_tests {
    use super::*;

    #[test]
    fn lazy_definition_parameters_share_source_symbols_and_restore_sharing() {
        use crate::raw::program::{ComputationTermNode, ComputationTypeNode};

        let mut env = CrateEnv::new();
        let root = env.root_module();
        let arena = env.arena();
        let domain = arena.value_type_bound(0);
        let ty = arena.alloc(ComputationTypeNode::Function {
            domain,
            codomain: arena.alloc(ComputationTypeNode::Return { value_ty: domain }),
        });
        let body = arena.alloc(ComputationTermNode::Lambda {
            var: SymbolId::ANONYMOUS,
            value_ty: domain,
            body: arena.alloc(ComputationTermNode::Return {
                value: arena.value_bound(0),
            }),
        });
        let mut symbols = vec![SymbolId::ANONYMOUS];
        let source = env
            .add_parameterized_definition(
                root,
                DefinedConstant::ProgramComputation { ty, body },
                symbols.clone(),
            )
            .unwrap();
        let namespaces = env.add_modules_in_scope(root, vec![], 2).unwrap();
        let ids = namespaces
            .iter()
            .map(|&namespace| env.reserve_lazy_definition(namespace, source, vec![], vec![]))
            .collect::<Vec<_>>();
        for id in &ids {
            assert!(Arc::ptr_eq(
                &env.definition_parameters[&source],
                &env.definition_parameters[id]
            ));
        }
        assert_eq!(
            postcard::to_allocvec(&env.definition_parameters[&source]).unwrap(),
            postcard::to_allocvec(&symbols).unwrap()
        );
        symbols.clear();
        assert_eq!(env.definition_parameters(source), &[SymbolId::ANONYMOUS]);

        let restored: CrateEnv =
            postcard::from_bytes(&postcard::to_allocvec(&env).unwrap()).unwrap();
        for id in ids {
            assert!(Arc::ptr_eq(
                &restored.definition_parameters[&source],
                &restored.definition_parameters[&id]
            ));
        }
    }

    #[test]
    fn import_captures_share_storage_without_exposing_caller_mutation() {
        use crate::raw::{exp::ExpContextEntry, program::ProgramContextEntry, sort::Sort};

        let mut env = CrateEnv::new();
        let root = env.root_module();
        let entry = ExpContextEntry {
            var: SymbolId::ANONYMOUS,
            ty: env.arena().sort(Sort::Set(0)),
        };
        let mut logical = vec![entry.clone()];
        let modules = env.add_modules_in_scope(root, logical.clone(), 2).unwrap();
        assert!(Arc::ptr_eq(
            &env.checking_contexts[&modules[0]],
            &env.checking_contexts[&modules[1]]
        ));
        logical.clear();
        let mut returned = env.definition_context(modules[0]);
        returned.clear();
        assert_eq!(env.definition_context(modules[1]), vec![entry.clone()]);

        let program_entry = ProgramContextEntry::ValueType {
            var: SymbolId::ANONYMOUS,
        };
        let mut program = Arc::new(vec![program_entry.clone()]);
        for &module in &modules {
            env.set_program_context(module, program.clone());
        }
        assert!(Arc::ptr_eq(
            &env.checking_program_contexts[&modules[0]],
            &env.checking_program_contexts[&modules[1]]
        ));
        Arc::make_mut(&mut program).clear();
        let mut returned = env.program_definition_context(modules[0]);
        returned.clear();
        assert_eq!(
            env.program_definition_context(modules[1]),
            vec![program_entry.clone()]
        );
        assert_eq!(
            postcard::to_allocvec(&env.checking_contexts[&modules[0]]).unwrap(),
            postcard::to_allocvec(&vec![entry]).unwrap()
        );
        assert_eq!(
            postcard::to_allocvec(&env.checking_program_contexts[&modules[0]]).unwrap(),
            postcard::to_allocvec(&vec![program_entry]).unwrap()
        );

        let restored: CrateEnv =
            postcard::from_bytes(&postcard::to_allocvec(&env).unwrap()).unwrap();
        assert!(Arc::ptr_eq(
            &restored.checking_contexts[&modules[0]],
            &restored.checking_contexts[&modules[1]]
        ));
        assert!(Arc::ptr_eq(
            &restored.checking_program_contexts[&modules[0]],
            &restored.checking_program_contexts[&modules[1]]
        ));
    }

    #[test]
    fn closed_namespace_route_index_preserves_conversion_and_scope() {
        use crate::raw::{exp::ExpNode, sort::Sort};

        let mut env = CrateEnv::new();
        let root = env.root_module();
        let parameter = ModuleParamId {
            module: root,
            position: 0,
        };
        let set = env.arena().sort(Sort::Set(0));
        let identity = env.arena().alloc(ExpNode::Lam {
            var: SymbolId::ANONYMOUS,
            ty: env.arena().sort(Sort::SetKind(1)),
            body: env.arena().exp_bound(0),
        });
        let equivalent = env.arena().alloc(ExpNode::App {
            func: identity,
            arg: set,
        });
        let key = NamespaceInstanceKey {
            scope: None,
            base: None,
            route: vec![(root, 1, 0)],
            arguments: vec![(parameter, set.into())],
        };
        env.remember_namespace_instance(key.clone(), (root, vec![root]));
        let mut converted = key.clone();
        converted.arguments[0].1 = equivalent.into();
        assert!(env.namespace_instance(&converted).is_none());
        assert_eq!(
            env.equivalent_namespace_instance(&converted),
            Some((root, vec![root]))
        );

        // Hash buckets are only an index: a collision never equates routes.
        let mut other_route = converted.clone();
        other_route.route[0].1 += 1;
        env.closed_namespace_routes
            .insert(other_route.route_hash(), vec![Arc::new(key.clone())]);
        assert!(env.equivalent_namespace_instance(&other_route).is_none());
        converted.scope = Some((root, vec![]));
        assert!(env.equivalent_namespace_instance(&converted).is_none());
    }

    #[test]
    fn compact_module_items_preserve_legacy_checkpoint_bytes() {
        #[derive(serde::Serialize)]
        enum LegacyItem {
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
        let definition = DefId {
            module: ModuleId(1),
            index: 2,
        };
        let inductive = InductiveId {
            module: ModuleId(3),
            index: 4,
        };
        let associated = || vec![("method".into(), definition)];
        let items = [
            LegacyItem::Definition {
                name: "value".into(),
                definition,
            },
            LegacyItem::Inductive {
                name: "Choice".into(),
                constructor_names: vec!["left".into(), "right".into()],
                associated_definitions: associated(),
                inductive,
            },
            LegacyItem::Record {
                name: "Pair".into(),
                associated_definitions: associated(),
                inductive,
            },
            LegacyItem::ProgramInductive {
                record_fields: Some(vec!["field".into()]),
                name: "Value".into(),
                constructor_names: vec!["make".into()],
                associated_definitions: associated(),
                inductive: ProgramInductiveId {
                    module: ModuleId(5),
                    index: 6,
                },
                reflected: inductive,
            },
        ];
        for item in items {
            let bytes = postcard::to_allocvec(&item).unwrap();
            let restored: ModuleItem = postcard::from_bytes(&bytes).unwrap();
            assert_eq!(postcard::to_allocvec(&restored).unwrap(), bytes);
            let copy = restored.clone();
            let name = |item: &ModuleItem| match item {
                ModuleItem::Definition { name, .. }
                | ModuleItem::Inductive { name, .. }
                | ModuleItem::Record { name, .. }
                | ModuleItem::ProgramInductive { name, .. } => Arc::as_ptr(name),
            };
            assert_eq!(name(&restored), name(&copy));
            if let ModuleItem::Inductive {
                constructor_names,
                associated_definitions,
                ..
            } = &restored
            {
                let mut copy = restored.clone();
                let ModuleItem::Inductive {
                    constructor_names: copied_names,
                    associated_definitions: copied_definitions,
                    ..
                } = &mut copy
                else {
                    unreachable!()
                };
                assert!(Arc::ptr_eq(constructor_names, copied_names));
                copied_definitions.clear();
                assert_eq!(associated_definitions.len(), 1);
            }
        }
        assert!(std::mem::size_of::<ModuleItem>() < std::mem::size_of::<LegacyItem>());
    }
    #[test]
    fn namespace_argument_arrays_share_storage_and_preserve_checkpoint_bytes() {
        let mut env = CrateEnv::new();
        let root = env.root_module();
        let namespaces = [env.add_module(), env.add_module()];
        let parameter = ModuleParamId {
            module: root,
            position: 0,
        };
        let arguments = vec![(
            parameter,
            ModuleArgument::Pts(env.arena().sort(crate::raw::sort::Sort::Set(0))),
        )];
        for namespace in namespaces {
            env.add_namespace_binding(
                root,
                root,
                namespace,
                arguments.clone(),
                HashMap::new(),
                RemappingId(0),
            );
        }
        let binding = env.binding(namespaces[0]);
        assert!(Arc::ptr_eq(
            &binding.arguments,
            &env.binding(namespaces[1]).arguments
        ));
        #[derive(serde::Serialize)]
        struct LegacyBinding {
            source: ModuleId,
            materialized: ModuleId,
            arguments: Vec<(ModuleParamId, ModuleArgument)>,
            definition_origins: HashMap<DefId, DefId>,
            remapping: RemappingId,
        }
        let legacy = LegacyBinding {
            source: binding.source,
            materialized: binding.materialized,
            arguments,
            definition_origins: binding.definition_origins.clone(),
            remapping: binding.remapping,
        };
        let bytes = postcard::to_allocvec(&legacy).unwrap();
        assert_eq!(postcard::to_allocvec(binding).unwrap(), bytes);
        let restored: NamespaceBinding = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(restored.arguments.as_ref(), binding.arguments.as_ref());
        assert_eq!(restored.source, binding.source);
        assert_eq!(restored.materialized, binding.materialized);
    }
    #[test]
    fn instantiated_name_indexes_keep_new_identities_and_isolate_later_declarations() {
        let mut env = CrateEnv::new();
        let source = env.add_module();
        let target = env.add_module();
        let binding = resolve::hir::BindingId(17);
        env.register_hir_name(source, binding, "value".into());
        env.publish_item(
            source,
            ModuleItem::Definition {
                name: "value".to_string().into(),
                definition: DefId {
                    module: source,
                    index: 0,
                },
            },
        )
        .unwrap();
        let specialized = ModuleItem::Definition {
            name: "value".to_string().into(),
            definition: DefId {
                module: target,
                index: 0,
            },
        };
        env.publish_instantiated_items(source, target, vec![specialized.clone()]);
        assert_eq!(env.module(target).item("value"), Some(&specialized));
        assert_eq!(env.module(target).hir_item(binding), Some(&specialized));
        assert!(Arc::ptr_eq(
            &env.module(source).names,
            &env.module(target).names
        ));
        assert!(Arc::ptr_eq(
            &env.module(source).hir_items,
            &env.module(target).hir_items
        ));
        env.publish_item(
            target,
            ModuleItem::Definition {
                name: "later".to_string().into(),
                definition: DefId {
                    module: target,
                    index: 1,
                },
            },
        )
        .unwrap();
        assert!(env.module(source).item("later").is_none());
        assert!(env.module(target).item("later").is_some());
        env.register_hir_name(target, resolve::hir::BindingId(18), "later".into());
        assert!(!env.module(source).hir_names.contains_key("later"));
        assert!(
            env.module(source)
                .hir_item(resolve::hir::BindingId(18))
                .is_none()
        );
        assert!(env.publish_item(target, specialized).is_err());
    }
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
                    arguments: vec![].into(),
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
