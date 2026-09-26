//! Crate/module declarations and materialized-binding provenance.

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
    },
    ProgramComputation {
        ty: ComputationType,
        body: ComputationTerm,
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
pub struct NamespaceBinding {
    pub source: ModuleId,
    pub materialized: ModuleId,
    pub arguments: Vec<(ModuleParamId, ModuleArgument)>,
    /// Maps definitions in `materialized` back to definitions in `source`.
    pub definition_origins: HashMap<DefId, DefId>,
    pub(crate) remapping: DeclarationRemapping,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct DeclarationRemapping {
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
    remapping: DeclarationRemapping,
}

#[derive(Debug, Clone)]
struct LazyInductive {
    source: InductiveId,
    substitutions: Vec<(ModuleParamId, Exp)>,
    remapping: DeclarationRemapping,
}

#[derive(Debug, Clone)]
struct LazyProgramInductive {
    source: ProgramInductiveId,
    substitutions: Vec<(ModuleParamId, ModuleArgument)>,
    remapping: DeclarationRemapping,
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

#[derive(Debug)]
pub struct CrateEnv {
    hir_symbols: HashMap<resolve::hir::BindingId, SymbolId>,
    definition_parameters: HashMap<DefId, Vec<SymbolId>>,
    arena: Arena,
    pub(crate) inference_cache: std::cell::RefCell<InferenceCache>,
    pub(crate) contexts: RefCell<ContextInterner<Exp>>,
    // Raw nodes and registered declarations are immutable. Weak-head reduction
    // depends only on those, not on the elaborator's context or meta assignments.
    pub(crate) whnf_cache: RefCell<FxHashMap<Exp, Exp>>,
    symbols: Vec<String>,
    symbol_ids: HashMap<String, SymbolId>,
    modules: Vec<ModuleEnv>,
    namespace_bindings: HashMap<ModuleId, NamespaceBinding>,
    checking_scopes: HashMap<ModuleId, ModuleId>,
    checking_contexts: HashMap<ModuleId, crate::raw::exp::ExpContext>,
    lazy_definitions: HashMap<DefId, LazyDefinition>,
    lazy_inductives: HashMap<InductiveId, LazyInductive>,
    nominal_definitions: HashMap<DefId, super::namespaces::Specialization<DefId>>,
    nominal_inductives: HashMap<InductiveId, super::namespaces::Specialization<InductiveId>>,
    nominal_datatypes:
        HashMap<ProgramInductiveId, super::namespaces::Specialization<ProgramInductiveId>>,
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
    /// Retained cache entries and distinct shared context extensions.
    pub fn cache_counts(&self) -> [(&'static str, usize); 3] {
        let inference = self.inference_cache.borrow();
        [
            ("inference", inference.len()),
            ("context bindings", self.contexts.borrow().len()),
            ("weak heads", self.whnf_cache.borrow().len()),
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
        Self {
            hir_symbols: HashMap::new(),
            definition_parameters: HashMap::new(),
            arena: Arena::new(),
            inference_cache: Default::default(),
            contexts: Default::default(),
            whnf_cache: Default::default(),
            symbols: vec![anonymous, root],
            symbol_ids,
            modules: vec![ModuleEnv::new("root".into(), None, vec![])],
            namespace_bindings: HashMap::new(),
            checking_scopes: HashMap::new(),
            checking_contexts: HashMap::new(),
            lazy_definitions: HashMap::new(),
            lazy_inductives: HashMap::new(),
            nominal_definitions: HashMap::new(),
            nominal_inductives: HashMap::new(),
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
    pub fn add_module_in_scope(
        &mut self,
        owner: ModuleId,
        mut context: crate::raw::exp::ExpContext,
    ) -> Result<ModuleId, String> {
        crate::raw::derivation::CheckSession::new(self, &mut context)
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
        let mut program_context = type_parameters
            .iter()
            .map(|var| crate::raw::program::ProgramContextEntry::ValueType { var: *var })
            .collect();
        match *definition {
            DefinedConstant::Pts { ty, body } => {
                CheckSession::new(self, &mut pts_context)
                    .check_pts(body, ty)
                    .map_err(|error| format!("definition check failed: {error:?}"))?;
            }
            DefinedConstant::ProgramValue { ty, body } => {
                ProgramCheckSession::new(self, &mut program_context)
                    .check_value_term(body, ty)
                    .map_err(|error| format!("Program value definition check failed: {error:?}"))?;
            }
            DefinedConstant::ProgramComputation { ty, body } => {
                ProgramCheckSession::new(self, &mut program_context)
                    .check_computation_term(body, ty)
                    .map_err(|error| {
                        format!("Program computation definition check failed: {error:?}")
                    })?;
            }
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
                        super::calculus::shift_bound_indices(self.arena(), *e, count, 0),
                    )
                })
                .collect::<Vec<_>>();
            let remap = &lazy.remapping;
            let logical = |e| {
                super::calculus::exp_subst_map(
                    self.arena(),
                    super::calculus::remap_all_global_ids(
                        self.arena(),
                        e,
                        &remap.definition_ids,
                        &remap.inductive_ids,
                        &remap.program_inductive_ids,
                    ),
                    &reflected,
                )
            };
            let value_ty = |t| {
                super::program_calculus::subst_value_type_module_params(
                    self.arena(),
                    super::program_calculus::remap_value_type_global_ids(
                        self.arena(),
                        t,
                        &remap.definition_ids,
                        &remap.program_inductive_ids,
                    ),
                    &shifted_substitutions,
                )
            };
            let comp_ty = |t| {
                super::program_calculus::subst_computation_type_module_params(
                    self.arena(),
                    super::program_calculus::remap_computation_type_global_ids(
                        self.arena(),
                        t,
                        &remap.definition_ids,
                        &remap.program_inductive_ids,
                    ),
                    &shifted_substitutions,
                )
            };
            let definition = match source {
                DefinedConstant::Pts { ty, body } => DefinedConstant::Pts {
                    ty: logical(ty),
                    body: logical(body),
                },
                DefinedConstant::ProgramValue { ty, body } => DefinedConstant::ProgramValue {
                    ty: value_ty(ty),
                    body: super::program_calculus::subst_value_module_params(
                        self.arena(),
                        super::program_calculus::remap_value_global_ids(
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
                        body: super::program_calculus::subst_computation_module_params(
                            self.arena(),
                            super::program_calculus::remap_computation_global_ids(
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
        remapping: &DeclarationRemapping,
    ) -> (DefId, bool) {
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
            &substitutions,
            &reflected_substitutions,
            remapping,
        );
        if self
            .namespace_arguments_equal(&arguments, &self.namespace_arguments(origin.source.module))
        {
            return (origin.source, false);
        }
        if self.namespace_arguments_shareable(&arguments)
            && let Some((&id, _)) = self.nominal_definitions.iter().find(|(_, candidate)| {
                candidate.source == origin.source
                    && self.namespace_arguments_shareable(&arguments)
                    && self.namespace_arguments_equal(&arguments, &candidate.arguments)
            })
        {
            return (id, false);
        }
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
                remapping: DeclarationRemapping::default(),
            },
        );
        self.nominal_definitions.insert(
            id,
            super::namespaces::Specialization {
                source: origin.source,
                arguments,
            },
        );
        (id, true)
    }

    pub(crate) fn set_lazy_definition_remapping(
        &mut self,
        id: DefId,
        remapping: DeclarationRemapping,
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
                .remap_global_ids(
                    self.arena(),
                    &lazy.remapping.definition_ids,
                    &lazy.remapping.inductive_ids,
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
        substitutions: Vec<(ModuleParamId, ModuleArgument)>,
        reflected_substitutions: Vec<(ModuleParamId, Exp)>,
        remapping: &DeclarationRemapping,
    ) -> (InductiveId, bool) {
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
            &substitutions,
            &reflected_substitutions,
            remapping,
        );
        if self
            .namespace_arguments_equal(&arguments, &self.namespace_arguments(origin.source.module))
        {
            return (origin.source, false);
        }
        if let Some((&id, _)) = self.nominal_inductives.iter().find(|(_, candidate)| {
            candidate.source == origin.source
                && self.namespace_arguments_shareable(&arguments)
                && self.namespace_arguments_equal(&arguments, &candidate.arguments)
        }) {
            return (id, false);
        }
        let id = self.reserve_inductive(module);
        self.nominal_inductives.insert(
            id,
            super::namespaces::Specialization {
                source: origin.source,
                arguments,
            },
        );
        self.lazy_inductives.insert(
            id,
            LazyInductive {
                source,
                substitutions: reflected_substitutions,
                remapping: DeclarationRemapping::default(),
            },
        );
        (id, true)
    }

    pub(crate) fn set_lazy_inductive_remapping(
        &mut self,
        id: InductiveId,
        remapping: DeclarationRemapping,
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
                .remap_global_ids(
                    self.arena(),
                    &lazy.remapping.definition_ids,
                    &lazy.remapping.inductive_ids,
                    &lazy.remapping.program_inductive_ids,
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
        substitutions: Vec<(ModuleParamId, ModuleArgument)>,
        reflected_substitutions: Vec<(ModuleParamId, Exp)>,
        remapping: &DeclarationRemapping,
    ) -> (ProgramInductiveId, bool) {
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
            &substitutions,
            &reflected_substitutions,
            remapping,
        );
        if self
            .namespace_arguments_equal(&arguments, &self.namespace_arguments(origin.source.module))
        {
            return (origin.source, false);
        }
        if let Some((&id, _)) = self.nominal_datatypes.iter().find(|(_, candidate)| {
            candidate.source == origin.source
                && self.namespace_arguments_shareable(&arguments)
                && self.namespace_arguments_equal(&arguments, &candidate.arguments)
        }) {
            return (id, false);
        }
        let id = self.reserve_program_inductive(module);
        self.nominal_datatypes.insert(
            id,
            super::namespaces::Specialization {
                source: origin.source,
                arguments,
            },
        );
        self.lazy_program_inductives.insert(
            id,
            LazyProgramInductive {
                source,
                substitutions,
                remapping: DeclarationRemapping::default(),
            },
        );
        (id, true)
    }

    pub(crate) fn set_lazy_program_inductive_remapping(
        &mut self,
        id: ProgramInductiveId,
        remapping: DeclarationRemapping,
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
        remapping: DeclarationRemapping,
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

    pub fn publish_item(&mut self, module: ModuleId, item: ModuleItem) -> Result<(), String> {
        let module = self.module_mut(module);
        let name = item.name().to_owned();
        if module.names.contains_key(&name) {
            return Err(format!("Module item '{name}' is already defined"));
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
        binding: ModuleId,
    ) -> Result<(), String> {
        let module = self.module_mut(module);
        if module.imports.contains_key(&name) {
            return Err(format!("Module import '{name}' is already defined"));
        }
        module.imports.insert(name, binding);
        Ok(())
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
