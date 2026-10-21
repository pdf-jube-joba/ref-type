//! Source-backed namespace members. A view allocates member metadata on lookup.
use super::*;

#[derive(Debug, Clone, artifact::Relocate, serde::Serialize, serde::Deserialize)]
pub(super) struct NamespaceView {
    pub source: ModuleId,
    pub identity: ModuleId,
    pub arguments: super::super::namespaces::SharedArguments,
    pub reflected: Arc<[(ModuleParamId, Exp)]>,
}

impl NamespaceView {
    fn definition(&self, id: &mut DefId) {
        if id.module == self.source {
            id.module = self.identity;
        }
    }

    pub(super) fn map_item(&self, item: &mut ModuleItem) {
        match item {
            ModuleItem::Definition { definition, .. } => self.definition(definition),
            ModuleItem::Inductive {
                inductive,
                associated_definitions,
                ..
            }
            | ModuleItem::Record {
                inductive,
                associated_definitions,
                ..
            } => {
                if inductive.module == self.source {
                    inductive.module = self.identity;
                }
                for (_, id) in associated_definitions.iter_mut() {
                    self.definition(id);
                }
            }
            ModuleItem::ProgramInductive {
                inductive,
                reflected,
                associated_definitions,
                ..
            } => {
                if inductive.module == self.source {
                    inductive.module = self.identity;
                }
                if reflected.module == self.source {
                    reflected.module = self.identity;
                }
                for (_, id) in associated_definitions.iter_mut() {
                    self.definition(id);
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
pub struct ModuleItems<'a>(pub(super) &'a ModuleEnv);

impl<'a> ModuleItems<'a> {
    pub fn len(self) -> usize {
        self.0.items.len()
    }
    pub fn is_empty(self) -> bool {
        self.0.items.is_empty()
    }
    pub fn iter(self) -> impl Iterator<Item = &'a ModuleItem> + Clone {
        (0..self.len()).map(move |index| self.0.item_at(index))
    }
    pub fn to_vec(self) -> Vec<ModuleItem> {
        self.iter().cloned().collect()
    }
}

impl<'a> IntoIterator for ModuleItems<'a> {
    type Item = &'a ModuleItem;
    type IntoIter =
        std::iter::Map<std::ops::Range<usize>, Box<dyn FnMut(usize) -> &'a ModuleItem + 'a>>;
    fn into_iter(self) -> Self::IntoIter {
        (0..self.len()).map(Box::new(move |index| self.0.item_at(index)))
    }
}
impl std::ops::Index<usize> for ModuleItems<'_> {
    type Output = ModuleItem;
    fn index(&self, index: usize) -> &ModuleItem {
        self.0.item_at(index)
    }
}
impl PartialEq for ModuleItems<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}
impl Eq for ModuleItems<'_> {}
impl Hash for ModuleItems<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for item in self.iter() {
            item.hash(state);
        }
    }
}
impl PartialEq<ModuleItems<'_>> for Vec<ModuleItem> {
    fn eq(&self, other: &ModuleItems<'_>) -> bool {
        self.iter().eq(other.iter())
    }
}

trait MemberId: Copy + Eq + Hash {
    fn module(self) -> ModuleId;
    fn with_module(self, module: ModuleId) -> Self;
}
macro_rules! member_id {
    ($($id:ty),*) => {$(
        impl MemberId for $id {
            fn module(self) -> ModuleId { self.module }
            fn with_module(self, module: ModuleId) -> Self { Self { module, ..self } }
        }
    )*};
}
member_id!(DefId, InductiveId, ProgramInductiveId);

struct ViewMap<'a, I> {
    env: &'a CrateEnv,
    entries: &'a SharedMap<I>,
    modules: &'a SharedMap<ModuleId>,
}
impl<I: MemberId> super::super::shared_map::IdLookup<I> for ViewMap<'_, I> {
    fn get(&self, key: &I) -> Option<&I> {
        self.entries.get(key)
    }
    fn is_empty(&self) -> bool {
        self.entries.is_empty() && self.modules.is_empty()
    }
    fn resolve(&self, key: &I) -> Option<I> {
        let explicit = self.entries.get(key).copied();
        let current = explicit.unwrap_or(*key);
        let Some(target) = self.modules.get(&current.module()).copied() else {
            return explicit;
        };
        let Some(view) = &self.env.module(target).view else {
            return explicit;
        };
        Some(current.with_module(view.identity))
    }
}

impl DeclarationRemapping {
    pub(crate) fn definitions<'a>(
        &'a self,
        env: &'a CrateEnv,
    ) -> impl super::super::shared_map::IdLookup<DefId> + 'a {
        ViewMap {
            env,
            entries: &self.definition_ids,
            modules: &self.module_ids,
        }
    }
    pub(crate) fn inductives<'a>(
        &'a self,
        env: &'a CrateEnv,
    ) -> impl super::super::shared_map::IdLookup<InductiveId> + 'a {
        ViewMap {
            env,
            entries: &self.inductive_ids,
            modules: &self.module_ids,
        }
    }
    pub(crate) fn datatypes<'a>(
        &'a self,
        env: &'a CrateEnv,
    ) -> impl super::super::shared_map::IdLookup<ProgramInductiveId> + 'a {
        ViewMap {
            env,
            entries: &self.program_inductive_ids,
            modules: &self.module_ids,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct ViewKey {
    source: ModuleId,
    generation: (usize, usize, usize, usize),
    arguments: Arc<[(ModuleParamId, ModuleArgument)]>,
    scope: super::super::namespaces::NamespaceScopeId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct ViewIdentityKey {
    source: ModuleId,
    arguments: Arc<[(ModuleParamId, ModuleArgument)]>,
    scope: super::super::namespaces::NamespaceScopeId,
}

impl CrateEnv {
    fn index_restored_views(&mut self) {
        if self.view_identities_indexed {
            return;
        }
        self.view_instances.clear();
        self.view_identities.clear();
        for index in 0..self.modules.len() {
            let Some(view) = self.modules[index].view.clone() else {
                continue;
            };
            let module = ModuleId(index as u32);
            let program = self.checking_program_contexts.get(&module).cloned();
            let scope = if self.namespace_arguments_shareable(&view.arguments)
                && program.is_none()
                && !self.namespace_has_local_context(view.source)
                && !self.checking_program_contexts.contains_key(&view.source)
            {
                super::super::namespaces::NamespaceScopeId::CLOSED
            } else {
                self.namespace_argument_cache.borrow_mut().scope(
                    self.checking_scopes.get(&module).copied().unwrap_or(module),
                    Some(Arc::new(self.definition_context(module))),
                    program,
                )
            };
            let arguments = self
                .namespace_argument_cache
                .borrow_mut()
                .share(&view.arguments);
            self.view_identities
                .entry(ViewIdentityKey {
                    source: view.source,
                    arguments,
                    scope,
                })
                .or_insert(view.identity);
            let shared = self
                .namespace_argument_cache
                .borrow_mut()
                .share_compact(&view.arguments);
            self.modules[index].view.as_mut().unwrap().arguments = shared;
        }
        for binding in self.namespace_bindings.values_mut() {
            binding.arguments = self
                .namespace_argument_cache
                .borrow_mut()
                .share(&binding.arguments);
        }
        self.view_identities_indexed = true;
    }

    /// Each view shares the source's index and argument telescope. Declaration
    /// IDs retain the source ordinal; only the namespace component changes.
    pub(crate) fn bind_namespace_views(
        &mut self,
        owner: ModuleId,
        route: &[ModuleId],
        context: &super::super::exp::ExpContext,
        program_context: &super::super::program::ProgramContext,
        substitutions: &[(ModuleParamId, ModuleArgument)],
        reflected: &[(ModuleParamId, Exp)],
        mut remapping: DeclarationRemapping,
    ) -> Result<(ModuleId, Vec<ModuleId>), crate::error::Error> {
        self.index_restored_views();
        let mut sources: Vec<_> = route.iter().map(|&id| (id, id, true)).collect();
        for &module in route {
            for &id in self.module(module).bindings() {
                let binding = self.binding(id);
                // Anonymous captures belong to the generic source body.
                if self.namespace_has_local_context(id) && !self.module(module).names_binding(id) {
                    continue;
                }
                sources.push((binding.source, id, false));
            }
        }
        let substitutions: Arc<[_]> = substitutions.into();
        let reflected: Arc<[_]> = reflected.into();
        let mut groups = Vec::new();
        let mut construction = None;
        let mut dependencies = Vec::new();
        let mut last = None;
        for (source, item_source, path) in sources {
            let original = self.namespace_binding_id(item_source).map_or_else(
                || self.namespace_arguments(source),
                |id| self.binding(id).arguments.to_vec(),
            );
            let arguments = self.substitute_namespace_arguments(
                &original,
                &substitutions,
                &reflected,
                &remapping,
            );
            let shareable = self.namespace_arguments_shareable(&arguments)
                && program_context.is_empty()
                && !self.namespace_has_local_context(source)
                && !self.checking_program_contexts.contains_key(&source);
            // The owner supplies the context for an open view. Closed views
            // are independent of unused local variables.
            let scope = if shareable {
                super::super::namespaces::NamespaceScopeId::CLOSED
            } else {
                self.namespace_argument_cache.borrow_mut().scope(
                    owner,
                    Some(Arc::new(context.clone())),
                    (!program_context.is_empty()).then(|| Arc::new(program_context.clone())),
                )
            };
            let template = self.module(source);
            let key = ViewKey {
                source,
                generation: (
                    template.items.len(),
                    template.definitions.len(),
                    template.inductives.len(),
                    template.bindings.len(),
                ),
                arguments: self.namespace_argument_cache.borrow_mut().share(&arguments),
                scope,
            };
            let canonical = self.view_instances.get(&key).copied();
            let semantic_key = ViewIdentityKey {
                source,
                arguments: key.arguments.clone(),
                scope,
            };
            let semantic = self.view_identities.get(&semantic_key).copied();
            if let Some(identity) = semantic {
                let template = self.module(source);
                let counts = (
                    template.definitions.len(),
                    template.inductives.len(),
                    template.program_inductives.len(),
                );
                let target = self.module_mut(identity);
                target.definitions.resize_with(counts.0, OnceCell::new);
                target.inductives.resize_with(counts.1, OnceCell::new);
                target
                    .program_inductives
                    .resize_with(counts.2, OnceCell::new);
            }
            if let Some(id) = canonical
                && !path
            {
                if let Some(view) = &self.module(item_source).view {
                    remapping.module_ids.insert(view.identity, id);
                }
                remapping.module_ids.insert(item_source, id);
                if let Some(handle) = construction {
                    *self.reserved_remapping_mut(handle) = remapping.clone();
                }
                self.attach_namespace_binding(owner, id);
                dependencies.push(id);
                if path {
                    last = Some(id);
                }
                continue;
            }
            let id = self.add_modules_in_scope(owner, context.clone(), 1)?[0];
            self.set_program_context(id, Arc::new(program_context.clone()));
            let identity = if let Some(canonical) = canonical {
                self.module(canonical).view.as_ref().unwrap().identity
            } else if let Some(identity) = semantic {
                identity
            } else if shareable
                && self
                    .namespace_arguments_equal(&arguments, &self.namespace_arguments_shared(source))
            {
                source
            } else {
                id
            };
            self.view_identities.entry(semantic_key).or_insert(identity);
            let template = self.module(source);
            let items = template.items.clone();
            let names = template.names.clone();
            let hir_names = template.hir_names.clone();
            let current = || {
                hir_names
                    .iter()
                    .filter_map(|(name, binding)| names.get(name).map(|index| (*binding, *index)))
            };
            let hir_items = if current().count() == template.hir_items.len()
                && current()
                    .all(|(binding, index)| template.hir_items.get(&binding) == Some(&index))
            {
                template.hir_items.clone()
            } else {
                Arc::new(current().collect())
            };
            let definitions = Slots::reserved(if identity == id {
                template.definitions.len()
            } else {
                0
            });
            let inductives = Slots::reserved(if identity == id {
                template.inductives.len()
            } else {
                0
            });
            let shared = self
                .namespace_argument_cache
                .borrow_mut()
                .share_compact(&arguments);
            let reflected = arguments
                .iter()
                .map(|&(parameter, argument)| {
                    let value = match argument {
                        ModuleArgument::Pts(value) => value,
                        ModuleArgument::ProgramType(value) => {
                            super::super::reflection::reflect_value_type(self, value)?
                        }
                        ModuleArgument::ProgramValue(value) => {
                            super::super::reflection::reflect_value(self, value)?
                        }
                    };
                    Ok((parameter, value))
                })
                .collect::<Result<Arc<[_]>, super::super::reflection::ReflectionError>>()?;
            let program_inductives = Slots::reserved(if identity == id {
                self.module(source).program_inductives.len()
            } else {
                0
            });
            let target = self.module_mut(id);
            target.items = items;
            target.names = names;
            target.hir_names = hir_names;
            target.hir_items = hir_items;
            target.definitions = definitions;
            target.inductives = inductives;
            target.program_inductives = program_inductives;
            target.view = Some(NamespaceView {
                source,
                identity,
                arguments: shared,
                reflected,
            });
            if let Some(view) = &self.module(item_source).view {
                remapping.module_ids.insert(view.identity, id);
            }
            remapping.module_ids.insert(item_source, id);
            let handle = *construction
                .get_or_insert_with(|| self.store_namespace_remapping(remapping.clone(), id));
            *self.reserved_remapping_mut(handle) = remapping.clone();
            self.add_namespace_binding(owner, source, id, arguments, HashMap::new(), handle);
            groups.push((key, id, item_source));
            dependencies.push(id);
            if path {
                last = Some(id);
            }
        }
        let last = last.expect("nonempty namespace route");
        if groups.is_empty() {
            return Ok((last, dependencies));
        }
        let remapping = construction.expect("new namespace construction");
        let mut inherited = Vec::new();
        for (key, id, previous) in groups {
            if let Some(previous) = self.namespace_binding_id(previous) {
                inherited.push((id, self.binding(previous).remapping));
            }
            self.view_instances.entry(key).or_insert(id);
        }
        self.compact_remapping(remapping);
        self.inherit_namespace_remappings(remapping, &inherited);
        timing::costs::count("namespace.views", || dependencies.len() as u64);
        Ok((last, dependencies))
    }
}
