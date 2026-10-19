//! Package-owned raw declarations and references into imported dependency exports.
use super::*;
use artifact::{Identity, Relocate, Relocation, Result};

/// Snapshot IDs escape only when the corresponding catalog entries are published.
pub(crate) struct SnapshotTransaction<'a> {
    snapshots: &'a RefCell<Vec<DeclarationRemapping>>,
    start: usize,
    committed: bool,
}
impl SnapshotTransaction<'_> {
    pub(crate) fn commit(mut self) {
        self.committed = true;
    }
}
impl Drop for SnapshotTransaction<'_> {
    fn drop(&mut self) {
        if !self.committed {
            self.snapshots.borrow_mut().truncate(self.start);
        }
    }
}

pub(crate) struct Boundary {
    pub modules: usize,
    pub symbols: usize,
    pub remappings: usize,
    snapshots: usize,
    pub kernel_definitions: HashSet<DefId>,
    hir_symbols: HashSet<resolve::hir::BindingId>,
    kernel: kernel::exports::Boundary,
    arena: super::super::exp::exports::Boundary,
}

#[derive(serde::Serialize, serde::Deserialize, Relocate)]
pub(crate) struct Export {
    pub modules: Vec<(ModuleId, ModuleEnv)>,
    pub symbols: Vec<(SymbolId, String, bool)>,
    pub remappings: crate::raw::remapping_checkpoint::Export,
    pub remapping_origins: HashMap<RemappingId, RemappingOrigin>,
    pub kernel: kernel::exports::EnvironmentExport,
    pub arena: super::super::exp::exports::Export,
    pub kernel_definitions: HashMap<DefId, kernel::ids::DefinitionId>,
    pub hir_symbols: HashMap<resolve::hir::BindingId, SymbolId>,
    #[serde(deserialize_with = "super::shared_vectors::deserialize")]
    definition_parameters: HashMap<DefId, Arc<Vec<SymbolId>>>,
    pub namespace_bindings: HashMap<ModuleId, NamespaceBinding>,
    pub checking_scopes: HashMap<ModuleId, ModuleId>,
    #[serde(deserialize_with = "super::shared_vectors::deserialize")]
    checking_contexts: HashMap<ModuleId, Arc<crate::raw::exp::ExpContext>>,
    #[serde(deserialize_with = "super::shared_vectors::deserialize")]
    checking_program_contexts: HashMap<ModuleId, Arc<crate::raw::program::ProgramContext>>,
    #[serde(with = "super::declaration_checkpoint::definitions")]
    lazy_definitions: HashMap<DefId, LazyDefinition>,
    #[serde(with = "super::declaration_checkpoint::inductives")]
    lazy_inductives: HashMap<InductiveId, LazyInductive>,
    #[serde(with = "super::declaration_checkpoint::specializations")]
    nominal_definitions: HashMap<DefId, super::super::namespaces::Specialization<DefId>>,
    #[serde(with = "super::declaration_checkpoint::specializations")]
    nominal_inductives: HashMap<InductiveId, super::super::namespaces::Specialization<InductiveId>>,
    #[serde(with = "super::declaration_checkpoint::specializations")]
    prospective_inductives:
        HashMap<InductiveId, super::super::namespaces::Specialization<InductiveId>>,
    #[serde(with = "super::declaration_checkpoint::specializations")]
    nominal_datatypes:
        HashMap<ProgramInductiveId, super::super::namespaces::Specialization<ProgramInductiveId>>,
    #[serde(with = "super::declaration_checkpoint::datatypes")]
    lazy_program_inductives: HashMap<ProgramInductiveId, LazyProgramInductive>,
}

impl Export {
    /// Follow language-visible source namespaces and their captured environments.
    /// Declaration slots remain intact within a retained module: their local IDs
    /// are stable even when an earlier provisional slot was never published.
    fn retain_owned_reachable(
        &mut self,
        environment: &CrateEnv,
        roots: &[ModuleId],
        external: &mut impl FnMut(kernel::syntax::Expression) -> bool,
    ) -> Result<()> {
        use std::collections::BTreeSet;
        let _phase = crate::profiling::Phase::start("artifact.raw-retain-reachable");
        let mut reachable = BTreeSet::new();
        reachable.extend(
            roots
                .iter()
                .map(|id| Identity::scalar("raw.module", id.0 as u64)),
        );
        // A shared expression may already name a raw nominal whose kernel
        // declaration was first registered in this package. Its expression is
        // external, but the newly registered classifier must still be exported.
        reachable.extend(
            self.kernel
                .parameters
                .iter()
                .map(|(id, _)| Identity::scalar("parameter", id.0)),
        );
        reachable.extend(
            self.kernel
                .inductives
                .iter()
                .map(|(id, _)| Identity::scalar("inductive", id.0)),
        );
        reachable.extend(
            self.kernel
                .datatypes
                .iter()
                .map(|(id, _)| Identity::scalar("datatype", id.0)),
        );
        let mut modules = HashSet::new();
        let mut remappings = HashSet::new();
        let mut arena_reachability = self.arena.reachability()?;
        let mut kernel_reachability = self.kernel.reachability(&environment.arena.core);
        let mut remapping_tables = HashSet::new();
        let module_entries: HashMap<_, _> = self
            .modules
            .iter()
            .map(|(id, module)| (*id, module))
            .collect();
        macro_rules! group {
            ($field:ident) => {
                let $field = self.$field.iter().fold(
                    HashMap::<ModuleId, Vec<_>>::new(),
                    |mut groups, (key, value)| {
                        groups.entry(key.module).or_default().push((key, value));
                        groups
                    },
                );
            };
        }
        group!(kernel_definitions);
        group!(definition_parameters);
        group!(lazy_definitions);
        group!(lazy_inductives);
        group!(lazy_program_inductives);
        group!(nominal_definitions);
        group!(nominal_inductives);
        group!(prospective_inductives);
        group!(nominal_datatypes);
        let mut pending: Vec<_> = reachable.iter().cloned().collect();
        while !pending.is_empty() {
            let frontier = std::mem::take(&mut pending);
            let mut references = Relocation::collecting();
            for identity in &frontier {
                let Identity::Scalar { space, value } = identity else {
                    continue;
                };
                let module = if space == "raw.module" {
                    Some(ModuleId(*value as u32))
                } else if matches!(space.as_str(), "inductive" | "datatype" | "parameter") {
                    Some(ModuleId((value >> 32) as u32))
                } else {
                    None
                };
                if let Some(id) = module
                    && modules.insert(id)
                {
                    let mut own_id = id;
                    own_id.relocate(&mut references)?;
                    if let Some(module) = module_entries.get(&id) {
                        (*module).clone().relocate(&mut references)?;
                    }
                    macro_rules! module_table {
                        ($field:ident) => {
                            if let Some(value) = self.$field.get(&id) {
                                value.clone().relocate(&mut references)?;
                            }
                        };
                    }
                    module_table!(namespace_bindings);
                    module_table!(checking_scopes);
                    module_table!(checking_contexts);
                    module_table!(checking_program_contexts);
                    macro_rules! declaration_table {
                        ($field:ident) => {
                            for &(key, value) in $field.get(&id).into_iter().flatten() {
                                (key.clone(), value.clone()).relocate(&mut references)?;
                            }
                        };
                    }
                    declaration_table!(kernel_definitions);
                    declaration_table!(definition_parameters);
                    declaration_table!(lazy_definitions);
                    declaration_table!(lazy_inductives);
                    declaration_table!(lazy_program_inductives);
                    declaration_table!(nominal_definitions);
                    declaration_table!(nominal_inductives);
                    declaration_table!(prospective_inductives);
                    declaration_table!(nominal_datatypes);
                }
                if space == "raw.remapping" && remappings.insert(*value as usize) {
                    let id = RemappingId(*value as usize);
                    if let Some(origin) = environment.remapping_origins.get(&id) {
                        origin.clone().relocate(&mut references)?;
                    }
                    let map = environment
                        .remappings
                        .get(id.0)
                        .ok_or_else(|| artifact::Error("reachable remapping missing".into()))?;
                    // Visiting scalar pairs keeps inherited Arc tables shared.
                    macro_rules! mappings {
                        ($field:ident) => {
                            map.$field
                                .collect_references(&mut references, &mut remapping_tables)?;
                        };
                    }
                    mappings!(module_ids);
                    mappings!(definition_ids);
                    mappings!(inductive_ids);
                    mappings!(program_inductive_ids);
                }
            }
            arena_reachability.extend(&frontier, &mut references)?;
            let mut discovered: BTreeSet<_> = frontier.into_iter().collect();
            discovered.extend(references.into_identities());
            kernel_reachability.extend(&mut discovered, external)?;
            for identity in discovered {
                if reachable.insert(identity.clone()) {
                    pending.push(identity);
                }
            }
        }
        self.modules.retain(|(id, _)| modules.contains(id));
        macro_rules! module_table {
            ($field:ident) => {
                self.$field.retain(|key, _| modules.contains(key));
            };
        }
        module_table!(namespace_bindings);
        module_table!(checking_scopes);
        module_table!(checking_contexts);
        module_table!(checking_program_contexts);
        macro_rules! declaration_table {
            ($field:ident) => {
                self.$field.retain(|key, _| modules.contains(&key.module));
            };
        }
        declaration_table!(kernel_definitions);
        declaration_table!(definition_parameters);
        declaration_table!(lazy_definitions);
        declaration_table!(lazy_inductives);
        declaration_table!(lazy_program_inductives);
        declaration_table!(nominal_definitions);
        declaration_table!(nominal_inductives);
        declaration_table!(prospective_inductives);
        declaration_table!(nominal_datatypes);
        drop(arena_reachability);
        self.arena.retain_reachable(&reachable);
        drop(kernel_reachability);
        self.kernel.retain_reachable(&reachable);
        Ok(())
    }

    pub(crate) fn canonicalize(&mut self, source_modules: &[ModuleId]) -> Result<()> {
        let source_order: HashMap<_, _> = source_modules
            .iter()
            .enumerate()
            .map(|(position, id)| (*id, position))
            .collect();
        let order = |id: &ModuleId| (source_order.get(id).copied().unwrap_or(usize::MAX), id.0);
        // Source namespaces retain declaration order, including repeated names.
        // Generated namespaces and attachment sets have no source position.
        self.modules.sort_by_key(|(id, _)| order(id));
        for (_, module) in &mut self.modules {
            module.children.sort_by_key(&order);
            module.bindings.sort_by_key(|id| id.0);
        }
        self.symbols.sort_by_key(|(id, _, _)| id.0);
        self.arena.canonicalize();
        self.kernel.canonicalize();
        self.remappings.canonicalize()?;
        Ok(())
    }
}

impl CrateEnv {
    pub(crate) fn snapshot_transaction(&self) -> SnapshotTransaction<'_> {
        SnapshotTransaction {
            snapshots: &self.remappings.snapshots,
            start: self.remappings.snapshots.borrow().len(),
            committed: false,
        }
    }

    #[cfg(test)]
    pub(crate) fn snapshot_count(&self) -> usize {
        self.remappings.snapshots.borrow().len()
    }

    pub(crate) fn exported_symbol(&self, id: SymbolId) -> (String, bool) {
        let name = &self.symbols[id.index()];
        (name.clone(), self.symbol_ids.get(name) == Some(&id))
    }

    pub(crate) fn boundary(&self) -> Boundary {
        Boundary {
            modules: self.modules.len(),
            symbols: self.symbols.len(),
            remappings: self.remappings.len(),
            snapshots: self.remappings.snapshots.borrow().len(),
            kernel_definitions: self.kernel_definitions.borrow().keys().copied().collect(),
            hir_symbols: self.hir_symbols.keys().copied().collect(),
            kernel: self.kernel.borrow().boundary(),
            arena: self.arena.boundary(),
        }
    }
    #[cfg(test)]
    pub(crate) fn export_since(&self, base: &Boundary) -> Result<Export> {
        self.export_since_with_snapshots(base, |_| true, None, &mut |_| false)
    }

    pub(crate) fn export_since_with_snapshots(
        &self,
        base: &Boundary,
        external_snapshot: impl Fn(RemappingSnapshotId) -> bool,
        roots: Option<&[ModuleId]>,
        external: &mut impl FnMut(kernel::syntax::Expression) -> bool,
    ) -> Result<Export> {
        let mut export = Export {
            modules: self
                .modules
                .iter()
                .enumerate()
                .skip(base.modules)
                .map(|(i, v)| (ModuleId(i as u32), v.as_ref().clone()))
                .collect(),
            symbols: Vec::new(),
            remappings: crate::raw::remapping_checkpoint::Export::empty(),
            remapping_origins: HashMap::new(),
            kernel: self.kernel.borrow().export_since(&base.kernel)?,
            arena: self.arena.export_since(&base.arena),
            kernel_definitions: self
                .kernel_definitions
                .borrow()
                .iter()
                .filter(|(key, _)| !base.kernel_definitions.contains(key))
                .map(|(k, v)| (*k, *v))
                .collect(),
            hir_symbols: self
                .hir_symbols
                .iter()
                .filter(|(key, _)| !base.hir_symbols.contains(key))
                .map(|(k, v)| (*k, *v))
                .collect(),
            definition_parameters: self
                .definition_parameters
                .iter()
                .filter(|(key, _)| key.module.index() >= base.modules)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            namespace_bindings: self
                .namespace_bindings
                .iter()
                .filter(|(key, _)| key.index() >= base.modules)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            checking_scopes: self
                .checking_scopes
                .iter()
                .filter(|(key, _)| key.index() >= base.modules)
                .map(|(k, v)| (*k, *v))
                .collect(),
            checking_contexts: self
                .checking_contexts
                .iter()
                .filter(|(key, _)| key.index() >= base.modules)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            checking_program_contexts: self
                .checking_program_contexts
                .iter()
                .filter(|(key, _)| key.index() >= base.modules)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            lazy_definitions: self
                .lazy_definitions
                .iter()
                .filter(|(key, _)| key.module.index() >= base.modules)
                .map(|(k, v)| (k, v.clone()))
                .collect(),
            lazy_inductives: self
                .lazy_inductives
                .iter()
                .filter(|(key, _)| key.module.index() >= base.modules)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            nominal_definitions: self
                .nominal_definitions
                .iter()
                .filter(|(key, _)| key.module.index() >= base.modules)
                .map(|(k, v)| (k, v.clone()))
                .collect(),
            nominal_inductives: self
                .nominal_inductives
                .iter()
                .filter(|(key, _)| key.module.index() >= base.modules)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            prospective_inductives: self
                .prospective_inductives
                .iter()
                .filter(|(key, _)| key.module.index() >= base.modules)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            nominal_datatypes: self
                .nominal_datatypes
                .iter()
                .filter(|(key, _)| key.module.index() >= base.modules)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            lazy_program_inductives: self
                .lazy_program_inductives
                .iter()
                .filter(|(key, _)| key.module.index() >= base.modules)
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
        };
        if let Some(roots) = roots {
            export.retain_owned_reachable(self, roots, external)?;
        }
        // Allocation suffixes may contain abandoned specialization attempts.
        // Retain the tables reached by the package metadata, not every attempt.
        let mut references = Relocation::collecting();
        export.relocate(&mut references)?;
        let references = references.into_identities();
        let mut remappings: std::collections::BTreeSet<_> = references
            .iter()
            .filter_map(|identity| match identity {
                Identity::Scalar { space, value } if space == "raw.remapping" => {
                    Some(*value as usize)
                }
                _ => None,
            })
            .collect();
        let mut pending: Vec<_> = remappings.iter().copied().collect();
        while let Some(id) = pending.pop() {
            if id < base.remappings {
                continue;
            }
            if let Some(origin) = self.remapping_origins.get(&RemappingId(id)) {
                export
                    .remapping_origins
                    .insert(RemappingId(id), origin.clone());
                if let RemappingOrigin::Composition { next, previous } = origin {
                    for parent in [next, previous] {
                        if remappings.insert(parent.0) {
                            pending.push(parent.0);
                        }
                    }
                }
            }
        }
        let mut snapshots = self.remappings.snapshots.borrow_mut();
        let snapshot_ids: Vec<_> = remappings
            .iter()
            .copied()
            .filter(|id| *id >= base.remappings)
            .map(|id| {
                let snapshot = RemappingSnapshotId(snapshots.len());
                snapshots.push(self.remappings[id].clone());
                snapshot
            })
            .collect();
        let dependencies: Vec<_> = snapshots[..base.snapshots]
            .iter()
            .enumerate()
            .filter(|(id, _)| *id == 0 || external_snapshot(RemappingSnapshotId(*id)))
            .map(|(id, map)| (RemappingSnapshotId(id), map))
            .collect();
        export.remappings = crate::raw::remapping_checkpoint::Export::capture_selected(
            &self.remappings,
            base.remappings,
            &remappings,
            &dependencies,
            snapshot_ids,
        )?;
        export.symbols = references
            .iter()
            .filter_map(|identity| match identity {
                Identity::Scalar { space, value }
                    if space == "symbol" && *value as usize >= base.symbols =>
                {
                    let id = SymbolId(*value as u32);
                    self.symbols
                        .get(id.index())
                        .map(|name| (id, name.clone(), self.symbol_ids.get(name) == Some(&id)))
                }
                _ => None,
            })
            .collect();
        Ok(export)
    }
    pub(crate) fn reserve_export(&self, export: &Export, r: &mut Relocation) -> Result<()> {
        r.insert("raw.module", 0, 0)?;
        r.insert("symbol", 0, 0)?;
        let mut next = self.modules.len();
        for (id, _) in &export.modules {
            if r.get("raw.module", id.0 as u64).is_none() {
                r.insert("raw.module", id.0 as u64, next as u64)?;
                next += 1;
            }
        }
        let mut next = self.symbols.len();
        for (id, name, interned) in &export.symbols {
            if r.get("symbol", id.0 as u64).is_some() {
                continue;
            }
            let mut name = name.clone();
            name.relocate(r)?;
            let value = if let Some(id) = interned.then(|| self.symbol_ids.get(&name)).flatten() {
                id.0 as usize
            } else {
                let n = next;
                next += 1;
                n
            };
            r.insert("symbol", id.0 as u64, value as u64)?;
        }
        let mut next = self.remappings.len();
        for id in &export.remappings.ids {
            if r.get("raw.remapping", id.0 as u64).is_none() {
                r.insert("raw.remapping", id.0 as u64, next as u64)?;
                next += 1;
            }
        }
        let mut next = self.remappings.snapshots.borrow().len();
        for id in &export.remappings.snapshots {
            if r.get("raw.remapping.snapshot", id.0 as u64).is_none() {
                r.insert("raw.remapping.snapshot", id.0 as u64, next as u64)?;
                next += 1;
            }
        }
        export
            .kernel
            .reserve_definitions(&self.kernel.borrow(), r)?;
        Ok(())
    }
    pub(crate) fn import_export(&mut self, export: Export) -> Result<()> {
        // The package caller stages an import in a disposable checker until all layers succeed.
        self.namespace_argument_cache.get_mut().originals.clear();
        self.kernel.get_mut().import_export(export.kernel)?;
        self.arena.import_export(export.arena)?;
        for (id, name, interned) in export.symbols {
            if id.index() == self.symbols.len() {
                self.symbols.push(name.clone());
                if interned {
                    self.symbol_ids.insert(name, id);
                }
            } else if self.symbols.get(id.index()) != Some(&name) {
                return Err(artifact::Error("symbol reservation mismatch".into()));
            }
        }
        let children: Vec<_> = export
            .modules
            .iter()
            .filter_map(|(id, m)| m.parent.map(|p| (p, *id)))
            .collect();
        for (id, incoming) in export.modules {
            if id.index() == self.modules.len() {
                self.modules.push(Box::new(incoming));
            } else {
                let existing = self
                    .modules
                    .get_mut(id.index())
                    .ok_or_else(|| artifact::Error("raw module reservation mismatch".into()))?;
                merge_module(existing, incoming)?;
            }
        }
        for (parent, child) in children {
            let module = self
                .modules
                .get_mut(parent.index())
                .ok_or_else(|| artifact::Error("missing raw parent module".into()))?;
            if !module.children.contains(&child) {
                module.children.push(child);
            }
        }
        let tables = &mut self.remappings;
        let snapshots = tables.snapshots.get_mut();
        let live = &mut tables.live;
        let dependencies: Vec<_> = snapshots
            .iter()
            .enumerate()
            .map(|(id, map)| (RemappingSnapshotId(id), map))
            .collect();
        for (id, snapshot, remapping) in export.remappings.restore(&dependencies)? {
            if snapshot.0 == snapshots.len() {
                snapshots.push(remapping.clone());
            } else if let Some(previous) = snapshots.get(snapshot.0) {
                same(previous, &remapping)?;
            } else {
                return Err(artifact::Error(
                    "raw remapping snapshot reservation mismatch".into(),
                ));
            }
            if id.0 == live.len() {
                live.push(remapping);
            } else if id.0 >= live.len() {
                return Err(artifact::Error("raw remapping reservation mismatch".into()));
            } else {
                let existing = &mut live[id.0];
                existing
                    .module_ids
                    .merge_compatible(&remapping.module_ids)?;
                existing
                    .definition_ids
                    .merge_compatible(&remapping.definition_ids)?;
                existing
                    .inductive_ids
                    .merge_compatible(&remapping.inductive_ids)?;
                existing
                    .program_inductive_ids
                    .merge_compatible(&remapping.program_inductive_ids)?;
            }
        }
        for (id, origin) in export.remapping_origins {
            if let Some(previous) = self.remapping_origins.get(&id) {
                same(previous, &origin)?;
            } else {
                self.remapping_origins.insert(id, origin);
            }
        }
        self.kernel_definitions
            .get_mut()
            .extend(export.kernel_definitions);
        self.hir_symbols.extend(export.hir_symbols);
        self.definition_parameters
            .extend(export.definition_parameters);
        self.namespace_bindings.extend(export.namespace_bindings);
        self.checking_scopes.extend(export.checking_scopes);
        self.checking_contexts.extend(export.checking_contexts);
        self.checking_program_contexts
            .extend(export.checking_program_contexts);
        self.lazy_definitions.extend(export.lazy_definitions);
        self.lazy_inductives.extend(export.lazy_inductives);
        self.nominal_definitions.extend(export.nominal_definitions);
        self.nominal_inductives.extend(export.nominal_inductives);
        self.prospective_inductives
            .extend(export.prospective_inductives);
        self.nominal_datatypes.extend(export.nominal_datatypes);
        self.lazy_program_inductives
            .extend(export.lazy_program_inductives);
        Ok(())
    }
}

impl Export {
    pub(crate) fn nominal_mappings(&mut self, r: &mut Relocation) -> Result<()> {
        let mut collect = Relocation::collecting();
        self.relocate(&mut collect)?;
        for id in collect.identities() {
            if let Identity::Scalar { space, value } = id
                && matches!(space.as_str(), "inductive" | "datatype" | "parameter")
                && r.get(space, *value).is_none()
            {
                let module = r.id("raw.module", value >> 32)?;
                r.insert(space, *value, (module << 32) | (value & 0xffff_ffff))?;
            }
        }
        Ok(())
    }
}

fn same<T: serde::Serialize>(left: &T, right: &T) -> Result<()> {
    let encode = |value: &T| {
        artifact::canonical::to_vec(value, crate::MAX_PACKAGE_BYTES)
            .map_err(|error| artifact::Error(error.to_string()))
    };
    if encode(left)? != encode(right)? {
        return Err(artifact::Error(
            "overlapping package declaration differs".into(),
        ));
    }
    Ok(())
}
fn merge_cells<T: serde::Serialize>(
    existing: &mut Vec<OnceCell<T>>,
    incoming: Vec<OnceCell<T>>,
) -> Result<()> {
    for (index, cell) in incoming.into_iter().enumerate() {
        if index == existing.len() {
            existing.push(cell);
            continue;
        }
        if let Some(value) = cell.into_inner() {
            if let Some(previous) = existing[index].get() {
                same(previous, &value)?;
            } else {
                let _ = existing[index].set(value);
            }
        }
    }
    Ok(())
}
fn merge_module(existing: &mut ModuleEnv, incoming: ModuleEnv) -> Result<()> {
    if existing.name != incoming.name || existing.parent != incoming.parent {
        return Err(artifact::Error(
            "overlapping package module identity differs".into(),
        ));
    }
    if existing.parameters.is_empty() {
        existing.parameters = incoming.parameters;
    } else if !incoming.parameters.is_empty() {
        same(&existing.parameters, &incoming.parameters)?;
    }
    merge_cells(&mut existing.definitions, incoming.definitions)?;
    merge_cells(&mut existing.inductives, incoming.inductives)?;
    merge_cells(
        &mut existing.program_inductives,
        incoming.program_inductives,
    )?;
    if existing.items.is_empty() {
        existing.items = incoming.items;
        existing.names = incoming.names;
        existing.hir_items = incoming.hir_items;
    } else if !incoming.items.is_empty() {
        same(&existing.items, &incoming.items)?;
    }
    Arc::make_mut(&mut existing.hir_names).extend(Arc::unwrap_or_clone(incoming.hir_names));
    existing.imports.extend(incoming.imports);
    for child in incoming.children {
        if !existing.children.contains(&child) {
            existing.children.push(child);
        }
    }
    for binding in incoming.bindings {
        if !existing.bindings.contains(&binding) {
            existing.bindings.push(binding);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verified_export_follows_deep_namespace_bindings_and_discards_detached_branches() {
        let mut env = CrateEnv::new();
        let boundary = env.boundary();
        let source = env.add_module();
        let mut retained = vec![source];
        let mut current = source;
        for _ in 0..1024 {
            let next = env.add_module_in_scope(source, vec![]).unwrap();
            let remapping = env.store_namespace_remapping(DeclarationRemapping::default(), next);
            env.add_namespace_binding(current, source, next, vec![], HashMap::new(), remapping);
            retained.push(next);
            current = next;
        }
        let detached = env.add_module_in_scope(source, vec![]).unwrap();
        let detached_child = env.add_module_in_scope(source, vec![]).unwrap();
        let remapping =
            env.store_namespace_remapping(DeclarationRemapping::default(), detached_child);
        env.add_namespace_binding(
            detached,
            source,
            detached_child,
            vec![],
            HashMap::new(),
            remapping,
        );
        let export = env
            .export_since_with_snapshots(&boundary, |_| true, Some(&[source]), &mut |_| false)
            .unwrap();
        let actual: HashSet<_> = export.modules.iter().map(|(id, _)| *id).collect();
        assert_eq!(actual, retained.into_iter().collect());
        assert!(!actual.contains(&detached));
        assert!(!actual.contains(&detached_child));
        assert_eq!(export.namespace_bindings.len(), 1024);
        assert_eq!(export.remappings.ids.len(), 1024);
    }

    #[test]
    fn verified_exports_drop_detached_provisional_scopes_but_pending_keeps_them() {
        let mut env = CrateEnv::new();
        let boundary = env.boundary();
        let source = env.add_module();
        let retained = env.add_module_in_scope(source, vec![]).unwrap();
        let discarded = env.add_module_in_scope(source, vec![]).unwrap();
        let remapping = env.store_namespace_remapping(DeclarationRemapping::default(), retained);
        env.add_namespace_binding(source, source, retained, vec![], HashMap::new(), remapping);
        let discarded_map =
            env.store_namespace_remapping(DeclarationRemapping::default(), discarded);
        let verified = env
            .export_since_with_snapshots(&boundary, |_| true, Some(&[source]), &mut |_| false)
            .unwrap();
        let ids: HashSet<_> = verified.modules.iter().map(|(id, _)| *id).collect();
        assert!(ids.contains(&source));
        assert!(ids.contains(&retained));
        assert!(!ids.contains(&discarded));
        assert!(!verified.checking_scopes.contains_key(&discarded));
        assert!(!verified.checking_contexts.contains_key(&discarded));
        assert!(!verified.remappings.ids.contains(&discarded_map));
        let pending = env.export_since(&boundary).unwrap();
        assert!(pending.modules.iter().any(|(id, _)| *id == discarded));
        assert!(pending.checking_scopes.contains_key(&discarded));
    }

    #[test]
    fn staging_keeps_dependency_remapping_tables_external() {
        let mut env = CrateEnv::new();
        let before_dependency = env.boundary();
        let root = env.root_module();
        let source = env.add_module();
        let namespace = env.add_module();
        let mut map = DeclarationRemapping::default();
        for index in 1..=5000 {
            map.module_ids
                .insert(ModuleId(index), ModuleId(index + 5000));
        }
        let inherited = env.store_namespace_remapping(map, namespace);
        env.add_namespace_binding(root, source, namespace, vec![], HashMap::new(), inherited);
        env.export_since(&before_dependency).unwrap();

        // Borrowed artifact import stages the whole checker through this codec.
        let bytes = postcard::to_allocvec(&env).unwrap();
        let mut staged: CrateEnv = postcard::from_bytes(&bytes).unwrap();
        staged.restore_shared_arena();
        let boundary = staged.boundary();
        let materialized = staged.add_module();
        let mut additions = DeclarationRemapping::default();
        additions
            .module_ids
            .insert(ModuleId(10001), ModuleId(10002));
        let composed = additions.after(staged.remapping(inherited));
        let remapping = staged.store_namespace_remapping(composed, materialized);
        staged.add_namespace_binding(
            root,
            source,
            materialized,
            vec![],
            HashMap::new(),
            remapping,
        );
        let export = staged.export_since(&boundary).unwrap();
        let bytes = artifact::canonical::to_vec(&export.remappings, 100_000).unwrap();
        assert!(
            bytes.len() < 512,
            "staging duplicated the 5000-entry dependency map: {} bytes",
            bytes.len()
        );
    }

    #[test]
    fn exports_reachable_remappings_and_preserves_creation_origin_when_attachments_grow() {
        let mut env = CrateEnv::new();
        let boundary = env.boundary();
        let root = env.root_module();
        let source = env.add_module();
        let namespace = env.add_module();
        let remapping = env.store_namespace_remapping(DeclarationRemapping::default(), namespace);
        env.add_namespace_binding(root, source, namespace, vec![], HashMap::new(), remapping);
        let discarded = env.store_remapping(DeclarationRemapping::default());
        let unused_symbol = env.intern("unused attempt");
        let before = env.export_since(&boundary).unwrap();
        assert_eq!(before.remappings.ids, vec![remapping]);
        assert!(!before.remapping_origins.contains_key(&discarded));
        assert!(before.symbols.iter().all(|(id, _, _)| *id != unused_symbol));
        let origin =
            artifact::canonical::to_vec(&before.remapping_origins[&remapping], 1000).unwrap();

        let extra = env.add_module();
        env.add_namespace_binding(root, source, extra, vec![], HashMap::new(), remapping);
        let after = env.export_since(&boundary).unwrap();
        assert_eq!(after.remappings.ids, vec![remapping]);
        assert_eq!(
            origin,
            artifact::canonical::to_vec(&after.remapping_origins[&remapping], 1000).unwrap()
        );
    }
}
