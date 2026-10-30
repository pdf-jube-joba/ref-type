//! Reuse an entire checked prefix without relocating overlapping environments.
use super::*;
#[path = "graph_store.rs"]
mod graph_store;
use graph_store::GraphPages;
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};

#[derive(Clone, Default, Serialize, Deserialize)]
pub(crate) struct Metadata {
    key: Fingerprint,
    input: Fingerprint,
    inputs: BTreeMap<String, Fingerprint>,
    syntax: BTreeSet<Vec<String>>,
    coverage: BTreeSet<Vec<String>>,
    history: Vec<Fingerprint>,
    generation: Option<String>,
    bytes: usize,
    graph: Vec<artifact_store::ObjectRef>,
}

impl Metadata {
    fn continuing(&self) -> bool {
        std::env::var("REF_TYPE_CACHE_SESSION")
            .ok()
            .is_some_and(|generation| self.generation.as_ref() == Some(&generation))
    }

    pub(super) fn matches_inputs(
        &self,
        inputs: &[crate::package_inputs::PackageInput],
        packages: &[project::package_loader::PackageInfo],
    ) -> bool {
        self.inputs.iter().all(|(name, input)| {
            packages
                .iter()
                .position(|p| &p.name == name)
                .is_some_and(|i| inputs[i].key == *input)
        })
    }

    pub(super) fn permits(&self, forced: &BTreeSet<Vec<String>>) -> bool {
        self.coverage.is_disjoint(forced)
    }
}

impl PackageRun<'_, '_> {
    fn resume_prefix(
        &mut self,
        request: Fingerprint,
        forced: &BTreeSet<usize>,
        wanted: &BTreeSet<usize>,
    ) -> Option<(PackageChecker, Metadata)> {
        let store = self.database.disk.as_ref()?.store();
        let manifest = store.read_checkpoint(&request).ok()?;
        if manifest.input != request || manifest.resolver.is_some() {
            return None;
        }
        let bytes = store.read_object(manifest.environment.as_ref()?).ok()?;
        let (magic, metadata, bytes): ([u8; 8], Metadata, Vec<u8>) =
            artifact_store::deserialize(&bytes).ok()?;
        let continuing = metadata.continuing();
        if magic != *b"REFSES02"
            || !self.valid_prefix(&metadata)
            || metadata.syntax.iter().any(|path| {
                self.graph
                    .indices
                    .get(path)
                    .is_none_or(|index| !continuing && forced.contains(index))
            })
        {
            return None;
        }
        if metadata.graph != manifest.graph {
            return None;
        }
        let pages = GraphPages::new(self.database.disk.as_ref()?.shared_store());
        pages.validate(&metadata.graph)?;
        let checker = elaboration::with_graph_store(pages, || {
            PackageChecker::restore(&bytes, |id| self.snapshot.source(&id.0).cloned())
        })?;
        self.database.stats.checkpoint_hits += 1;
        self.progress.environment_reused(
            metadata
                .coverage
                .iter()
                .filter(|path| {
                    self.graph
                        .indices
                        .get(*path)
                        .is_some_and(|i| !wanted.contains(i))
                })
                .count(),
        );
        Some((checker, metadata))
    }

    fn save_pending(
        &mut self,
        key: Fingerprint,
        input: Fingerprint,
        coverage: &BTreeSet<Vec<String>>,
        metadata: &Metadata,
        steps: usize,
        bytes: postcard::Result<Vec<u8>>,
        graph: Vec<artifact_store::ObjectRef>,
    ) {
        let saved: Result<(), crate::error::CacheError> = (|| {
            let store = self
                .database
                .disk
                .as_ref()
                .expect("checkpoint store")
                .store();
            let mut metadata = metadata.clone();
            metadata.graph = graph.clone();
            let state =
                bytes.map_err(|error| crate::error::CacheError::Codec(error.to_string()))?;
            let bytes = artifact_store::serialize(&(*b"REFSES02", &metadata, state))?;
            let environment = store.write_object(ObjectKind::Checkpoint, &bytes)?;
            store.publish_checkpoint(&StoreManifest {
                key,
                input,
                coverage: coverage.iter().cloned().collect(),
                environment: Some(environment),
                graph,
                ..Default::default()
            })
        })();
        match saved {
            Ok(()) => {
                self.database.stats.checkpoint_writes += 1;
                self.progress
                    .storage_stats(self.database.cache_store_stats());
                self.progress.checkpoint_saved(steps);
            }
            Err(error) => {
                self.database.stats.checkpoint_skips += 1;
                self.progress.storage_failed(error.to_string());
            }
        }
        self.progress.phase(ProgressPhase::Checking);
    }

    fn prefix_score(
        &self,
        coverage: impl Iterator<Item = impl AsRef<[String]>>,
        wanted: &BTreeSet<usize>,
        forced: &BTreeSet<usize>,
    ) -> Option<(usize, std::cmp::Reverse<usize>)> {
        let mut shared = 0usize;
        let mut extra = 0usize;
        for path in coverage {
            let index = *self.graph.indices.get(path.as_ref())?;
            if forced.contains(&index) {
                return None;
            }
            if wanted.contains(&index) {
                shared += 1;
            } else {
                extra += 1;
            }
        }
        // A large prefix can contain far more unrelated checking state than
        // this request will ever use. Loading it defeats bounded submodule
        // checks, even when it saves a few more source modules. Prefer net
        // useful coverage and rebuild when the irrelevant part dominates.
        (shared > 0 && extra <= shared)
            .then_some((shared.saturating_sub(extra), std::cmp::Reverse(extra)))
    }

    fn valid_prefix(&self, metadata: &Metadata) -> bool {
        metadata.inputs.iter().all(|(name, input)| {
            self.packages
                .iter()
                .position(|p| &p.name == name)
                .is_some_and(|i| self.inputs[i].key == *input)
        })
    }

    fn restore_prefix(
        &mut self,
        wanted: &BTreeSet<usize>,
        forced: &BTreeSet<usize>,
    ) -> (PackageChecker, Metadata) {
        // Completed work in this session belongs to the current verification
        // generation. Forced input ranges apply when entering the session, not
        // when another package requests a dependency checked by this worker.
        if let Some((checker, metadata)) = self.native_active.take()
            && self.valid_prefix(&metadata)
        {
            let extra = metadata
                .coverage
                .iter()
                .filter(|path| {
                    self.graph
                        .indices
                        .get(*path)
                        .is_some_and(|i| !wanted.contains(i))
                })
                .count();
            self.progress.environment_reused(extra);
            return (checker, metadata);
        }
        let mut candidates = BTreeMap::new();
        let unforced = BTreeSet::new();
        for metadata in self.database.prefixes.values() {
            if self.valid_prefix(metadata)
                && let Some(score) = self.prefix_score(
                    metadata.coverage.iter(),
                    wanted,
                    if metadata.continuing() {
                        &unforced
                    } else {
                        forced
                    },
                )
            {
                candidates.insert(metadata.key, (score, Some(metadata.clone()), None));
            }
        }
        if let Some(disk) = &self.database.disk {
            for input in self.inputs {
                for manifest in disk.store().list_matching(&input.key).unwrap_or_default() {
                    if manifest.resolver.is_some()
                        || !manifest.results.is_empty()
                        || !manifest
                            .environment
                            .as_ref()
                            .is_some_and(|o| o.kind == ObjectKind::Checkpoint)
                    {
                        continue;
                    }
                    // A recovered full-check-local invocation can reuse work
                    // completed in its own generation. Validate that generation
                    // in the envelope before loading any graph pages below.
                    if let Some(score) =
                        self.prefix_score(manifest.coverage.iter(), wanted, &unforced)
                    {
                        candidates
                            .entry(manifest.key)
                            .and_modify(|entry| entry.2 = Some(manifest.clone()))
                            .or_insert((score, None, Some(manifest)));
                    }
                }
            }
        }
        let mut candidates: Vec<_> = candidates.into_values().collect();
        candidates.sort_by_key(|entry| std::cmp::Reverse(entry.0));
        for (score, memory, manifest) in candidates {
            let loaded = (|| {
                if let Some(metadata) = memory
                    && let Some(bytes) = self.database.package_environments.get(&metadata.key)
                {
                    return Some((metadata.clone(), bytes.to_vec()));
                }
                let manifest = manifest?;
                let bytes = self
                    .database
                    .disk
                    .as_ref()?
                    .store()
                    .read_object(manifest.environment.as_ref()?)
                    .ok()?;
                let (magic, metadata, state): ([u8; 8], Metadata, Vec<u8>) =
                    artifact_store::deserialize(&bytes).ok()?;
                (magic == *b"REFSES02" && metadata.key == manifest.key).then_some((metadata, state))
            })();
            let Some((metadata, bytes)) = loaded else {
                continue;
            };
            if !self.valid_prefix(&metadata)
                || (!metadata.continuing()
                    && self
                        .prefix_score(metadata.coverage.iter(), wanted, forced)
                        .is_none())
            {
                continue;
            }
            let started = Instant::now();
            let Some(disk) = &self.database.disk else {
                continue;
            };
            let pages = GraphPages::new(disk.shared_store());
            if pages.validate(&metadata.graph).is_none() {
                continue;
            }
            if let Some(checker) = elaboration::with_graph_store(pages, || {
                PackageChecker::restore(&bytes, |id| self.snapshot.source(&id.0).cloned())
            }) {
                self.database.stats.environment_hits += 1;
                if let Some(disk) = &self.database.disk {
                    disk.store().record_relocation(started.elapsed());
                }
                self.database
                    .package_environments
                    .insert(metadata.key, bytes.into());
                self.database
                    .prefixes
                    .insert(metadata.key, metadata.clone());
                self.progress.environment_reused(score.1.0);
                return (checker, metadata);
            }
        }
        Default::default()
    }

    fn save_prefix(
        &mut self,
        checker: &mut PackageChecker,
        metadata: &mut Metadata,
        request: Fingerprint,
    ) {
        self.progress
            .session_statistics(checker.session_statistics());
        if self.database.disk.is_none() || metadata.coverage.is_empty() || checker.is_pending() {
            return;
        }
        let Some(owner) = self.packages.iter().rposition(|p| {
            metadata
                .coverage
                .iter()
                .any(|path| path.first() == Some(&p.name))
        }) else {
            return;
        };
        metadata.input = self.inputs[owner].key;
        let Ok(key_bytes) = artifact_store::serialize(&(
            metadata.input,
            &metadata.inputs,
            &metadata.syntax,
            &metadata.coverage,
            &metadata.history,
        )) else {
            return;
        };
        metadata.key = crate::cache::fingerprint(&key_bytes);
        if self.database.prefixes.get(&metadata.key).is_some() {
            return;
        }
        checker.prepare_export();
        if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
            eprintln!(
                "prefix saving: {} source modules, {} entries, {} expressions",
                metadata.coverage.len(),
                checker.artifact_entry_count(),
                checker.expression_count()
            );
        }
        let pages = GraphPages::new(self.database.disk.as_ref().unwrap().shared_store());
        let state = match elaboration::with_graph_store(pages.clone(), || checker.checkpoint()) {
            Ok(state) => state,
            Err(error) => {
                self.database.stats.cache_write_failures += 1;
                self.progress.storage_failed(error.to_string());
                return;
            }
        };
        metadata.bytes = state.len();
        metadata.graph = pages.references();
        if let Some(disk) = &self.database.disk {
            let saved = (|| {
                let bytes = artifact_store::serialize(&(*b"REFSES02", &*metadata, &state))?;
                let object = disk.store().write_object(ObjectKind::Checkpoint, &bytes)?;
                let manifest = StoreManifest {
                    key: metadata.key,
                    input: metadata.input,
                    coverage: metadata.coverage.iter().cloned().collect(),
                    environment: Some(object),
                    graph: metadata.graph.clone(),
                    ..Default::default()
                };
                disk.store().publish(&manifest)?;
                // Advance the recovery pointer too: an older in-flight
                // checkpoint must never hide this newer completed prefix.
                disk.store().publish_checkpoint(&StoreManifest {
                    key: request,
                    input: request,
                    ..manifest
                })
            })();
            if let Err(error) = saved {
                self.database.stats.cache_write_failures += 1;
                self.progress.storage_failed(error.to_string());
                return;
            }
        }
        self.database
            .package_environments
            .insert(metadata.key, state.into());
        self.database
            .prefixes
            .insert(metadata.key, metadata.clone());
        self.progress
            .storage_stats(self.database.cache_store_stats());
        self.progress
            .checkpoint_saved(checker.checkpoint_position());
    }

    fn prefix_header(
        &self,
        package: usize,
        roots: &[syntax::Module],
        wanted: &BTreeSet<usize>,
        checker: &mut PackageChecker,
        metadata: &mut Metadata,
    ) -> Option<()> {
        let name = &self.packages[package].name;
        if checker.has_resolution(name)
            && wanted.iter().all(|&index| {
                let path = &self.graph.units[index].path;
                path.first() != Some(name) || metadata.syntax.contains(path)
            })
        {
            return Some(());
        }
        let Some(module) = roots.iter().find(|module| &module.name.0 == name) else {
            return Some(());
        };
        for dependency in &self.inputs[package].dependencies {
            self.prefix_header(dependency.index, roots, wanted, checker, metadata)?;
        }
        let paths = wanted
            .iter()
            .filter_map(|&i| {
                let path = &self.graph.units[i].path;
                (path.first() == Some(name)).then(|| path.clone())
            })
            .collect();
        checker.append_resolution_selected(module, &paths).ok()?;
        metadata
            .inputs
            .insert(name.clone(), self.inputs[package].key);
        metadata.syntax.extend(wanted.iter().filter_map(|&i| {
            let path = &self.graph.units[i].path;
            (path.first() == Some(name)).then(|| path.clone())
        }));
        Some(())
    }

    pub(super) fn ensure_native(
        &mut self,
        index: usize,
        states: &mut [PackageState<'_>],
    ) -> Option<()> {
        // Package result hits can change which state enters this function. Key
        // recovery by the exact whole request, independently of those hits and
        // of broader artifacts selected to satisfy individual packages.
        let request_parts: BTreeSet<_> = states
            .iter()
            .map(|state| {
                crate::package_inputs::artifact_key(
                    &state.input,
                    state
                        .indices
                        .iter()
                        .map(|&i| self.graph.units[i].path.clone()),
                )
            })
            .collect();
        let request = crate::cache::fingerprint(
            &artifact_store::serialize(&(b"session-request", request_parts)).ok()?,
        );
        let wanted = self.graph.closure(
            states
                .iter()
                .flat_map(|state| state.indices.iter().copied()),
        );
        let forced = states
            .iter()
            .filter(|state| state.force && state.results.is_none())
            .flat_map(|state| state.indices.iter().copied())
            .collect();
        self.progress.phase(ProgressPhase::Restoring);
        let (mut checker, mut metadata) = self
            .resume_prefix(request, &forced, &wanted)
            .unwrap_or_else(|| self.restore_prefix(&wanted, &forced));
        metadata.generation = std::env::var("REF_TYPE_CACHE_SESSION").ok();
        let roots = self.graph.roots.to_vec();
        let mut saved_position = checker.checkpoint_position();
        let mut entered_local = false;
        for root in &roots {
            let selected: BTreeSet<_> = wanted
                .iter()
                .copied()
                .filter(|&i| self.graph.units[i].path.first() == Some(&root.name.0))
                .collect();
            if selected.is_empty() {
                continue;
            }
            if selected
                .iter()
                .all(|&i| metadata.coverage.contains(&self.graph.units[i].path))
            {
                for &i in &selected {
                    self.progress.reused(i, Duration::ZERO);
                }
                self.progress.verified(&selected);
                continue;
            }
            let package = self.packages.iter().position(|p| p.name == root.name.0)?;
            if !entered_local && self.local_packages.contains(&root.name.0) {
                // Keep a reusable dependency boundary for local edits and
                // forced local checks, independently of checkpoint spacing.
                self.save_prefix(&mut checker, &mut metadata, request);
                saved_position = checker.checkpoint_position();
                entered_local = true;
            }
            for dependency in &self.inputs[package].dependencies {
                self.prefix_header(
                    dependency.index,
                    &roots,
                    &wanted,
                    &mut checker,
                    &mut metadata,
                )?;
            }
            let paths: BTreeSet<_> = selected
                .iter()
                .map(|&i| self.graph.units[i].path.clone())
                .collect();
            let mut did = BTreeSet::new();
            let mut step_modules = Vec::new();
            let mut remaining = BTreeMap::<usize, usize>::new();
            metadata
                .inputs
                .insert(root.name.0.clone(), self.inputs[package].key);
            metadata.syntax.extend(paths.iter().cloned());
            let interval = self.database.disk.as_ref().map(|_| {
                self.options
                    .checkpoint_interval
                    .unwrap_or(Duration::from_secs(30))
            });
            self.progress.phase(ProgressPhase::Checking);
            let pages = self
                .database
                .disk
                .as_ref()
                .map(|disk| GraphPages::new(disk.shared_store()));
            let mut check = || {
                checker.append_session_selected(root, &paths, interval, |event| match event {
                    PackageProgress::Prepared {
                        paths,
                        start,
                        selected: steps,
                    } => {
                        let order: Vec<_> = paths
                            .iter()
                            .map(|path| {
                                (1..=path.len())
                                    .rev()
                                    .find_map(|length| self.graph.indices.get(&path[..length]))
                                    .copied()
                                    .expect("prefix source module")
                            })
                            .collect();
                        did.extend(steps.iter().map(|&position| order[position]));
                        for &index in &order {
                            if selected.contains(&index) {
                                remaining.entry(index).or_default();
                            }
                        }
                        for &position in &steps {
                            *remaining.entry(order[position]).or_default() += 1;
                        }
                        step_modules = order.clone();
                        self.progress
                            .begin_batch(&order, start, order.len(), &steps);
                    }
                    PackageProgress::Step(elaboration::CheckStepProgress::Started(position)) => {
                        self.progress.start_step(position)
                    }
                    PackageProgress::Step(elaboration::CheckStepProgress::Finished {
                        position,
                        elapsed,
                        success,
                    }) => {
                        self.database.stats.checked_steps += 1;
                        if success {
                            *remaining
                                .get_mut(&step_modules[position])
                                .expect("scheduled declaration") -= 1;
                        }
                        self.progress.step(position, elapsed, success);
                    }
                    PackageProgress::Saving(stats) => {
                        self.database.stats.session = *stats;
                        self.progress
                            .session_statistics(self.database.stats.session.clone());
                        if let Some(pages) = &pages {
                            pages.clear();
                        }
                        self.progress.phase(ProgressPhase::Saving);
                    }
                    // The active request owns recovery even while a dependency
                    // is being checked. resume_prefix looks up this same key.
                    PackageProgress::Checkpoint { steps, bytes } => self.save_pending(
                        request,
                        request,
                        &paths,
                        &metadata,
                        steps,
                        bytes,
                        pages
                            .as_ref()
                            .map_or_else(Vec::new, |pages| pages.references()),
                    ),
                    _ => {}
                })
            };
            let checked = if let Some(pages) = &pages {
                elaboration::with_graph_store(pages.clone(), check)
            } else {
                check()
            };
            self.progress.finish_batch();
            if let Err(error) = checked {
                if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
                    eprintln!("prefix checking failed for {}: {error}", root.name.0);
                }
                let completed: BTreeSet<_> = remaining
                    .iter()
                    .filter_map(|(&i, &left)| (left == 0).then_some(i))
                    .collect();
                metadata
                    .coverage
                    .extend(completed.iter().map(|&i| self.graph.units[i].path.clone()));
                self.progress.verified(&completed);
                self.database.stats.checked_modules += did.len();
                self.database.stats.session = checker.session_statistics();
                let mut results: BTreeMap<_, _> = wanted
                    .iter()
                    .map(|&i| {
                        let path = self.graph.units[i].path.clone();
                        (
                            i,
                            ModuleResult {
                                status: if metadata.coverage.contains(&path) {
                                    ModuleStatus::Verified
                                } else {
                                    ModuleStatus::Incomplete
                                },
                                path,
                                dependencies: self.graph.units[i]
                                    .dependencies
                                    .iter()
                                    .map(|&d| self.graph.units[d].path.clone())
                                    .collect(),
                                ..Default::default()
                            },
                        )
                    })
                    .collect();
                collect_analysis(checker.analysis(), self.graph, &mut results);
                self.failed = Some(Arc::new(SemanticResult {
                    modules: results.into_values().collect(),
                    diagnostics: vec![diagnostic(&error)],
                }));
                return None;
            }
            self.database.stats.checked_modules += did.len();
            for &i in selected.difference(&did) {
                self.progress.reused(i, Duration::ZERO);
                if states[index].indices.contains(&i) {
                    self.database.stats.reused_modules += 1;
                    self.database.stats.restored_modules += 1;
                }
            }
            self.progress.verified(&selected);
            metadata
                .coverage
                .extend(selected.iter().map(|&i| self.graph.units[i].path.clone()));
            metadata.history.push(crate::package_inputs::artifact_key(
                &self.inputs[package].key,
                selected.iter().map(|&i| self.graph.units[i].path.clone()),
            ));
            self.save_covered_results(&checker, &metadata, states);
            self.progress
                .session_statistics(checker.session_statistics());
            // Geometric metadata snapshots bound cumulative prefix encoding by
            // the added work. Immutable graph pages are still appended once;
            // timed in-flight checkpoints provide independent recovery points.
            let position = checker.checkpoint_position();
            if position >= saved_position.max(1).saturating_mul(2) {
                self.save_prefix(&mut checker, &mut metadata, request);
                saved_position = position;
            }
        }
        self.save_covered_results(&checker, &metadata, states);
        self.progress.phase(ProgressPhase::Saving);
        self.save_prefix(&mut checker, &mut metadata, request);
        if let Some(disk) = &self.database.disk {
            let _ = disk.store().discard_checkpoint(&request);
        }
        self.database.stats.session = checker.session_statistics();
        if self.options.collect_statistics {
            self.database
                .verification_statistics
                .extend(checker.statistics().lines());
        }
        self.native_active = Some((checker, metadata));
        Some(())
    }
    fn save_covered_results(
        &mut self,
        checker: &PackageChecker,
        metadata: &Metadata,
        states: &mut [PackageState<'_>],
    ) {
        for state in states {
            if state.results.is_none()
                && state
                    .indices
                    .iter()
                    .all(|&i| metadata.coverage.contains(&self.graph.units[i].path))
            {
                self.save_results(checker, state);
            }
        }
    }

    fn save_results(&mut self, checker: &PackageChecker, state: &mut PackageState<'_>) {
        let own = state.indices.clone();
        let mut fresh: BTreeMap<_, _> = own
            .iter()
            .map(|&i| {
                (
                    i,
                    ModuleResult {
                        path: self.graph.units[i].path.clone(),
                        status: ModuleStatus::Verified,
                        dependencies: self.graph.units[i]
                            .dependencies
                            .iter()
                            .map(|&d| self.graph.units[d].path.clone())
                            .collect(),
                        ..Default::default()
                    },
                )
            })
            .collect();
        collect_analysis(checker.analysis(), self.graph, &mut fresh);
        let results: Vec<_> = fresh.into_values().collect();
        let mut manifest = StoreManifest {
            key: state.key,
            input: state.input,
            coverage: results.iter().map(|r| r.path.clone()).collect(),
            ..Default::default()
        };
        for result in &results {
            let i = self.graph.indices[&result.path];
            self.database
                .checked
                .insert(self.keys[i], Arc::new(result.clone()));
            if let Some(disk) = &self.database.disk {
                if disk.write(&self.keys[i], result).is_err() {
                    self.database.stats.cache_write_failures += 1;
                }
                if let Ok(bytes) = artifact_store::serialize(result)
                    && let Ok(object) = disk.store().write_object(ObjectKind::Result, &bytes)
                {
                    manifest.results.push((result.path.clone(), object));
                }
            }
        }
        if let Some(disk) = &self.database.disk {
            if disk.store().publish(&manifest).is_err() {
                self.database.stats.cache_write_failures += 1;
            } else {
                self.database.stats.package_writes += 1;
                self.database.stats.disk_writes += results.len();
                let _ = disk.store().discard_checkpoint(&state.key);
            }
        }
        self.database.package_results.insert(
            manifest.key,
            MemoryPackage {
                manifest: manifest.clone(),
                results: results.clone(),
            },
        );
        state.manifest = Some(manifest);
        state.results = Some(results);
    }
}
