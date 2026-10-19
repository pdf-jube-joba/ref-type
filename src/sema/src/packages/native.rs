//! Reuse an entire checked prefix without relocating overlapping environments.
use super::*;
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
    bytes: usize,
}

impl PackageRun<'_, '_> {
    fn resume_prefix(
        &mut self,
        state: &PackageState<'_>,
        forced: &BTreeSet<usize>,
        wanted: &BTreeSet<usize>,
    ) -> Option<(PackageChecker, Metadata)> {
        if state.force {
            return None;
        }
        let store = self.database.disk.as_ref()?.store();
        let manifest = store.read_checkpoint(&state.key).ok()?;
        if manifest.input != state.input || manifest.resolver.is_some() {
            return None;
        }
        let bytes = store.read_object(manifest.environment.as_ref()?).ok()?;
        let (magic, metadata, bytes): ([u8; 8], Metadata, Vec<u8>) =
            artifact_store::deserialize(&bytes).ok()?;
        if magic != *b"REFPFX01"
            || !self.valid_prefix(&metadata)
            || metadata.coverage.iter().any(|path| {
                self.graph.indices.get(path).is_none_or(|index| {
                    forced.contains(index)
                        || (self.options.narrow_environment && !wanted.contains(index))
                })
            })
        {
            return None;
        }
        let checker = PackageChecker::restore(&bytes, |id| self.snapshot.source(&id.0).cloned())?;
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
    ) {
        let saved = (|| {
            let store = self.database.disk.as_ref()?.store();
            let bytes = artifact_store::serialize(&(*b"REFPFX01", metadata, bytes.ok()?)).ok()?;
            let environment = store.write_object(ObjectKind::Checkpoint, &bytes).ok()?;
            store
                .publish_checkpoint(&StoreManifest {
                    key,
                    input,
                    coverage: coverage.iter().cloned().collect(),
                    environment: Some(environment),
                    ..Default::default()
                })
                .ok()
        })();
        if saved.is_some() {
            self.database.stats.checkpoint_writes += 1;
            self.progress.checkpoint_saved(steps);
        } else {
            self.database.stats.checkpoint_skips += 1;
        }
        self.progress.phase(ProgressPhase::Checking);
    }

    fn prefix_score(
        &self,
        coverage: impl Iterator<Item = impl AsRef<[String]>>,
        wanted: &BTreeSet<usize>,
        forced: &BTreeSet<usize>,
        small: bool,
    ) -> Option<(usize, std::cmp::Reverse<usize>)> {
        let mut shared = 0;
        let mut extra = 0;
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
        (shared > 0 && (extra == 0 || (small && !self.options.narrow_environment)))
            .then_some((shared, std::cmp::Reverse(extra)))
    }

    fn valid_prefix(&self, metadata: &Metadata) -> bool {
        metadata.inputs.iter().all(|(name, input)| {
            self.packages
                .iter()
                .position(|p| &p.name == name)
                .is_some_and(|i| self.inputs[i].key == *input)
        })
    }

    fn has_syntax(&self, metadata: &Metadata, wanted: &BTreeSet<usize>) -> bool {
        wanted.iter().all(|&index| {
            let path = &self.graph.units[index].path;
            !metadata.inputs.contains_key(&path[0]) || metadata.syntax.contains(path)
        })
    }

    fn restore_prefix(
        &mut self,
        wanted: &BTreeSet<usize>,
        forced: &BTreeSet<usize>,
    ) -> (PackageChecker, Metadata) {
        let active = self.native_active.take().filter(|(_, metadata)| {
            self.valid_prefix(metadata)
                && self.has_syntax(metadata, wanted)
                && self
                    .prefix_score(
                        metadata.coverage.iter(),
                        wanted,
                        forced,
                        metadata.bytes > 0 && metadata.bytes <= 8 * 1024 * 1024,
                    )
                    .is_some()
        });
        let active_score = active.as_ref().and_then(|(_, m)| {
            self.prefix_score(
                m.coverage.iter(),
                wanted,
                forced,
                m.bytes > 0 && m.bytes <= 8 * 1024 * 1024,
            )
        });
        let mut candidates = BTreeMap::new();
        for metadata in self.database.prefixes.values() {
            if self.valid_prefix(metadata)
                && self.has_syntax(metadata, wanted)
                && let Some(score) = self.prefix_score(
                    metadata.coverage.iter(),
                    wanted,
                    forced,
                    metadata.bytes > 0 && metadata.bytes <= 8 * 1024 * 1024,
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
                    if let Some(score) = self.prefix_score(
                        manifest.coverage.iter(),
                        wanted,
                        forced,
                        manifest
                            .environment
                            .as_ref()
                            .is_some_and(|o| o.decoded_bytes <= 8 * 1024 * 1024),
                    ) {
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
            if active_score.is_some_and(|active| active >= score) {
                break;
            }
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
                (magic == *b"REFPFX01" && metadata.key == manifest.key).then_some((metadata, state))
            })();
            let Some((metadata, bytes)) = loaded else {
                continue;
            };
            if !self.valid_prefix(&metadata) || !self.has_syntax(&metadata, wanted) {
                continue;
            }
            let started = Instant::now();
            if let Some(checker) =
                PackageChecker::restore(&bytes, |id| self.snapshot.source(&id.0).cloned())
            {
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
        let active = active.unwrap_or_default();
        if let Some(score) = active_score {
            self.progress.environment_reused(score.1.0);
        }
        active
    }

    fn save_prefix(&mut self, checker: &mut PackageChecker, metadata: &mut Metadata) {
        if metadata.coverage.is_empty() || checker.is_pending() {
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
        let Ok(state) = checker.checkpoint() else {
            return;
        };
        metadata.bytes = state.len();
        if let Some(disk) = &self.database.disk {
            let saved = (|| {
                let bytes = artifact_store::serialize(&(*b"REFPFX01", &*metadata, &state))?;
                let object = disk.store().write_object(ObjectKind::Checkpoint, &bytes)?;
                disk.store().publish(&StoreManifest {
                    key: metadata.key,
                    input: metadata.input,
                    coverage: metadata.coverage.iter().cloned().collect(),
                    environment: Some(object),
                    ..Default::default()
                })
            })();
            if saved.is_err() {
                self.database.stats.cache_write_failures += 1;
            }
        }
        self.database
            .package_environments
            .insert(metadata.key, state.into());
        self.database
            .prefixes
            .insert(metadata.key, metadata.clone());
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
        if checker.has_resolution(name) {
            return Some(());
        }
        let Some(module) = roots.iter().find(|module| &module.name.0 == name) else {
            return Some(());
        };
        for dependency in &self.inputs[package].dependencies {
            self.prefix_header(dependency.index, roots, wanted, checker, metadata)?;
        }
        checker.append_resolution(module).ok()?;
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
        let mut wanted = self.graph.closure(states[index].indices.iter().copied());
        if let Some((_, metadata)) = &self.native_active {
            // Keep the already checked part of this request in the live
            // environment. Rebuilding a narrower dependency selection loses
            // shared declarations between independently selected packages.
            // Coverage outside the request still follows the prefix size and
            // narrow-environment limits below.
            wanted.extend(
                states
                    .iter()
                    .flat_map(|state| state.indices.iter().copied())
                    .filter(|&i| metadata.coverage.contains(&self.graph.units[i].path)),
            );
        }
        let forced = states
            .iter()
            .filter(|state| state.force && state.results.is_none())
            .flat_map(|state| state.indices.iter().copied())
            .collect();
        self.progress.phase(ProgressPhase::Restoring);
        let (mut checker, mut metadata) = self
            .resume_prefix(&states[index], &forced, &wanted)
            .unwrap_or_else(|| self.restore_prefix(&wanted, &forced));
        let own_name = states[index].module.name.0.clone();
        let roots = self.graph.selected(&wanted);
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
            if root.name.0 == own_name {
                self.save_covered_results(&checker, &metadata, states);
                self.save_prefix(&mut checker, &mut metadata);
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
            let checked = checker.append_selected_with_checkpoints(
                root,
                &paths,
                interval,
                |event| match event {
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
                    }) => self.progress.step(position, elapsed, success),
                    PackageProgress::Saving => self.progress.phase(ProgressPhase::Saving),
                    PackageProgress::Checkpoint { steps, bytes } => self.save_pending(
                        states[index].key,
                        states[index].input,
                        &paths,
                        &metadata,
                        steps,
                        bytes,
                    ),
                    _ => {}
                },
            );
            self.progress.finish_batch();
            if let Err(error) = checked {
                if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
                    eprintln!("prefix checking failed for {}: {error}", root.name.0);
                }
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
        }
        self.save_covered_results(&checker, &metadata, states);
        self.progress.phase(ProgressPhase::Saving);
        self.save_prefix(&mut checker, &mut metadata);
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
