//! Independent package artifacts over the manifest dependency graph.
use super::*;
use crate::artifact_store::{self, ObjectKind, StoreManifest};
use elaboration::{ArtifactCatalog, PackageArtifact, PackageChecker, PackageProgress};

#[derive(Clone)]
pub(crate) struct MemoryPackage {
    manifest: StoreManifest,
    results: Vec<ModuleResult>,
}
struct PackageState<'a> {
    module: &'a syntax::Module,
    input: Fingerprint,
    key: Fingerprint,
    indices: BTreeSet<usize>,
    dependencies: Vec<usize>,
    partials: Vec<Fingerprint>,
    results: Option<Vec<ModuleResult>>,
    artifact: Option<PackageArtifact>,
    manifest: Option<StoreManifest>,
    force: bool,
    tried_disk_environment: bool,
}

struct PackageRun<'a, 'g> {
    database: &'a mut Database,
    snapshot: &'a SourceSnapshot,
    options: &'a CheckOptions,
    graph: &'a ModuleGraph<'g>,
    keys: &'a [Fingerprint],
    valid_inputs: BTreeSet<Fingerprint>,
    progress: &'a mut crate::progress::Reporter,
}

impl PackageRun<'_, '_> {
    fn closure(states: &[PackageState<'_>], index: usize) -> BTreeSet<usize> {
        let mut result = BTreeSet::new();
        let mut pending = states[index].dependencies.clone();
        while let Some(i) = pending.pop() {
            if result.insert(i) {
                pending.extend(&states[i].dependencies);
            }
        }
        result
    }

    fn load_environment(&mut self, state: &mut PackageState<'_>) {
        if state.tried_disk_environment || state.force {
            return;
        }
        state.tried_disk_environment = true;
        state.artifact = self.memory_environment(&state.key);
        if state.artifact.is_some() {
            return;
        }
        if let Some((disk, manifest)) = self.database.disk.as_ref().zip(state.manifest.as_ref()) {
            state.artifact = (|| {
                Some(PackageArtifact {
                    resolver: disk.store().read_object(manifest.resolver.as_ref()?).ok()?,
                    environment: disk
                        .store()
                        .read_object(manifest.environment.as_ref()?)
                        .ok()?,
                })
            })();
        }
    }

    fn memory_environment(&self, key: &Fingerprint) -> Option<PackageArtifact> {
        let bytes = self.database.package_environments.get(key)?;
        artifact_store::deserialize(&artifact_store::decode_memory(&bytes).ok()?).ok()
    }

    fn import_saved(
        &mut self,
        key: Fingerprint,
        states: &[PackageState<'_>],
        checker: &mut PackageChecker,
        catalog: &mut ArtifactCatalog,
        visiting: &mut BTreeSet<Fingerprint>,
        transactional: bool,
    ) -> Option<()> {
        if catalog.contains(&key) {
            return Some(());
        }
        if !visiting.insert(key) {
            return None;
        }
        // Pin persisted dependencies even when their bytes are already in memory.
        let persisted = self
            .database
            .disk
            .as_ref()
            .and_then(|disk| disk.store().read_manifest(&key).ok());
        let current = states.iter().find(|state| state.key == key);
        let memory = self.database.package_results.get(&key).cloned();
        let manifest = current
            .and_then(|state| state.manifest.clone())
            .or_else(|| memory.as_ref().map(|saved| saved.manifest.clone()))
            .or(persisted)?;
        if !self.valid_inputs.contains(&manifest.input) {
            return None;
        }
        for dependency in manifest.dependencies {
            self.import_saved(
                dependency,
                states,
                checker,
                catalog,
                visiting,
                transactional,
            )?;
        }
        let cached = current.and_then(|state| state.artifact.as_ref());
        let loaded = if cached.is_none() {
            self.memory_environment(&key).or_else(|| {
                let store = self.database.disk.as_ref()?.store();
                Some(PackageArtifact {
                    resolver: store.read_object(manifest.resolver.as_ref()?).ok()?,
                    environment: store.read_object(manifest.environment.as_ref()?).ok()?,
                })
            })
        } else {
            None
        };
        let artifact = cached.or(loaded.as_ref())?;
        let started = std::time::Instant::now();
        let imported = if transactional {
            checker.import_artifact(artifact, catalog, |id| self.snapshot.source(&id.0).cloned())
        } else {
            std::mem::take(checker)
                .import_artifact_owned(artifact, std::mem::take(catalog), |id| {
                    self.snapshot.source(&id.0).cloned()
                })
                .map(|(imported, identities)| {
                    *checker = imported;
                    *catalog = identities;
                })
        };
        if let Some(disk) = &self.database.disk {
            disk.store().record_relocation(started.elapsed());
        }
        if let Err(error) = imported {
            if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
                eprintln!("package import failed: {error}");
            }
            return None;
        }
        self.database.stats.environment_hits += 1;
        visiting.remove(&key);
        Some(())
    }

    fn release_environment(&self, state: &mut PackageState<'_>) {
        let persisted = self.database.disk.is_some()
            && state
                .manifest
                .as_ref()
                .is_some_and(|manifest| manifest.environment.is_some());
        if persisted || self.database.package_environments.get(&state.key).is_some() {
            state.artifact = None;
            state.tried_disk_environment = false;
        }
    }

    fn ensure(&mut self, index: usize, states: &mut [PackageState<'_>]) -> Option<()> {
        self.load_environment(&mut states[index]);
        if states[index].artifact.is_some() {
            return Some(());
        }
        // A broader saved coverage can supply results, but a rebuild publishes
        // precisely the syntax selected by this request.
        states[index].key = crate::package_inputs::artifact_key(
            &states[index].input,
            states[index]
                .indices
                .iter()
                .map(|&i| self.graph.units[i].path.clone()),
        );
        let dependencies = Self::closure(states, index);
        let mut checker = PackageChecker::default();
        let mut catalog = ArtifactCatalog::default();
        // A damaged environment is rebuilt once from its own current inputs.
        for attempt in 0..2 {
            let mut failed = None;
            for &dependency in &dependencies {
                self.ensure(dependency, states)?;
                if self
                    .import_saved(
                        states[dependency].key,
                        states,
                        &mut checker,
                        &mut catalog,
                        &mut BTreeSet::new(),
                        false,
                    )
                    .is_none()
                {
                    failed = Some(dependency);
                    break;
                }
                self.release_environment(&mut states[dependency]);
            }
            match failed {
                None => break,
                Some(dependency) if attempt == 0 => {
                    states[dependency].artifact = None;
                    states[dependency].tried_disk_environment = true;
                    self.ensure(dependency, states)?;
                    checker = PackageChecker::default();
                    catalog = ArtifactCatalog::default();
                }
                Some(_) => return None,
            }
        }
        let boundary = checker.artifact_boundary();
        if !states[index].force {
            for partial in states[index].partials.clone() {
                let _ = self.import_saved(
                    partial,
                    states,
                    &mut checker,
                    &mut catalog,
                    &mut BTreeSet::new(),
                    true,
                );
            }
        }
        let key = states[index].key;
        let input = states[index].input;
        let indices = states[index].indices.clone();
        let dependency_keys = dependencies
            .iter()
            .map(|&i| states[i].key)
            .collect::<Vec<_>>();
        let coverage = indices
            .iter()
            .map(|&i| self.graph.units[i].path.clone())
            .collect::<Vec<_>>();
        if !states[index].force {
            let resume = self.database.disk.as_ref().and_then(|disk| {
                let manifest = disk.store().read_checkpoint(&key).ok()?;
                Some(PackageArtifact {
                    resolver: disk.store().read_object(manifest.resolver.as_ref()?).ok()?,
                    environment: disk
                        .store()
                        .read_object(manifest.environment.as_ref()?)
                        .ok()?,
                })
            });
            if let Some(resume) = resume
                && checker
                    .import_resume(&resume, &mut catalog, |id| {
                        self.snapshot.source(&id.0).cloned()
                    })
                    .is_ok()
            {
                self.database.stats.checkpoint_hits += 1;
            }
        }
        let mut reused = BTreeSet::new();
        let interval = self.database.disk.as_ref().map(|_| {
            self.options
                .checkpoint_interval
                .unwrap_or(std::time::Duration::from_secs(30))
        });
        self.progress.phase(ProgressPhase::Resolving);
        let checked = checker.append_selected_with_artifact_checkpoints(
            states[index].module,
            &coverage.iter().cloned().collect(),
            interval,
            key,
            input,
            &boundary,
            &mut catalog,
            |event| match event {
                PackageProgress::Prepared {
                    paths,
                    start,
                    selected,
                } => {
                    let steps: Vec<_> = paths
                        .iter()
                        .map(|path| {
                            (1..=path.len())
                                .rev()
                                .find_map(|length| self.graph.indices.get(&path[..length]))
                                .copied()
                                .expect("package source scope")
                        })
                        .collect();
                    let remaining: BTreeSet<_> =
                        selected.iter().map(|&position| steps[position]).collect();
                    reused = steps
                        .iter()
                        .copied()
                        .filter(|i| indices.contains(i) && !remaining.contains(i))
                        .collect();
                    self.database.stats.reused_modules += reused.len();
                    self.database.stats.restored_modules += reused.len();
                    self.progress
                        .begin_batch(&steps, start, steps.len(), &selected);
                    self.progress.phase(ProgressPhase::Checking);
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
                PackageProgress::Checkpoint { .. } => {}
                PackageProgress::ArtifactCheckpoint { steps, artifact } => {
                    let saved = (|| {
                        let disk = self.database.disk.as_ref()?;
                        let artifact = artifact
                            .map_err(|error| {
                                disk.store()
                                    .record_export_failure(format!("checkpoint export: {error}"));
                            })
                            .ok()?;
                        let dependencies = artifact
                            .dependencies()
                            .map_err(|error| {
                                disk.store().record_export_failure(format!(
                                    "checkpoint dependencies: {error}"
                                ));
                            })
                            .ok()?;
                        let resolver = disk
                            .store()
                            .write_object(ObjectKind::Resolver, &artifact.resolver)
                            .ok()?;
                        let environment = disk
                            .store()
                            .write_object(ObjectKind::Checkpoint, &artifact.environment)
                            .ok()?;
                        disk.store()
                            .publish_checkpoint(&StoreManifest {
                                key,
                                input,
                                coverage: coverage.clone(),
                                dependencies,
                                resolver: Some(resolver),
                                environment: Some(environment),
                                ..Default::default()
                            })
                            .ok()?;
                        Some(())
                    })();
                    if saved.is_some() {
                        self.database.stats.checkpoint_writes += 1;
                        self.progress.checkpoint_saved(steps);
                    } else {
                        self.database.stats.checkpoint_skips += 1;
                    }
                    self.progress.phase(ProgressPhase::Checking);
                }
            },
        );
        self.progress.finish_batch();
        if checked.is_err() {
            return None;
        }
        self.database.stats.checked_modules += indices.len() - reused.len();
        self.progress.verified(&indices);
        let mut fresh: BTreeMap<_, _> = indices
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
        for (&i, result) in &fresh {
            self.database
                .checked
                .insert(self.keys[i], Arc::new(result.clone()));
            if let Some(disk) = &self.database.disk
                && disk.write(&self.keys[i], result).is_err()
            {
                self.database.stats.cache_write_failures += 1;
            }
        }
        let results = fresh.into_values().collect::<Vec<_>>();
        self.progress.phase(ProgressPhase::Saving);
        let artifact = checker
            .export_artifact_for_input(key, input, &boundary, &mut catalog)
            .map_err(|error| {
                if let Some(disk) = &self.database.disk {
                    disk.store().record_export_failure(&error);
                }
                if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
                    eprintln!("package export skipped: {error}");
                }
            })
            .ok();
        drop(checker);
        drop(catalog);
        drop(boundary);
        if artifact.is_none() {
            self.database.stats.package_skips += 1;
        }
        let mut manifest = StoreManifest {
            key,
            input,
            coverage,
            dependencies: artifact
                .as_ref()
                .and_then(|artifact| artifact.dependencies().ok())
                .unwrap_or(dependency_keys),
            ..Default::default()
        };
        if let Some(disk) = &self.database.disk {
            let saved = (|| -> Result<(), crate::error::CacheError> {
                for result in &results {
                    let object = disk
                        .store()
                        .write_object(ObjectKind::Result, &artifact_store::serialize(result)?)?;
                    manifest.results.push((result.path.clone(), object));
                }
                if let Some(artifact) = &artifact {
                    // Results remain useful when an environment exceeds the object budget.
                    if let (Ok(resolver), Ok(environment)) = (
                        disk.store()
                            .write_object(ObjectKind::Resolver, &artifact.resolver),
                        disk.store()
                            .write_object(ObjectKind::Environment, &artifact.environment),
                    ) {
                        manifest.resolver = Some(resolver);
                        manifest.environment = Some(environment);
                    }
                }
                disk.store().publish(&manifest)?;
                if manifest.environment.is_some() {
                    disk.store().discard_checkpoint(&key)?;
                }
                Ok(())
            })();
            if saved.is_ok() {
                self.database.stats.package_writes += 1;
                self.database.stats.disk_writes += results.len();
            } else {
                self.database.stats.cache_write_failures += 1;
            }
        }
        self.database.package_results.insert(
            key,
            MemoryPackage {
                manifest: manifest.clone(),
                results: results.clone(),
            },
        );
        if let Some(artifact) = &artifact
            && let Ok(bytes) = artifact_store::serialize(artifact)
                .and_then(|bytes| artifact_store::encode_memory(&bytes))
        {
            self.database.package_environments.insert(key, bytes.into());
        }
        states[index].results = Some(results);
        states[index].artifact = artifact;
        states[index].manifest = Some(manifest);
        states[index].tried_disk_environment = true;
        Some(())
    }
}

impl Database {
    pub(super) fn check_packages(
        &mut self,
        snapshot: &SourceSnapshot,
        options: &CheckOptions,
        graph: &ModuleGraph<'_>,
        requested: &BTreeSet<usize>,
        packages: &[project::package_loader::PackageInfo],
        local_packages: &BTreeSet<String>,
        module_keys: &[Fingerprint],
        progress: &mut crate::progress::Reporter,
    ) -> Option<Arc<SemanticResult>> {
        let modules: Vec<_> = graph
            .roots
            .iter()
            .filter(|module| {
                requested
                    .iter()
                    .any(|&i| graph.units[i].path.first() == Some(&module.name.0))
            })
            .collect();
        let inputs = crate::package_inputs::inputs(snapshot, packages, &options.configuration);
        let by_name: HashMap<_, _> = packages
            .iter()
            .enumerate()
            .map(|(i, p)| (p.name.as_str(), i))
            .collect();
        let selected: HashMap<_, _> = modules
            .iter()
            .enumerate()
            .map(|(i, m)| (m.name.0.as_str(), i))
            .collect();
        let mut states = Vec::new();
        for module in &modules {
            let package = *by_name.get(module.name.0.as_str())?;
            let input = inputs[package].key;
            if let Some(disk) = &self.disk {
                let instance = crate::cache::fingerprint(
                    inputs[package].instance.0.as_os_str().as_encoded_bytes(),
                );
                if disk.store().observe_input(&instance, &input).is_err() {
                    self.stats.cache_write_failures += 1;
                }
            }
            let indices: BTreeSet<_> = requested
                .iter()
                .copied()
                .filter(|&i| graph.units[i].path[0] == module.name.0)
                .collect();
            let coverage = indices
                .iter()
                .map(|&i| graph.units[i].path.clone())
                .collect::<Vec<_>>();
            let key = crate::package_inputs::artifact_key(&input, coverage.clone());
            let force =
                options.force || (options.force_local && local_packages.contains(&module.name.0));
            let mut state = PackageState {
                module,
                input,
                key,
                indices,
                dependencies: Vec::new(),
                partials: Vec::new(),
                results: None,
                artifact: None,
                manifest: None,
                force,
                tried_disk_environment: false,
            };
            let mut pending = inputs[package]
                .dependencies
                .iter()
                .map(|d| d.index)
                .collect::<Vec<_>>();
            let mut all = BTreeSet::new();
            while let Some(p) = pending.pop() {
                if all.insert(p) {
                    pending.extend(inputs[p].dependencies.iter().map(|d| d.index));
                }
            }
            state.dependencies = all
                .iter()
                .filter_map(|&p| selected.get(packages[p].name.as_str()).copied())
                .collect();
            if !force {
                let mut available = BTreeMap::new();
                let memory = self.package_results.get(&key).or_else(|| {
                    self.package_results.values().find(|saved| {
                        saved.manifest.input == input
                            && coverage
                                .iter()
                                .all(|path| saved.manifest.coverage.contains(path))
                    })
                });
                if let Some(memory) = memory {
                    state.results = Some(
                        memory
                            .results
                            .iter()
                            .filter(|result| coverage.contains(&result.path))
                            .cloned()
                            .collect(),
                    );
                    state.key = memory.manifest.key;
                    state.manifest = Some(memory.manifest.clone());
                }
                if state.results.is_none() {
                    state.results = indices_for_results(&state.indices, module_keys, graph, self);
                }
                if state.results.is_none()
                    && let Some(disk) = &self.disk
                    && let Some(manifest) = disk
                        .store()
                        .read_manifest(&key)
                        .ok()
                        .filter(|manifest| manifest.input == input)
                    && let Some(saved) = read_results(disk, &manifest, &coverage)
                {
                    self.stats.disk_hits += saved.len();
                    state.results = Some(saved);
                    state.manifest = Some(manifest);
                }
                if state.manifest.is_none() {
                    if state.results.is_none() {
                        for saved in self
                            .package_results
                            .values()
                            .filter(|saved| saved.manifest.input == input)
                        {
                            available.extend(
                                saved
                                    .results
                                    .iter()
                                    .filter(|result| {
                                        result.status == ModuleStatus::Verified
                                            && coverage.contains(&result.path)
                                    })
                                    .map(|result| (result.path.clone(), result.clone())),
                            );
                        }
                    }
                    state.partials = self
                        .package_results
                        .values()
                        .filter(|saved| {
                            saved.manifest.input == input
                                && saved
                                    .manifest
                                    .coverage
                                    .iter()
                                    .all(|path| coverage.contains(path))
                        })
                        .map(|saved| saved.manifest.key)
                        .collect();
                    if let Some(disk) = &self.disk {
                        let candidates = disk.store().list_matching(&input).unwrap_or_default();
                        if state.results.is_none() {
                            for manifest in &candidates {
                                if let Some(saved) = read_results(disk, manifest, &coverage) {
                                    self.stats.disk_hits += saved.len();
                                    state.results = Some(saved);
                                    state.key = manifest.key;
                                    state.manifest = Some(manifest.clone());
                                    break;
                                }
                            }
                        }
                        if state.manifest.is_none() {
                            state.partials.extend(
                                candidates
                                    .iter()
                                    .filter(|manifest| {
                                        manifest.coverage.iter().all(|path| coverage.contains(path))
                                    })
                                    .map(|manifest| manifest.key),
                            );
                            if state.results.is_none() {
                                for manifest in candidates {
                                    let missing: Vec<_> = coverage
                                        .iter()
                                        .filter(|path| {
                                            manifest.coverage.contains(path)
                                                && !available.contains_key(*path)
                                        })
                                        .cloned()
                                        .collect();
                                    if let Some(saved) = read_results(disk, &manifest, &missing) {
                                        self.stats.disk_hits += saved.len();
                                        available.extend(
                                            saved
                                                .into_iter()
                                                .map(|result| (result.path.clone(), result)),
                                        );
                                    }
                                }
                            }
                        }
                    }
                    state.partials.sort();
                    state.partials.dedup();
                }
                if state.results.is_none() {
                    // Workers can publish individual verified modules without a
                    // complete package manifest. Exhaust result-only reuse before
                    // importing any environment to continue checking this package.
                    state.results = complete_module_results(
                        &state.indices,
                        module_keys,
                        graph,
                        self,
                        available,
                    );
                }
            }
            if let Some(saved) = &state.results {
                self.stats.package_hits += 1;
                self.stats.reused_modules += saved.len();
                for &i in &state.indices {
                    progress.reused(i, std::time::Duration::ZERO);
                }
            }
            states.push(state);
        }
        // The module checkpoint path handles edits within a single package,
        // retaining its unaffected module results and checking-order prefixes.
        if packages.len() == 1
            && !options.force
            && !options.force_local
            && states.iter().any(|state| state.results.is_none())
            && states.iter().all(|state| state.partials.is_empty())
            && requested.iter().any(|&i| {
                self.checked.get(&module_keys[i]).is_some()
                    || self
                        .disk
                        .as_ref()
                        .and_then(|disk| disk.read(&module_keys[i]))
                        .is_some()
            })
        {
            return None;
        }
        progress.skip_cached();
        let mut run = PackageRun {
            database: self,
            snapshot,
            options,
            graph,
            keys: module_keys,
            valid_inputs: inputs.iter().map(|input| input.key).collect(),
            progress,
        };
        for index in 0..states.len() {
            if states[index].results.is_none() {
                run.ensure(index, &mut states)?;
                run.release_environment(&mut states[index]);
            }
        }
        let mut results = BTreeMap::new();
        for state in states {
            for mut result in state.results? {
                let index = *graph.indices.get(&result.path)?;
                result.dependencies = graph.units[index]
                    .dependencies
                    .iter()
                    .map(|&d| graph.units[d].path.clone())
                    .collect();
                results.insert(index, result);
            }
        }
        self.stats.environment_bytes =
            self.environments.bytes() + self.package_environments.bytes();
        Some(Arc::new(SemanticResult {
            modules: results.into_values().collect(),
            diagnostics: Vec::new(),
        }))
    }
}

fn indices_for_results(
    indices: &BTreeSet<usize>,
    keys: &[Fingerprint],
    graph: &ModuleGraph<'_>,
    database: &Database,
) -> Option<Vec<ModuleResult>> {
    indices
        .iter()
        .map(|&index| {
            database
                .checked
                .get(&keys[index])
                .filter(|result| result.path == graph.units[index].path)
                .map(|result| result.as_ref().clone())
        })
        .collect::<Option<Vec<_>>>()
        .filter(|results| {
            results
                .iter()
                .all(|result| result.status == ModuleStatus::Verified)
        })
}

fn complete_module_results(
    indices: &BTreeSet<usize>,
    keys: &[Fingerprint],
    graph: &ModuleGraph<'_>,
    database: &mut Database,
    mut available: BTreeMap<Vec<String>, ModuleResult>,
) -> Option<Vec<ModuleResult>> {
    for &index in indices {
        let path = &graph.units[index].path;
        if available.contains_key(path) {
            continue;
        }
        let valid =
            |result: &ModuleResult| result.status == ModuleStatus::Verified && &result.path == path;
        let result = database
            .checked
            .get(&keys[index])
            .filter(|result| valid(result))
            .map(|result| result.as_ref().clone())
            .or_else(|| {
                let result = database.disk.as_ref()?.read(&keys[index])?;
                if !valid(&result) {
                    return None;
                }
                database.stats.disk_hits += 1;
                database
                    .checked
                    .insert(keys[index], Arc::new(result.clone()));
                Some(result)
            });
        if let Some(result) = result {
            available.insert(path.clone(), result);
        }
    }
    indices
        .iter()
        .map(|&index| available.remove(&graph.units[index].path))
        .collect()
}

fn read_results(
    disk: &crate::cache::DiskCache,
    manifest: &StoreManifest,
    coverage: &[Vec<String>],
) -> Option<Vec<ModuleResult>> {
    if !coverage.iter().all(|path| manifest.coverage.contains(path)) {
        return None;
    }
    let results: Option<Vec<ModuleResult>> = manifest
        .results
        .iter()
        .filter(|(path, _)| coverage.contains(path))
        .map(|(_, object)| {
            artifact_store::deserialize(&disk.store().read_object(object).ok()?).ok()
        })
        .collect();
    results.filter(|results| {
        results.len() == coverage.len()
            && results
                .iter()
                .all(|result| result.status == ModuleStatus::Verified)
            && coverage
                .iter()
                .all(|path| results.iter().any(|result| &result.path == path))
    })
}
