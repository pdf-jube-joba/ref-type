//! Independent package artifacts over the manifest dependency graph.
use super::*;
use crate::artifact_store::{self, ObjectKind, StoreManifest};
use elaboration::{PackageChecker, PackageProgress};

#[path = "packages/native.rs"]
pub(crate) mod native;

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
    results: Option<Vec<ModuleResult>>,
    manifest: Option<StoreManifest>,
    force: bool,
}

struct PackageRun<'a, 'g> {
    database: &'a mut Database,
    snapshot: &'a SourceSnapshot,
    options: &'a CheckOptions,
    graph: &'a ModuleGraph<'g>,
    keys: &'a [Fingerprint],
    progress: &'a mut crate::progress::Reporter,
    native_active: Option<(PackageChecker, native::Metadata)>,
    failed: Option<Arc<SemanticResult>>,
    inputs: &'a [crate::package_inputs::PackageInput],
    packages: &'a [project::package_loader::PackageInfo],
    local_packages: &'a BTreeSet<String>,
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
        let _cost = timing::costs::Scope::enter("query.packages");
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
                results: None,
                manifest: None,
                force,
            };
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
                        if state.manifest.is_none() && state.results.is_none() {
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
            && self
                .session
                .as_ref()
                .is_none_or(|(_, metadata)| !metadata.matches_inputs(&inputs, packages))
            && !options.force
            && !options.force_local
            && states.iter().any(|state| state.results.is_none())
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
        let forced_paths: BTreeSet<_> = states
            .iter()
            .filter(|state| state.force)
            .flat_map(|state| {
                state
                    .indices
                    .iter()
                    .map(|&index| graph.units[index].path.clone())
            })
            .collect();
        let native_active = self
            .session
            .take()
            .filter(|(_, metadata)| metadata.permits(&forced_paths));
        let mut run = PackageRun {
            database: self,
            snapshot,
            options,
            graph,
            keys: module_keys,
            progress,
            native_active,
            failed: None,
            inputs: &inputs,
            packages,
            local_packages,
        };
        let closures: Vec<_> = states
            .iter()
            .map(|state| graph.closure(state.indices.iter().copied()))
            .collect();
        for index in 0..states.len() {
            // A consumer can check its complete dependency selection in one
            // environment. Keep separate requests for independently selected
            // declarations which that consumer would leave unchecked.
            if (index + 1..states.len()).any(|consumer| {
                states[consumer].results.is_none()
                    && states[index].indices.is_subset(&closures[consumer])
            }) {
                continue;
            }
            if states[index].results.is_none() && run.ensure_native(index, &mut states).is_none() {
                if let Some(result) = run.failed.take() {
                    return Some(result);
                }
                if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
                    eprintln!(
                        "package checking unavailable: {}",
                        states[index].module.name.0
                    );
                }
                return None;
            }
        }
        run.database.session = run.native_active.take();
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
    let objects: Vec<_> = manifest
        .results
        .iter()
        .filter(|(path, _)| coverage.contains(path))
        .map(|(_, object)| object)
        .collect();
    let results: Option<Vec<ModuleResult>> = disk.store().read_values(&objects).ok();
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
