use crate::{
    cache::{DiskCache, Fingerprint, fingerprint},
    environment::{EnvironmentCache, EnvironmentPlan},
    graph::ModuleGraph,
    parsing::{ParseCache, SnapshotLoader},
    *,
};
use diagnostics::DiagnosticError;
use elaboration::Checker;
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    path::{Path, PathBuf},
    sync::Arc,
};

#[derive(Clone, Debug, Default)]
pub struct CheckOptions {
    /// Included in cache identities for clients with additional checking settings.
    pub configuration: String,
    /// Run verification even when a checked result exists (e.g. tracing).
    pub force: bool,
    /// One-shot checking can rebuild independent prefixes after errors instead
    /// of serializing recovery environments during every successful check.
    pub skip_environment_cache: bool,
    /// Rebuild precisely the requested environment after a broader prefix exceeded resources.
    pub narrow_environment: bool,
    /// Recheck entry packages (including workspace members), reusing dependency checkpoints.
    pub force_local: bool,
    /// Select only the named module and its dependencies, excluding unrelated children.
    pub module_only: bool,
    /// Receive source module timings after analysis and result storage finish.
    pub progress: Option<fn(&ModuleProgress)>,
    /// Receive the selected dependency graph and live verification progress.
    pub progress_events: Option<fn(&ProgressEvent)>,
    pub collect_statistics: bool,
    pub diagnostics: elaboration::DiagnosticMode,
    /// Minimum work time between module-boundary package checkpoints (default 30s).
    pub checkpoint_interval: Option<std::time::Duration>,
}

struct LoadedProject {
    modules: Vec<syntax::Module>,
    diagnostics: Vec<Diagnostic>,
    package_info: Vec<project::package_loader::PackageInfo>,
    local_packages: BTreeSet<String>,
}

/// Mutable query storage. Results and snapshots can outlive the database.
/// Checked environments are retained as detached, serializable checkpoints.
#[derive(Default)]
pub struct Database {
    sources: std::cell::RefCell<project::SourceCache>,
    parses: ParseCache,
    checked: crate::memory::GenerationCache<Fingerprint, Arc<ModuleResult>>,
    queries: crate::memory::GenerationCache<Fingerprint, Arc<SemanticResult>>,
    environments: EnvironmentCache,
    package_environments: EnvironmentCache,
    package_results: crate::memory::GenerationCache<Fingerprint, packages::MemoryPackage>,
    prefixes: crate::memory::GenerationCache<Fingerprint, packages::native::Metadata>,
    disk: Option<DiskCache>,
    stats: QueryStats,
    verification_statistics: Vec<String>,
}

impl Database {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn with_cache(directory: impl Into<PathBuf>) -> Self {
        Self {
            disk: Some(DiskCache::new(directory.into())),
            ..Self::default()
        }
    }
    pub fn read_snapshot(
        &self,
        entry: impl AsRef<Path>,
        _reuse_dependency_sources: bool,
    ) -> Result<SourceSnapshot, project::Error> {
        let _cost = timing::costs::Scope::enter("source.snapshot");
        SourceSnapshot::read_with_source_cache(entry, &mut self.sources.borrow_mut())
    }
    pub fn stats(&self) -> &QueryStats {
        &self.stats
    }
    pub fn set_cache_budget(&mut self, bytes: u64) {
        if let Some(disk) = &self.disk {
            disk.set_budget(bytes);
        }
    }
    pub fn cache_store_stats(&self) -> crate::artifact_store::CacheStoreStats {
        self.disk
            .as_ref()
            .map(|disk| disk.store().stats())
            .unwrap_or_default()
    }
    pub fn verification_statistics(&self) -> &[String] {
        &self.verification_statistics
    }
    pub fn memory_cache_stats(&self) -> crate::MemoryCacheStats {
        crate::MemoryCacheStats {
            source_entries: self.sources.borrow().len(),
            source_bytes: self.sources.borrow().bytes(),
            parse_entries: self.parses.len(),
            parse_source_bytes: self.parses.source_bytes(),
            module_results: self.checked.len(),
            query_results: self.queries.len(),
            package_results: self.package_results.len(),
            compressed_environment_bytes: self.environments.bytes()
                + self.package_environments.bytes(),
        }
    }
    pub fn clear_memory(&mut self) {
        self.sources.get_mut().clear();
        self.parses.clear();
        self.checked.clear();
        self.queries.clear();
        self.environments.clear();
        self.package_environments.clear();
        self.package_results.clear();
        self.prefixes.clear();
    }

    pub fn parse(
        &mut self,
        snapshot: &SourceSnapshot,
        file: impl AsRef<Path>,
        kind: ParseKind,
    ) -> Arc<ParseResult> {
        self.parses.next_generation();
        self.parses
            .parse(snapshot, file.as_ref(), kind, &mut self.stats)
    }

    /// Load and parse the complete source graph, without elaborating terms.
    pub fn parse_project(
        &mut self,
        snapshot: &SourceSnapshot,
    ) -> Result<Vec<syntax::Module>, Vec<Diagnostic>> {
        self.parses.next_generation();
        self.stats = QueryStats {
            environment_bytes: self.environments.bytes() + self.package_environments.bytes(),
            ..QueryStats::default()
        };
        let LoadedProject {
            modules,
            diagnostics,
            ..
        } = self.load(snapshot)?;
        if diagnostics.is_empty() {
            Ok(modules)
        } else {
            Err(diagnostics)
        }
    }

    /// Source module identities, including repeated names, for bounded checking batches.
    pub fn module_paths(
        &mut self,
        snapshot: &SourceSnapshot,
    ) -> Result<Vec<Vec<String>>, Vec<Diagnostic>> {
        let modules = self.parse_project(snapshot)?;
        Ok(ModuleGraph::structure(&modules)
            .units
            .into_iter()
            .map(|unit| unit.path)
            .collect())
    }

    fn load(&mut self, snapshot: &SourceSnapshot) -> Result<LoadedProject, Vec<Diagnostic>> {
        let _cost = timing::costs::Scope::enter("source.load");
        let started = std::time::Instant::now();
        let mut loader = SnapshotLoader {
            snapshot,
            cache: &mut self.parses,
            stats: &mut self.stats,
            diagnostics: vec![],
        };
        let result = if snapshot.entry().extension().is_some_and(|ext| ext == "ref") {
            ::project::module_loader::load_modules(snapshot.entry(), &mut loader)
                .map(|modules| (modules, BTreeSet::new(), Vec::new()))
        } else {
            ::project::package_loader::load_package_with(snapshot.entry(), &mut loader).map(
                |graph| {
                    (
                        graph.modules,
                        graph
                            .entry_packages
                            .iter()
                            .map(|id| graph.packages[id.0].name.clone())
                            .collect(),
                        graph.packages,
                    )
                },
            )
        };
        if std::env::var_os("REF_TYPE_PROFILE_MODULES").is_some() {
            eprintln!(
                "modules phase=load elapsed_us={} parsed={} cache_hits={}",
                started.elapsed().as_micros(),
                loader.stats.parsed_files,
                loader.stats.reused_parses
            );
        }
        match result {
            Ok((modules, local_packages, package_info)) => Ok(LoadedProject {
                modules,
                diagnostics: loader.diagnostics,
                package_info,
                local_packages,
            }),
            Err(message) if loader.diagnostics.is_empty() => Err(vec![Diagnostic {
                cause: message.diagnostic_data(),
                message: format!("Module Load Error: {message}"),
                location: None,
                goals: vec![],
            }]),
            Err(_) => Err(loader.diagnostics),
        }
    }

    pub fn check(&mut self, snapshot: &SourceSnapshot) -> Arc<SemanticResult> {
        self.check_with_options(snapshot, &CheckOptions::default())
    }
    pub fn check_with_options(
        &mut self,
        snapshot: &SourceSnapshot,
        options: &CheckOptions,
    ) -> Arc<SemanticResult> {
        elaboration::diagnostics::with_diagnostic_mode(options.diagnostics, || {
            self.query(snapshot, options, true, |_| true)
        })
    }
    /// Check the named module and the scopes/imports on which it depends.
    pub fn module(&mut self, snapshot: &SourceSnapshot, path: &[String]) -> Arc<SemanticResult> {
        self.query(snapshot, &CheckOptions::default(), false, |unit| {
            unit.path == path
        })
    }
    /// Check a named module and its children with the settings of a whole project.
    pub fn module_with_options(
        &mut self,
        snapshot: &SourceSnapshot,
        path: &[String],
        options: &CheckOptions,
    ) -> Arc<SemanticResult> {
        elaboration::diagnostics::with_diagnostic_mode(options.diagnostics, || {
            self.query(snapshot, options, false, |unit| {
                unit.path == path || (!options.module_only && unit.path.starts_with(path))
            })
        })
    }
    /// All modules with declarations in the requested file and their dependencies.
    pub fn file(
        &mut self,
        snapshot: &SourceSnapshot,
        path: impl AsRef<Path>,
    ) -> Arc<SemanticResult> {
        let file = snapshot.identity(path.as_ref());
        self.query(snapshot, &CheckOptions::default(), false, |unit| {
            unit.module
                .source
                .as_ref()
                .is_some_and(|source| source.id.0 == file)
        })
    }
    pub fn declaration(
        &mut self,
        snapshot: &SourceSnapshot,
        id: &DeclarationId,
    ) -> Option<Declaration> {
        self.module(snapshot, &id.module).declaration(id).cloned()
    }

    fn query(
        &mut self,
        snapshot: &SourceSnapshot,
        options: &CheckOptions,
        complete: bool,
        select: impl Fn(&crate::graph::Unit<'_>) -> bool,
    ) -> Arc<SemanticResult> {
        self.parses.next_generation();
        self.checked.next_generation();
        self.queries.next_generation();
        self.package_results.next_generation();
        self.prefixes.next_generation();
        let _cost_session = timing::costs::Session::start();
        let _cost = timing::costs::Scope::enter("query.total");
        let _timing = timing::Session::start(options.progress.is_some());
        self.stats = QueryStats {
            environment_bytes: self.environments.bytes() + self.package_environments.bytes(),
            ..QueryStats::default()
        };
        if let Some(disk) = &self.disk
            && disk.store().release_pins().is_err()
        {
            self.stats.cache_write_failures += 1;
        }
        let _phase = elaboration::profiling::Phase::start("query.total");
        self.verification_statistics.clear();
        let notify = |event| {
            if let Some(receive) = options.progress_events {
                receive(&event);
            }
        };
        notify(ProgressEvent::Phase(ProgressPhase::Loading));
        let compact = options.diagnostics == elaboration::DiagnosticMode::Compact;
        // A complete snapshot includes manifests, source identities and contents.
        // Its verified result can be read without reconstructing the syntax graph.
        let complete_key = (complete && self.disk.is_some())
            .then(|| crate::cache::snapshot_key(snapshot, &options.configuration, compact));
        if let Some(key) = complete_key
            && !options.force
            && !options.force_local
            && !options.collect_statistics
        {
            let cached = self
                .queries
                .get(&key)
                .filter(|r| r.is_success())
                .cloned()
                .or_else(|| {
                    let result = self.disk.as_ref()?.read_query(&key)?;
                    self.stats.disk_hits += result.modules.len();
                    Some(Arc::new(result))
                });
            if let Some(result) = cached {
                self.stats.reused_modules = result.modules.len();
                if !snapshot.entry().extension().is_some_and(|ext| ext == "ref") {
                    self.stats.package_hits =
                        result.modules.iter().filter(|m| m.path.len() == 1).count();
                }
                crate::progress::reused_result(snapshot, &result, options);
                self.queries.insert(key, result.clone());
                return result;
            }
        }
        let LoadedProject {
            modules,
            diagnostics: parse_diagnostics,
            package_info,
            local_packages,
        } = match self.load(snapshot) {
            Ok(modules) => modules,
            Err(mut diagnostics) => {
                if compact {
                    diagnostics.truncate(1);
                }
                notify(ProgressEvent::Finished { success: false });
                return Arc::new(SemanticResult {
                    modules: vec![],
                    diagnostics,
                });
            }
        };
        let source_roots: Vec<_> = package_info
            .iter()
            .map(|package| package.directory.clone())
            .collect();
        let _source_roots = ::syntax::source_reference::package_roots_guard(&source_roots);
        notify(ProgressEvent::Phase(ProgressPhase::Planning));
        let graph = {
            let _phase = elaboration::profiling::Phase::start("query.graph");
            let _cost = timing::costs::Scope::enter("query.graph");
            ModuleGraph::new(&modules)
        };
        let package_input = !snapshot.entry().extension().is_some_and(|ext| ext == "ref");
        let forced = |index: usize| {
            options.force
                || options.collect_statistics
                || (options.force_local
                    && (!package_input || local_packages.contains(&graph.units[index].path[0])))
        };
        let requested = graph.closure(
            graph
                .units
                .iter()
                .enumerate()
                .filter_map(|(index, unit)| select(unit).then_some(index)),
        );
        let invalid: BTreeSet<_> = graph
            .units
            .iter()
            .enumerate()
            .filter_map(|(index, unit)| {
                parse_diagnostics
                    .iter()
                    .any(|diagnostic| {
                        diagnostic.location.as_ref().is_some_and(|location| {
                            unit.module
                                .source
                                .as_ref()
                                .is_some_and(|source| source.id.0 == location.file)
                        })
                    })
                    .then_some(index)
            })
            .collect();
        let blocked: BTreeSet<_> = requested
            .iter()
            .copied()
            .filter(|&index| !invalid.is_empty() && !graph.closure([index]).is_disjoint(&invalid))
            .collect();
        let mut diagnostics: Vec<_> = parse_diagnostics
            .into_iter()
            .filter(|diagnostic| {
                diagnostic.location.as_ref().is_none_or(|location| {
                    requested.iter().any(|&index| {
                        graph.units[index]
                            .module
                            .source
                            .as_ref()
                            .is_some_and(|source| source.id.0 == location.file)
                    })
                })
            })
            .collect();
        let mut progress = crate::progress::Reporter::new(
            &graph,
            &requested,
            package_input,
            options.progress,
            options.progress_events,
        );
        if compact && !diagnostics.is_empty() {
            diagnostics.truncate(1);
            return Arc::new(SemanticResult {
                modules: vec![],
                diagnostics,
            });
        }
        let mut settings = format!(
            "{}\n{}\n{}",
            env!("REF_SEMA_REVISION"),
            snapshot.entry().display(),
            options.configuration
        )
        .into_bytes();
        for (path, _) in snapshot
            .files()
            .filter(|(path, _)| path.file_name().is_some_and(|name| name == "ref.toml"))
        {
            settings.extend(path.to_string_lossy().as_bytes());
            settings.extend(snapshot.content_digest(path).expect("captured manifest"));
        }
        let settings = fingerprint(&settings);
        progress.phase(ProgressPhase::Cache);
        let keys: Vec<_> = (0..graph.units.len())
            .map(|index| graph.key(index, &settings))
            .collect();
        let mut query_bytes = Vec::new();
        for &index in &requested {
            query_bytes.extend(keys[index]);
        }
        query_bytes.push(u8::from(compact));
        query_bytes.extend(serde_json::to_vec(&diagnostics).expect("diagnostics serialize"));
        let query_key = complete_key.unwrap_or_else(|| fingerprint(&query_bytes));
        if !options.force
            && !options.force_local
            && !options.collect_statistics
            && let Some(result) = self.queries.get(&query_key)
        {
            // Keep this query's module entries hot across repeated query-level hits.
            for index in &requested {
                let _ = self.checked.get(&keys[*index]);
            }
            self.stats.reused_modules = result.modules.len();
            self.stats.environment_bytes =
                self.environments.bytes() + self.package_environments.bytes();
            if result.is_success() {
                progress.skip_all();
            } else {
                for module in &result.modules {
                    if module.status == ModuleStatus::Verified {
                        progress.reused(graph.indices[&module.path], std::time::Duration::ZERO);
                    }
                }
                progress.skip_cached();
            }
            progress.finish(result.is_success());
            return result.clone();
        }
        if package_input
            && !(options.force && self.disk.is_none())
            && (package_info.len() > 1 || requested.len() == graph.units.len())
            && diagnostics.is_empty()
            && !options.collect_statistics
            && let Some(result) = self.check_packages(
                snapshot,
                options,
                &graph,
                &requested,
                &package_info,
                &local_packages,
                &keys,
                &mut progress,
            )
        {
            self.save_complete_result(complete_key, &result);
            self.queries.insert(query_key, result.clone());
            progress.finish(result.is_success());
            return result;
        }
        let mut results = BTreeMap::new();
        let mut misses = BTreeSet::new();
        for &index in &requested {
            let _time = timing::Scope::module(|| graph.units[index].path.clone());
            if blocked.contains(&index) {
                continue;
            }
            let started = std::time::Instant::now();
            let cached = if forced(index) {
                None
            } else {
                self.checked.get(&keys[index]).cloned().or_else(|| {
                    let result = self.disk.as_ref()?.read(&keys[index])?;
                    if result.path != graph.units[index].path {
                        return None;
                    }
                    self.stats.disk_hits += 1;
                    let result = Arc::new(result);
                    self.checked.insert(keys[index], result.clone());
                    Some(result)
                })
            };
            if let Some(result) = cached {
                progress.reused(index, started.elapsed());
                self.stats.reused_modules += 1;
                results.insert(index, result);
            } else {
                misses.insert(index);
            }
        }
        let mut pending = graph.closure(misses.iter().copied());
        let mut recovering = false;
        let mut recovery_environments = EnvironmentCache::default();
        let mut full_resolution = None;
        let mut full_plan = None;
        while !pending.is_empty() {
            let selected = std::mem::take(&mut pending);
            let mut workspace = Checker::default();
            // Keep the complete requested layout stable across edits. A failed
            // resolution still uses the smaller batch for independent recovery.
            let available = requested.difference(&blocked).copied().collect();
            let profile_modules = std::env::var_os("REF_TYPE_PROFILE_MODULES").is_some();
            if profile_modules {
                eprintln!(
                    "modules phase=check retry={recovering} selected={selected:?} environment={settings:?}"
                );
            }
            progress.phase(ProgressPhase::Resolving);
            let full = full_resolution.get_or_insert_with(|| {
                let _phase = elaboration::profiling::Phase::start("query.resolve");
                let _cost = timing::costs::Scope::enter("query.resolve");
                resolve::resolve(&graph.selected(&available))
            });
            let fallback;
            let resolved = match &*full {
                Ok(project) => Ok(project),
                Err(_) => {
                    let _phase = elaboration::profiling::Phase::start("query.resolve-recovery");
                    let _cost = timing::costs::Scope::enter("query.resolve-recovery");
                    fallback = resolve::resolve(&graph.selected(&selected));
                    fallback.as_ref()
                }
            };
            let mut saved = EnvironmentCache::default();
            let check_phase = elaboration::profiling::Phase::start("query.check-batch");
            let check_cost = timing::costs::Scope::enter("query.check-batch");
            let checked = match &resolved {
                Ok(project) => {
                    progress.phase(ProgressPhase::Planning);
                    let cache_environments = !((compact || options.skip_environment_cache)
                        && (options.force || options.collect_statistics)
                        && self.disk.is_none());
                    let environment_settings = cache_environments.then_some(&settings);
                    let fallback_plan;
                    let plan = if full.is_ok() {
                        full_plan.get_or_insert_with(|| {
                            EnvironmentPlan::new(project, &graph, environment_settings)
                        })
                    } else {
                        fallback_plan = EnvironmentPlan::new(project, &graph, environment_settings);
                        &fallback_plan
                    };
                    let end = plan.end(&selected);
                    let first_forced = plan
                        .steps
                        .iter()
                        .position(|&index| forced(index))
                        .unwrap_or(end);
                    progress.phase(ProgressPhase::Restoring);
                    let mut start = 0;
                    if recovering || (!options.force && !options.collect_statistics) {
                        for &(position, key) in plan
                            .checkpoints
                            .iter()
                            .rev()
                            .filter(|(position, _)| *position <= end)
                        {
                            let bytes = recovery_environments
                                .get(&key)
                                .or_else(|| {
                                    if options.force
                                        || options.collect_statistics
                                        || position > first_forced
                                    {
                                        return None;
                                    }
                                    self.environments.get(&key)
                                })
                                .or_else(|| {
                                    if options.force
                                        || options.collect_statistics
                                        || position > first_forced
                                    {
                                        return None;
                                    }
                                    let bytes: Arc<[u8]> =
                                        self.disk.as_ref()?.read_environment(&key)?.into();
                                    self.environments.insert(key, bytes.clone());
                                    Some(bytes)
                                });
                            if profile_modules {
                                eprintln!(
                                    "modules phase=restore position={position} cache_hit={} environment={key:?}",
                                    bytes.is_some()
                                );
                            }
                            if bytes.is_some()
                                && std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some()
                            {
                                eprintln!("restoring environment at {position}");
                            }
                            if let Some(restored) =
                                bytes.as_deref().and_then(Checker::restore_environment)
                            {
                                workspace = restored;
                                start = position;
                                if recovering {
                                    self.stats.recovery_environment_hits += 1;
                                } else {
                                    self.stats.environment_hits += 1;
                                }
                                break;
                            }
                        }
                    }
                    let selected_steps: BTreeSet<_> = (start..end)
                        .filter(|&position| selected.contains(&plan.steps[position]))
                        .collect();
                    let checked: BTreeSet<_> = selected_steps
                        .iter()
                        .map(|&position| plan.steps[position])
                        .collect();
                    self.stats.checked_modules += checked.len();
                    self.stats.restored_modules += plan.steps[..start]
                        .iter()
                        .copied()
                        .collect::<BTreeSet<_>>()
                        .difference(&checked)
                        .count();
                    let checkpoints = plan.save_points();
                    progress.begin_batch(&plan.steps, start, end, &selected_steps);
                    progress.phase(ProgressPhase::Checking);
                    let checked = workspace.check_range_with_progress(
                        project,
                        start,
                        end,
                        &selected_steps,
                        &checkpoints,
                        |position, bytes| match bytes {
                            Ok(bytes) => {
                                let key = plan
                                    .checkpoints
                                    .iter()
                                    .find(|(step, _)| *step == position)
                                    .unwrap()
                                    .1;
                                if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
                                    eprintln!(
                                        "environment checkpoint {position}: {} bytes",
                                        bytes.len()
                                    );
                                }
                                saved.insert(key, bytes.into());
                            }
                            Err(_) => self.stats.environment_skips += 1,
                        },
                        |event| match event {
                            elaboration::CheckStepProgress::Started(position) => {
                                progress.start_step(position)
                            }
                            elaboration::CheckStepProgress::Finished {
                                position,
                                elapsed,
                                success,
                            } => progress.step(position, elapsed, success),
                        },
                    );
                    progress.finish_batch();
                    checked
                }
                Err(error) => {
                    self.stats.checked_modules += selected.len();
                    Err(elaboration::Diagnostic::resolution((*error).clone()))
                }
            };
            drop(check_cost);
            drop(check_phase);
            if checked.is_ok() {
                progress.verified(&selected);
            }
            progress.phase(ProgressPhase::Saving);
            recovering = true;
            for (key, bytes) in saved.into_entries() {
                recovery_environments.insert(key, bytes.clone());
                if checked.is_ok()
                    && !((options.force || options.collect_statistics) && self.disk.is_none())
                {
                    if let Some(disk) = &self.disk {
                        match disk.write_environment(&key, &bytes) {
                            Ok(()) => self.stats.environment_writes += 1,
                            Err(_) => self.stats.cache_write_failures += 1,
                        }
                    }
                    self.environments.insert(key, bytes);
                }
            }
            if options.collect_statistics {
                self.verification_statistics = workspace.statistics().lines();
            }
            let mut fresh: BTreeMap<_, _> = selected
                .iter()
                .map(|&index| {
                    (
                        index,
                        ModuleResult {
                            path: graph.units[index].path.clone(),
                            status: if checked.is_ok() {
                                ModuleStatus::Verified
                            } else {
                                ModuleStatus::Incomplete
                            },
                            dependencies: graph.units[index]
                                .dependencies
                                .iter()
                                .map(|&dependency| graph.units[dependency].path.clone())
                                .collect(),
                            ..ModuleResult::default()
                        },
                    )
                })
                .collect();
            {
                let _phase = elaboration::profiling::Phase::start("query.collect-analysis");
                let _cost = timing::costs::Scope::enter("query.collect-analysis");
                collect_analysis(workspace.analysis(), &graph, &mut fresh);
            }
            if let Err(error) = &checked {
                diagnostics.push(diagnostic(error));
                if !compact
                    && let Some(&failed) = graph.indices.get(&resolved.as_ref().err().map_or_else(
                        || workspace.active_module_path(),
                        |error| error.module.clone(),
                    ))
                {
                    // Continue independent scopes in a fresh workspace after an error.
                    pending = selected
                        .iter()
                        .copied()
                        .filter(|&index| !graph.closure([index]).contains(&failed))
                        .collect();
                }
            }
            for (index, result) in fresh {
                let _time = timing::Scope::module(|| graph.units[index].path.clone());
                let result = Arc::new(result);
                // Only batches accepted by the kernel produce persistent records.
                if checked.is_ok() {
                    self.checked.insert(keys[index], result.clone());
                    if let Some(disk) = &self.disk {
                        match disk.write(&keys[index], &result) {
                            Ok(()) => self.stats.disk_writes += 1,
                            Err(_) => self.stats.cache_write_failures += 1,
                        }
                    }
                }
                if requested.contains(&index) {
                    results.insert(index, result);
                }
            }
            let _phase = elaboration::profiling::Phase::start("query.drop-workspace");
            let _cost = timing::costs::Scope::enter("query.drop-workspace");
            drop(workspace);
        }
        let result = Arc::new(SemanticResult {
            modules: results
                .into_values()
                .map(|result| {
                    let _time = timing::Scope::module(|| result.path.clone());
                    result.as_ref().clone()
                })
                .collect(),
            diagnostics,
        });
        self.stats.environment_bytes =
            self.environments.bytes() + self.package_environments.bytes();
        progress.skip_cached();
        progress.phase(ProgressPhase::Saving);
        self.save_complete_result(complete_key, &result);
        self.queries.insert(query_key, result.clone());
        progress.finish(result.is_success());
        result
    }

    fn save_complete_result(&mut self, key: Option<Fingerprint>, result: &SemanticResult) {
        if result.is_success()
            && let Some((key, disk)) = key.zip(self.disk.as_ref())
        {
            match disk.write_query(&key, result) {
                Ok(()) => self.stats.disk_writes += 1,
                Err(_) => self.stats.cache_write_failures += 1,
            }
        }
    }
}

fn collect_analysis(
    analysis: &elaboration::analysis::Analysis,
    graph: &ModuleGraph<'_>,
    results: &mut BTreeMap<usize, ModuleResult>,
) {
    let _cost = timing::costs::Scope::enter("query.collect-analysis");
    for declaration in &analysis.declarations {
        let _time = timing::Scope::module(|| declaration.module.clone());
        if let Some(result) = graph
            .indices
            .get(&declaration.module)
            .and_then(|index| results.get_mut(index))
        {
            result.declarations.push(Declaration {
                id: DeclarationId {
                    module: declaration.module.clone(),
                    name: declaration.name.clone(),
                },
                kind: declaration.kind.into(),
                location: (&declaration.location).into(),
                ty: declaration.ty.clone(),
            });
        }
    }
    for reference in &analysis.references {
        let _time = timing::Scope::module(|| reference.module.clone());
        if let Some(result) = graph
            .indices
            .get(&reference.module)
            .and_then(|index| results.get_mut(index))
        {
            let reference = Reference {
                location: (&reference.location).into(),
                target: DeclarationId {
                    module: reference.target_module.clone(),
                    name: reference.target_name.clone(),
                },
            };
            result.references.push(reference);
        }
    }
    for result in results.values_mut() {
        let _time = timing::Scope::module(|| result.path.clone());
        let mut seen = HashSet::new();
        result
            .references
            .retain(|reference| seen.insert(reference.clone()));
    }
    for output in &analysis.outputs {
        let _time = timing::Scope::module(|| output.module.clone());
        if let Some(result) = graph
            .indices
            .get(&output.module)
            .and_then(|index| results.get_mut(index))
        {
            result.outputs.push(QueryOutput {
                location: (&output.location).into(),
                text: output.text.clone(),
            });
        }
    }
}

fn diagnostic(error: &elaboration::Diagnostic) -> Diagnostic {
    Diagnostic {
        cause: error.diagnostic_data(),
        message: error.message.clone(),
        location: error.location.as_ref().map(Location::from),
        goals: error
            .goals
            .iter()
            .filter_map(|goal| {
                Some(Goal {
                    name: goal.name.clone(),
                    location: Location::from(goal.location.as_ref()?),
                    context: goal.context.clone(),
                    judgement: goal.judgement.clone(),
                    constraints: goal.constraints.clone(),
                    state: goal.state.clone(),
                    solution: goal.solution.clone(),
                    occurrences: goal.occurrences.iter().map(Location::from).collect(),
                })
            })
            .collect(),
    }
}

#[path = "packages.rs"]
pub(crate) mod packages;
