use crate::{
    cache::{DiskCache, Fingerprint, fingerprint},
    environment::{EnvironmentCache, EnvironmentPlan},
    graph::ModuleGraph,
    parsing::{ParseCache, SnapshotLoader},
    *,
};
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
    pub collect_statistics: bool,
    pub diagnostics: elaboration::DiagnosticMode,
}

/// Mutable query storage. Results and snapshots can outlive the database.
/// Checked environments are retained as detached, serializable checkpoints.
#[derive(Default)]
pub struct Database {
    parses: ParseCache,
    checked: HashMap<Fingerprint, Arc<ModuleResult>>,
    queries: HashMap<Fingerprint, Arc<SemanticResult>>,
    environments: EnvironmentCache,
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
    pub fn stats(&self) -> &QueryStats {
        &self.stats
    }
    pub fn verification_statistics(&self) -> &[String] {
        &self.verification_statistics
    }
    pub fn clear_memory(&mut self) {
        self.parses.clear();
        self.checked.clear();
        self.queries.clear();
        self.environments.clear();
    }

    pub fn parse(
        &mut self,
        snapshot: &SourceSnapshot,
        file: impl AsRef<Path>,
        kind: ParseKind,
    ) -> Arc<ParseResult> {
        self.parses
            .parse(snapshot, file.as_ref(), kind, &mut self.stats)
    }

    /// Load and parse the complete source graph, without elaborating terms.
    pub fn parse_project(
        &mut self,
        snapshot: &SourceSnapshot,
    ) -> Result<Vec<syntax::Module>, Vec<Diagnostic>> {
        self.stats = QueryStats {
            environment_bytes: self.environments.bytes(),
            ..QueryStats::default()
        };
        let (modules, diagnostics) = self.load(snapshot)?;
        if diagnostics.is_empty() {
            Ok(modules)
        } else {
            Err(diagnostics)
        }
    }

    fn load(
        &mut self,
        snapshot: &SourceSnapshot,
    ) -> Result<(Vec<syntax::Module>, Vec<Diagnostic>), Vec<Diagnostic>> {
        let started = std::time::Instant::now();
        let mut loader = SnapshotLoader {
            snapshot,
            cache: &mut self.parses,
            stats: &mut self.stats,
            diagnostics: vec![],
        };
        let result = if snapshot.entry().extension().is_some_and(|ext| ext == "ref") {
            ::project::module_loader::load_modules(snapshot.entry(), &mut loader)
        } else {
            ::project::package_loader::load_package_with(snapshot.entry(), &mut loader)
                .map(|graph| graph.modules)
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
            Ok(modules) => Ok((modules, loader.diagnostics)),
            Err(message) if loader.diagnostics.is_empty() => Err(vec![Diagnostic {
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
            self.query(snapshot, options, |_| true)
        })
    }
    /// Check the named module and the scopes/imports on which it depends.
    pub fn module(&mut self, snapshot: &SourceSnapshot, path: &[String]) -> Arc<SemanticResult> {
        self.query(snapshot, &CheckOptions::default(), |unit| unit.path == path)
    }
    /// All modules with declarations in the requested file and their dependencies.
    pub fn file(
        &mut self,
        snapshot: &SourceSnapshot,
        path: impl AsRef<Path>,
    ) -> Arc<SemanticResult> {
        let file = snapshot.identity(path.as_ref());
        self.query(snapshot, &CheckOptions::default(), |unit| {
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
        select: impl Fn(&crate::graph::Unit<'_>) -> bool,
    ) -> Arc<SemanticResult> {
        self.stats = QueryStats {
            environment_bytes: self.environments.bytes(),
            ..QueryStats::default()
        };
        let _phase = elaboration::profiling::Phase::start("query.total");
        self.verification_statistics.clear();
        let compact = options.diagnostics == elaboration::DiagnosticMode::Compact;
        let (modules, parse_diagnostics) = match self.load(snapshot) {
            Ok(modules) => modules,
            Err(mut diagnostics) => {
                if compact {
                    diagnostics.truncate(1);
                }
                return Arc::new(SemanticResult {
                    modules: vec![],
                    diagnostics,
                });
            }
        };
        let graph = {
            let _phase = elaboration::profiling::Phase::start("query.graph");
            ModuleGraph::new(&modules)
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
            .filter(|&index| !graph.closure([index]).is_disjoint(&invalid))
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
        for (path, source) in snapshot
            .files()
            .filter(|(path, _)| path.file_name().is_some_and(|name| name == "ref.toml"))
        {
            settings.extend(path.to_string_lossy().as_bytes());
            settings.extend(fingerprint(source.text.as_bytes()));
        }
        let settings = fingerprint(&settings);
        let keys: Vec<_> = (0..graph.units.len())
            .map(|index| graph.key(index, &settings))
            .collect();
        let mut query_bytes = Vec::new();
        for &index in &requested {
            query_bytes.extend(keys[index]);
        }
        query_bytes.push(u8::from(compact));
        query_bytes.extend(serde_json::to_vec(&diagnostics).expect("diagnostics serialize"));
        let query_key = fingerprint(&query_bytes);
        if !options.force
            && !options.collect_statistics
            && let Some(result) = self.queries.get(&query_key)
        {
            self.stats.reused_modules = result.modules.len();
            self.stats.environment_bytes = self.environments.bytes();
            return result.clone();
        }
        let mut results = BTreeMap::new();
        let mut misses = BTreeSet::new();
        for &index in &requested {
            if blocked.contains(&index) {
                continue;
            }
            let cached = if options.force || options.collect_statistics {
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
            let full = full_resolution.get_or_insert_with(|| {
                let _phase = elaboration::profiling::Phase::start("query.resolve");
                resolve::resolve(&graph.selected(&available))
            });
            let fallback;
            let resolved = match &*full {
                Ok(project) => Ok(project),
                Err(_) => {
                    let _phase = elaboration::profiling::Phase::start("query.resolve-recovery");
                    fallback = resolve::resolve(&graph.selected(&selected));
                    fallback.as_ref()
                }
            };
            let mut saved = EnvironmentCache::default();
            let check_phase = elaboration::profiling::Phase::start("query.check-batch");
            let checked = match &resolved {
                Ok(project) => {
                    let fallback_plan;
                    let plan = if full.is_ok() {
                        full_plan
                            .get_or_insert_with(|| EnvironmentPlan::new(project, &graph, &settings))
                    } else {
                        fallback_plan = EnvironmentPlan::new(project, &graph, &settings);
                        &fallback_plan
                    };
                    let end = plan.end(&selected);
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
                                    if options.force || options.collect_statistics {
                                        return None;
                                    }
                                    self.environments.get(&key)
                                })
                                .or_else(|| {
                                    if options.force || options.collect_statistics {
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
                    let checkpoints = if compact
                        && (options.force || options.collect_statistics)
                        && self.disk.is_none()
                    {
                        BTreeSet::new()
                    } else {
                        plan.save_points()
                    };
                    workspace.check_range(
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
                    )
                }
                Err(error) => {
                    self.stats.checked_modules += selected.len();
                    Err(elaboration::Diagnostic {
                        message: format!("Resolution Error: {}", error.message),
                        location: error.location.clone(),
                        goals: Vec::new(),
                    })
                }
            };
            drop(check_phase);
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
                collect_analysis(&workspace, &graph, &mut fresh);
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
            drop(workspace);
        }
        let result = Arc::new(SemanticResult {
            modules: results
                .into_values()
                .map(|result| result.as_ref().clone())
                .collect(),
            diagnostics,
        });
        self.stats.environment_bytes = self.environments.bytes();
        self.queries.insert(query_key, result.clone());
        result
    }
}

fn collect_analysis(
    workspace: &Checker,
    graph: &ModuleGraph<'_>,
    results: &mut BTreeMap<usize, ModuleResult>,
) {
    for declaration in &workspace.analysis().declarations {
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
    for reference in &workspace.analysis().references {
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
        let mut seen = HashSet::new();
        result
            .references
            .retain(|reference| seen.insert(reference.clone()));
    }
    for output in &workspace.analysis().outputs {
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
