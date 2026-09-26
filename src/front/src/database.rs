use crate::{
    cache::{DiskCache, Fingerprint, fingerprint},
    graph::ModuleGraph,
    parsing::{ParseCache, SnapshotLoader},
    *,
};
use elaboration::{
    elaborator::GlobalEnvironment,
    metavariables::{ElaborationError, format_elaboration_error},
};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
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
}

/// Mutable query storage. Results and snapshots can outlive the database.
/// Elaboration workspaces are dropped after each checking batch.
#[derive(Default)]
pub struct Database {
    parses: ParseCache,
    checked: HashMap<Fingerprint, Arc<ModuleResult>>,
    queries: HashMap<Fingerprint, Arc<SemanticResult>>,
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
        self.stats = QueryStats::default();
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
        let mut loader = SnapshotLoader {
            snapshot,
            cache: &mut self.parses,
            stats: &mut self.stats,
            diagnostics: vec![],
        };
        let result = if snapshot.entry().extension().is_some_and(|ext| ext == "ref") {
            front_syntax::module_loader::load_modules(snapshot.entry(), &mut loader)
        } else {
            front_syntax::package_loader::load_package_with(snapshot.entry(), &mut loader)
                .map(|graph| graph.modules)
        };
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
        self.query(snapshot, options, |_| true)
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
        self.stats = QueryStats::default();
        self.verification_statistics.clear();
        let (modules, parse_diagnostics) = match self.load(snapshot) {
            Ok(modules) => modules,
            Err(diagnostics) => {
                return Arc::new(SemanticResult {
                    modules: vec![],
                    diagnostics,
                });
            }
        };
        let graph = ModuleGraph::new(&modules);
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
        let mut settings = format!(
            "{}\n{}\n{}",
            env!("REF_FRONT_REVISION"),
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
        query_bytes.extend(serde_json::to_vec(&diagnostics).expect("diagnostics serialize"));
        let query_key = fingerprint(&query_bytes);
        if !options.force
            && !options.collect_statistics
            && let Some(result) = self.queries.get(&query_key)
        {
            self.stats.reused_modules = result.modules.len();
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
        while !pending.is_empty() {
            let selected = std::mem::take(&mut pending);
            self.stats.checked_modules += selected.len();
            let mut workspace = GlobalEnvironment::default();
            let checked = workspace.add_modules_to_root(&graph.selected(&selected));
            if options.collect_statistics {
                self.verification_statistics = vec![
                    format!("raw nodes: {:?}", workspace.arena().node_counts()),
                    format!("raw caches: {:?}", workspace.crate_env().cache_counts()),
                    format!(
                        "kernel nodes: {:?}",
                        workspace.kernel_env().arena().node_counts()
                    ),
                    format!("kernel caches: {:?}", workspace.kernel_env().cache_counts()),
                    format!(
                        "kernel declaration nodes: {}",
                        workspace.kernel_env().declaration_node_count()
                    ),
                ];
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
            collect_analysis(&workspace, &graph, &mut fresh);
            if let Err(error) = &checked {
                diagnostics.push(diagnostic(&workspace, error));
                if let Some(&failed) = graph.indices.get(&workspace.active_module_path()) {
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
        }
        let result = Arc::new(SemanticResult {
            modules: results
                .into_values()
                .map(|result| result.as_ref().clone())
                .collect(),
            diagnostics,
        });
        self.queries.insert(query_key, result.clone());
        result
    }
}

fn collect_analysis(
    workspace: &GlobalEnvironment,
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
            if !result.references.contains(&reference) {
                result.references.push(reference);
            }
        }
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

fn diagnostic(workspace: &GlobalEnvironment, error: &ElaborationError) -> Diagnostic {
    let (location, error) = match error {
        ElaborationError::Located { location, error } => {
            (Some(Location::from(location)), error.as_ref())
        }
        error => (None, error),
    };
    let goals = match error {
        ElaborationError::UnsolvedGoals(goals) | ElaborationError::AmbiguousImplicit(goals) => {
            goals
                .iter()
                .filter_map(|goal| {
                    let mut location = location.clone()?;
                    location.range = goal.span.start..goal.span.end;
                    Some(Goal {
                        name: goal.display_name(),
                        location,
                        context: elaboration::raw::printing::format_ctx(
                            workspace.crate_env(),
                            &goal.context,
                        ),
                        judgement: goal.principal.as_ref().map(|constraint| {
                            elaboration::metavariables::format_constraint(
                                workspace.crate_env(),
                                constraint,
                            )
                        }),
                        constraints: goal
                            .constraints
                            .iter()
                            .map(|constraint| {
                                elaboration::metavariables::format_constraint_record(
                                    workspace.crate_env(),
                                    constraint,
                                )
                            })
                            .collect(),
                    })
                })
                .collect()
        }
        _ => vec![],
    };
    Diagnostic {
        message: format!(
            "Elaboration Error: {}",
            format_elaboration_error(workspace.crate_env(), error)
        ),
        location,
        goals,
    }
}
