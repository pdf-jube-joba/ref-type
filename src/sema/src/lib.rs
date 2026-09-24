//! Common semantic entry point for batch and interactive consumers.
mod artifact;
mod diagnostics;
pub use artifact::{CheckedArtifact, KernelArtifact};
mod edits;
mod goals;
mod outline;
mod references;
pub use references::{Occurrence, ReferenceResult, SemanticRef};
mod packages;
mod source;
mod tree;
pub use diagnostics::{Diagnostic, DiagnosticReport, Severity, SourceOrigin};
pub use edits::{EditError, EditProposal, TextEdit};
pub use goals::{DisplayJudgement, GoalId, GoalSnapshot};
pub use outline::{ItemId, ItemKey, ItemKind, ItemVersion, OutlineItem};
pub use packages::{Package, PackageGraph, PackageId};
pub use source::{FileId, FileSnapshot, Location, RevisionId, SourceDatabase};

use crate::{
    elaborator::GlobalEnvironment,
    metavariables::{ElaborationError, format_elaboration_error},
    parse::ParsedSource,
};
use std::{
    cell::{OnceCell, RefCell},
    path::{Path, PathBuf},
    rc::Rc,
    sync::Arc,
};
use tree::ModuleTree;

pub struct AnalysisHost {
    sources: SourceDatabase,
    root: PathBuf,
    identities: Rc<RefCell<outline::ItemInterner>>,
    current: RefCell<Option<AnalysisSnapshot>>,
}

impl AnalysisHost {
    pub fn new(root: impl AsRef<Path>) -> std::io::Result<Self> {
        let sources = SourceDatabase::new(std::env::current_dir()?)?;
        let mut root = sources.absolute_path(root.as_ref());
        if root.is_dir() {
            root = root.join("ref.toml");
        } else if root.file_name().is_some_and(|name| name == "root.ref")
            && root
                .parent()
                .and_then(Path::file_name)
                .is_some_and(|name| name == "src")
            && let Some(parent) = root.parent().and_then(Path::parent)
            && parent.join("ref.toml").is_file()
        {
            root = parent.join("ref.toml");
        }
        Ok(Self {
            sources,
            root,
            identities: Rc::default(),
            current: RefCell::default(),
        })
    }

    pub fn sources(&self) -> &SourceDatabase {
        &self.sources
    }
    pub fn sources_mut(&mut self) -> &mut SourceDatabase {
        &mut self.sources
    }

    /// Refresh the reachable disk tree, retaining open buffers. Missing files
    /// are explicit VFS inputs, so later snapshots cannot accidentally read them.
    pub fn refresh_disk(&mut self) {
        let tree = ModuleTree::load(&self.root, |path| {
            let text = std::fs::read_to_string(path).ok();
            let identity = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
            let id = self.sources.set_disk_identity(path, text, identity);
            self.sources
                .file(id)
                .ok_or_else(|| format!("failed to read source file at {}", path.display()))
        });
        if self
            .current
            .borrow()
            .as_ref()
            .is_none_or(|snapshot| snapshot.revision() != self.sources.revision())
        {
            self.fresh_snapshot(OnceCell::from(tree));
        }
    }

    pub fn snapshot(&self) -> AnalysisSnapshot {
        if let Some(snapshot) = self.current.borrow().as_ref()
            && snapshot.revision() == self.sources.revision()
        {
            return snapshot.clone();
        }
        self.fresh_snapshot(OnceCell::new())
    }

    fn fresh_snapshot(&self, tree: OnceCell<ModuleTree>) -> AnalysisSnapshot {
        let snapshot = AnalysisSnapshot(Rc::new(SnapshotData {
            sources: self.sources.clone(),
            root: self.root.clone(),
            tree,
            outline: OnceCell::new(),
            source_map: OnceCell::new(),
            check: OnceCell::new(),
        }));
        // Assign identities in input order while the previous snapshot is still
        // current. Later query order cannot change declaration correspondence.
        let outline = self.identities.borrow_mut().outline(snapshot.tree());
        snapshot.0.outline.set(outline).unwrap();
        *self.current.borrow_mut() = Some(snapshot.clone());
        snapshot
    }
}

struct SnapshotData {
    sources: SourceDatabase,
    root: PathBuf,
    tree: OnceCell<ModuleTree>,
    outline: OnceCell<Vec<OutlineItem>>,
    source_map: OnceCell<syntax::SourceMap>,
    check: OnceCell<CheckResult>,
}

/// Immutable inputs and memoized, snapshot-owned query results.
/// This first implementation uses one analysis worker and rebuilds the checker.
#[derive(Clone)]
pub struct AnalysisSnapshot(Rc<SnapshotData>);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckStatus {
    Checked,
    Incomplete,
    Failed,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ItemCheckStatus {
    Checked,
    Incomplete,
    Failed,
    Blocked { dependencies: Vec<ItemId> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ItemCheck {
    pub item: ItemId,
    pub status: ItemCheckStatus,
}

#[derive(Debug, Clone)]
pub struct CheckResult {
    pub revision: RevisionId,
    pub status: CheckStatus,
    pub diagnostics: Vec<Diagnostic>,
    pub outputs: Vec<String>,
    pub statistics: Vec<String>,
    pub goals: Vec<GoalSnapshot>,
    pub items: Vec<ItemCheck>,
    pub occurrences: Vec<Occurrence>,
    pub artifacts: Vec<CheckedArtifact>,
}

impl AnalysisSnapshot {
    pub fn packages(&self) -> &PackageGraph {
        &self.tree().packages
    }
    pub fn revision(&self) -> RevisionId {
        self.0.sources.revision()
    }
    pub fn sources(&self) -> &SourceDatabase {
        &self.0.sources
    }

    fn tree(&self) -> &ModuleTree {
        self.0.tree.get_or_init(|| {
            ModuleTree::load(&self.0.root, |path| {
                self.0
                    .sources
                    .file_id(path)
                    .and_then(|id| self.0.sources.file(id))
                    .ok_or_else(|| format!("failed to read source file at {}", path.display()))
            })
        })
    }

    pub fn parse(&self, file: FileId) -> Option<Arc<ParsedSource>> {
        if let Some(parsed) = self.tree().parsed.get(&file) {
            return Some(parsed.clone());
        }
        let file = self.0.sources.file(file)?;
        Some(Arc::new(crate::parse::parse_source_recovering(
            &file.source.text,
            file.source.id.0 == self.0.root,
        )))
    }

    pub fn outline(&self) -> &[OutlineItem] {
        self.0.outline.get().expect("snapshot outline initialized")
    }

    /// Resolve an AST occurrence in this snapshot's reachable module tree.
    pub fn ast_location(&self, id: syntax::AstId) -> Option<Location> {
        let map = self.0.source_map.get_or_init(|| {
            let mut map = syntax::SourceMap::default();
            for module in &self.tree().modules {
                map.insert_module(module);
            }
            map
        });
        let location = map.location(id)?;
        let file = self.sources().file_id(&location.source.id.0)?;
        Some(self.sources().file(file)?.location(location.span))
    }

    pub fn parse_diagnostics(&self) -> DiagnosticReport {
        DiagnosticReport {
            revision: self.revision(),
            diagnostics: self.tree().diagnostics.clone(),
        }
    }

    pub fn modules(&self) -> Result<Vec<crate::syntax::Module>, DiagnosticReport> {
        if self.tree().diagnostics.is_empty() {
            Ok(self.tree().modules.clone())
        } else {
            Err(self.parse_diagnostics())
        }
    }

    pub fn diagnostics(&self, file: FileId) -> DiagnosticReport {
        DiagnosticReport {
            revision: self.revision(),
            diagnostics: self
                .check()
                .diagnostics
                .iter()
                .filter(|diagnostic| {
                    diagnostic
                        .primary
                        .is_some_and(|location| location.file == file)
                })
                .cloned()
                .collect(),
        }
    }

    pub fn check(&self) -> &CheckResult {
        self.0.check.get_or_init(|| self.compute_check())
    }

    pub fn check_item(&self, item: ItemId) -> Option<&ItemCheck> {
        self.check().items.iter().find(|result| result.item == item)
    }

    pub fn check_with_control(
        &self,
        cancellation: kernel::control::CancellationToken,
        steps: Option<u64>,
    ) -> Result<&CheckResult, kernel::control::Interrupted> {
        kernel::control::run(cancellation, steps, || self.check())
    }

    fn compute_check(&self) -> CheckResult {
        let tree = self.tree();
        let outline = self.outline();
        let mut result = CheckResult {
            revision: self.revision(),
            status: CheckStatus::Checked,
            diagnostics: tree.diagnostics.clone(),
            outputs: Vec::new(),
            statistics: Vec::new(),
            goals: Vec::new(),
            items: Vec::new(),
            occurrences: Vec::new(),
            artifacts: Vec::new(),
        };
        let mut skipped = Vec::new();
        let source_location = |location: Location| {
            self.sources()
                .file(location.file)
                .map(|file| crate::syntax::SourceLocation {
                    source: file.source.clone(),
                    span: location.range,
                })
        };
        for item in outline.iter().filter(|item| {
            item.key.kind == ItemKind::Error
                || tree.diagnostics.iter().any(|diagnostic| {
                    diagnostic.code == "source" && diagnostic.primary == Some(item.location)
                })
        }) {
            if let Some(location) = source_location(item.location) {
                skipped.push((location, item.id.0));
                result.items.push(ItemCheck {
                    item: item.id,
                    status: ItemCheckStatus::Failed,
                });
            }
        }
        let (global, completed) = loop {
            kernel::control::checkpoint();
            let mut global = GlobalEnvironment::default();
            global.skip_declarations(skipped.clone());
            match global.add_modules_to_root(&tree.modules) {
                Ok(()) => break (global, true),
                Err(error) => {
                    let (error, location, origin) = self.locate_error(&error);
                    let dependencies = global
                        .blocked_dependencies()
                        .into_iter()
                        .map(ItemId)
                        .collect::<Vec<_>>();
                    let status = if !dependencies.is_empty() {
                        ItemCheckStatus::Blocked { dependencies }
                    } else if let ElaborationError::UnsolvedGoals(goals)
                    | ElaborationError::AmbiguousImplicit(goals) = error
                    {
                        result.goals.extend(self.capture_goals(
                            global.crate_env(),
                            goals,
                            location,
                        ));
                        ItemCheckStatus::Incomplete
                    } else {
                        ItemCheckStatus::Failed
                    };
                    let code = if matches!(status, ItemCheckStatus::Blocked { .. }) {
                        "blocked"
                    } else {
                        "elaboration"
                    };
                    let mut diagnostic = Diagnostic::error(
                        code,
                        format_elaboration_error(global.crate_env(), error),
                        location,
                    );
                    diagnostic.provenance = self.source_trace(&global.crate_env().sources, origin);
                    for entry in &diagnostic.provenance {
                        if let Some(syntax::DerivedOrigin::Expansion {
                            definition: Some(definition),
                            ..
                        }) = entry.origin
                            && let Some(location) = diagnostic
                                .provenance
                                .iter()
                                .find(|entry| entry.id == definition)
                                .and_then(|entry| entry.written)
                            && !diagnostic
                                .secondary
                                .iter()
                                .any(|(previous, _)| *previous == location)
                        {
                            diagnostic
                                .secondary
                                .push((location, "macro defined here".into()));
                        }
                    }
                    result.diagnostics.push(diagnostic);
                    let owner = location.and_then(|location| {
                        outline
                            .iter()
                            .filter(|item| {
                                item.location.file == location.file
                                    && tree::contains(item.location.range, location.range)
                            })
                            .min_by_key(|item| item.location.range.end - item.location.range.start)
                    });
                    let Some(owner) = owner else {
                        break (global, false);
                    };
                    result
                        .occurrences
                        .extend(self.capture_references(&global).into_iter().filter(
                            |occurrence| {
                                occurrence.location.file == owner.location.file
                                    && tree::contains(
                                        owner.location.range,
                                        occurrence.location.range,
                                    )
                            },
                        ));
                    if result.items.iter().any(|item| item.item == owner.id) {
                        break (global, false);
                    }
                    result.items.push(ItemCheck {
                        item: owner.id,
                        status,
                    });
                    let Some(location) = source_location(owner.location) else {
                        break (global, false);
                    };
                    skipped.push((location, owner.id.0));
                    // All partial registration state is owned by this attempt.
                    // Replaying the accepted prefix makes failure publication atomic.
                }
            }
        };
        let failed_modules = outline
            .iter()
            .filter(|item| {
                item.key.kind == ItemKind::Module
                    && result.items.iter().any(|checked| checked.item == item.id)
            })
            .collect::<Vec<_>>();
        for item in outline {
            if result.items.iter().any(|checked| checked.item == item.id) {
                continue;
            }
            let mut dependencies = failed_modules
                .iter()
                .filter(|module| {
                    let mut path = module.key.module.clone();
                    path.push(module.key.name.clone());
                    item.key.package == module.key.package && item.key.module.starts_with(&path)
                })
                .map(|module| module.id)
                .collect::<Vec<_>>();
            if matches!(item.key.kind, ItemKind::Field | ItemKind::Constructor)
                && let Some(owner_name) = item.key.name.split_once("::").map(|(owner, _)| owner)
                && let Some(owner) = outline.iter().find(|owner| {
                    owner.key.package == item.key.package
                        && owner.key.module == item.key.module
                        && owner.key.name == owner_name
                })
                && result.items.iter().any(|checked| {
                    checked.item == owner.id && checked.status != ItemCheckStatus::Checked
                })
            {
                dependencies.push(owner.id);
            }
            let status = if !completed {
                ItemCheckStatus::Failed
            } else if dependencies.is_empty() {
                ItemCheckStatus::Checked
            } else {
                ItemCheckStatus::Blocked { dependencies }
            };
            result.items.push(ItemCheck {
                item: item.id,
                status,
            });
        }
        result.status = if result.diagnostics.is_empty() {
            CheckStatus::Checked
        } else if result
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code == "blocked")
            || result
                .items
                .iter()
                .any(|item| item.status == ItemCheckStatus::Incomplete)
                && !result
                    .items
                    .iter()
                    .any(|item| item.status == ItemCheckStatus::Failed)
                && tree.diagnostics.is_empty()
        {
            CheckStatus::Incomplete
        } else {
            CheckStatus::Failed
        };
        result.occurrences.extend(self.capture_references(&global));
        let mut seen = std::collections::HashSet::new();
        result
            .occurrences
            .retain(|occurrence| seen.insert((occurrence.location, occurrence.target)));
        result.outputs = global
            .outputs()
            .iter()
            .map(|output| output.render(global.crate_env()))
            .collect();
        result.statistics = vec![
            format!("raw nodes: {:?}", global.arena().node_counts()),
            format!(
                "raw declaration nodes: {:?}",
                global.crate_env().declaration_node_counts()
            ),
            format!(
                "raw allocated nodes: {:?}",
                global.arena().allocated_node_counts()
            ),
            format!("raw caches: {:?}", global.crate_env().cache_counts()),
            format!(
                "kernel nodes: {:?}",
                global.kernel_env().arena().node_counts()
            ),
            format!("kernel caches: {:?}", global.kernel_env().cache_counts()),
            format!(
                "kernel declaration nodes: {}",
                global.kernel_env().declaration_node_count()
            ),
        ];
        if completed {
            global.crate_env().clear_elaboration_caches();
            global.kernel_env().clear_caches();
            let environment = Rc::new(global);
            for item in outline {
                if result.items.iter().any(|checked| {
                    checked.item == item.id && checked.status == ItemCheckStatus::Checked
                }) {
                    result
                        .artifacts
                        .push(CheckedArtifact::new(item, environment.clone()));
                }
            }
        }
        result
    }

    fn locate_error<'a>(
        &self,
        mut error: &'a ElaborationError,
    ) -> (
        &'a ElaborationError,
        Option<Location>,
        Option<syntax::AstId>,
    ) {
        let mut primary = None;
        let mut origin = None;
        while let ElaborationError::Located {
            location,
            error: inner,
            origin: inner_origin,
        } = error
        {
            origin = *inner_origin;
            primary = self
                .0
                .sources
                .file_id(&location.source.id.0)
                .and_then(|id| self.0.sources.file(id))
                .map(|file| file.location(location.span));
            error = inner;
        }
        (error, primary, origin)
    }

    pub fn render_diagnostic(&self, diagnostic: &Diagnostic) -> String {
        let heading = if matches!(diagnostic.code, "elaboration" | "blocked") {
            "Elaboration Error"
        } else {
            "Module Load Error"
        };
        let detail = if diagnostic.code == "syntax" {
            "parse error: "
        } else {
            ""
        };
        let mut message = format!("{heading}: {detail}{}", diagnostic.message);
        if let Some(location) = diagnostic.primary
            && let Some(file) = self.0.sources.file(location.file)
            && file.revision == location.revision
        {
            message.push('\n');
            message.push_str(
                &crate::syntax::SourceLocation {
                    source: file.source.clone(),
                    span: location.range,
                }
                .render(),
            );
        }
        for (location, label) in &diagnostic.secondary {
            if let Some(file) = self.0.sources.file(location.file)
                && file.revision == location.revision
            {
                message.push_str(&format!(
                    "\n{label}\n{}",
                    syntax::SourceLocation {
                        source: file.source.clone(),
                        span: location.range
                    }
                    .render()
                ));
            }
        }
        message
    }
}

#[cfg(test)]
mod edit_sequence_tests;
#[cfg(test)]
mod tests;

pub mod elaborator;
mod macros;
pub mod module_loader;
use elab::{metavariables, output};
#[cfg(test)]
mod elaboration_tests;
use syntax::{self, parse};

#[cfg(test)]
mod package_tests;
