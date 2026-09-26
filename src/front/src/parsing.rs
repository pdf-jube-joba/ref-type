use crate::{
    Diagnostic, Location, QueryStats, SourceSnapshot,
    cache::{Fingerprint, fingerprint},
};
use front_syntax::{
    module_loader::SourceProvider,
    parse,
    syntax::{Module, ModuleItem, SourceFile, SourceSpan},
};
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    sync::Arc,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ParseKind {
    Root,
    Module,
}

#[derive(Debug, Clone)]
pub enum ParsedSyntax {
    Root(Vec<Module>),
    Module {
        items: Vec<ModuleItem>,
        spans: Vec<SourceSpan>,
    },
}

#[derive(Debug, Clone)]
pub struct ParseResult {
    pub source: Arc<SourceFile>,
    pub syntax: Option<ParsedSyntax>,
    pub diagnostics: Vec<Diagnostic>,
}

type ParseKey = (PathBuf, Fingerprint, ParseKind);
#[derive(Default)]
pub(crate) struct ParseCache {
    entries: HashMap<ParseKey, Arc<ParseResult>>,
}
impl ParseCache {
    pub fn parse(
        &mut self,
        snapshot: &SourceSnapshot,
        path: &Path,
        kind: ParseKind,
        stats: &mut QueryStats,
    ) -> Arc<ParseResult> {
        let path = snapshot.identity(path);
        let Some(source) = snapshot.source(&path) else {
            return Arc::new(ParseResult {
                source: Arc::new(SourceFile {
                    id: front_syntax::syntax::SourceId(path.clone()),
                    text: String::new(),
                }),
                syntax: None,
                diagnostics: vec![Diagnostic {
                    message: format!("source file is missing: {}", path.display()),
                    location: Some(Location {
                        file: path,
                        range: 0..0,
                    }),
                    goals: vec![],
                }],
            });
        };
        let key = (path.clone(), fingerprint(source.text.as_bytes()), kind);
        if let Some(cached) = self.entries.get(&key) {
            stats.reused_parses += 1;
            return cached.clone();
        }
        stats.parsed_files += 1;
        let result = match kind {
            ParseKind::Root => parse::parse_root(&source.text).map(ParsedSyntax::Root),
            ParseKind::Module => parse::parse_items(&source.text)
                .map(|(items, spans)| ParsedSyntax::Module { items, spans }),
        };
        let (syntax, diagnostics) = match result {
            Ok(syntax) => (Some(syntax), vec![]),
            Err(error) => (
                None,
                vec![Diagnostic {
                    message: format!("Module Load Error: {}", error.message()),
                    location: Some(Location {
                        file: path,
                        range: error.span().start..error.span().end,
                    }),
                    goals: vec![],
                }],
            ),
        };
        let parsed = Arc::new(ParseResult {
            source: source.clone(),
            syntax,
            diagnostics,
        });
        self.entries.insert(key, parsed.clone());
        parsed
    }
    pub fn clear(&mut self) {
        self.entries.clear();
    }
}

pub(crate) struct SnapshotLoader<'a> {
    pub snapshot: &'a SourceSnapshot,
    pub cache: &'a mut ParseCache,
    pub stats: &'a mut QueryStats,
    pub diagnostics: Vec<Diagnostic>,
}
impl SourceProvider for SnapshotLoader<'_> {
    fn identity(&self, path: &Path) -> Result<PathBuf, String> {
        Ok(self.snapshot.identity(path))
    }
    fn read(&mut self, path: &Path) -> Result<Arc<SourceFile>, String> {
        self.snapshot
            .source(path)
            .cloned()
            .ok_or_else(|| format!("source file is missing: {}", path.display()))
    }
    fn modules(&mut self, path: &Path) -> Result<Vec<Module>, String> {
        let result = self
            .cache
            .parse(self.snapshot, path, ParseKind::Root, self.stats);
        self.diagnostics.extend(result.diagnostics.clone());
        match &result.syntax {
            Some(ParsedSyntax::Root(modules)) => Ok(modules.clone()),
            _ => Err(result
                .diagnostics
                .iter()
                .map(|d| d.message.as_str())
                .collect::<Vec<_>>()
                .join("\n")),
        }
    }
    fn items(&mut self, path: &Path) -> Result<(Vec<ModuleItem>, Vec<SourceSpan>), String> {
        let result = self
            .cache
            .parse(self.snapshot, path, ParseKind::Module, self.stats);
        self.diagnostics.extend(result.diagnostics.clone());
        match &result.syntax {
            Some(ParsedSyntax::Module { items, spans }) => Ok((items.clone(), spans.clone())),
            _ => Ok((Vec::new(), Vec::new())),
        }
    }
}
