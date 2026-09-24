use super::{Diagnostic, FileId, FileSnapshot};
use crate::{
    parse::{ParsedSource, parse_source_recovering},
    syntax::{Module, ModuleBody, ModuleItem, SourceSpan},
};
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    sync::Arc,
};

#[derive(Default)]
pub(super) struct ModuleTree {
    pub modules: Vec<Module>,
    pub parsed: HashMap<FileId, Arc<ParsedSource>>,
    pub files: HashMap<FileId, Arc<FileSnapshot>>,
    pub diagnostics: Vec<Diagnostic>,
    pub packages: super::PackageGraph,
    pub file_packages: HashMap<FileId, super::PackageId>,
}

impl ModuleTree {
    pub fn load(
        root: &Path,
        mut read: impl FnMut(&Path) -> Result<Arc<FileSnapshot>, String>,
    ) -> Self {
        let mut tree = Self::default();
        if root.file_name().is_some_and(|name| name == "ref.toml") {
            tree.load_packages(root, &mut read);
            return tree;
        }
        if root.extension().and_then(|ext| ext.to_str()) != Some("ref") {
            tree.diagnostics.push(Diagnostic::error(
                "source",
                format!(
                    "root source file must have the .ref extension: {}",
                    root.display()
                ),
                None,
            ));
            return tree;
        }
        let source = match read(root) {
            Ok(source) => source,
            Err(message) => {
                tree.diagnostics
                    .push(Diagnostic::error("source", message, None));
                return tree;
            }
        };
        let parsed = tree.parse(source.clone(), true);
        let mut modules = parsed.modules.clone();
        let mut used = HashMap::new();
        let source_root = root.parent().unwrap_or_else(|| Path::new("."));
        for module in &mut modules {
            attach_source(module, &source);
            tree.resolve(module, &[], source_root, &mut used, &mut read);
        }
        tree.modules = modules;
        tree
    }

    pub(super) fn parse(&mut self, file: Arc<FileSnapshot>, root: bool) -> Arc<ParsedSource> {
        let parsed = Arc::new(parse_source_recovering(&file.source.text, root));
        self.diagnostics
            .extend(parsed.diagnostics.iter().map(|error| {
                Diagnostic::error(
                    "syntax",
                    error.message.clone(),
                    Some(file.location(error.span)),
                )
            }));
        self.parsed.insert(file.id, parsed.clone());
        self.files.insert(file.id, file);
        parsed
    }

    pub(super) fn resolve(
        &mut self,
        module: &mut Module,
        parent: &[String],
        root: &Path,
        used: &mut HashMap<PathBuf, String>,
        read: &mut impl FnMut(&Path) -> Result<Arc<FileSnapshot>, String>,
    ) {
        let mut path = parent.to_vec();
        path.push(module.name.0.clone());
        if matches!(module.body, ModuleBody::External) {
            let source_path = root
                .join(path.iter().collect::<PathBuf>())
                .with_extension("ref");
            let result = read(&source_path).and_then(|file| {
                let display = format!("root.{}", path.join("."));
                if let Some(first) = used.insert(file.identity.clone(), display.clone()) {
                    return Err(format!(
                        "source file {} is used by both module '{first}' and module '{display}'",
                        source_path.display()
                    ));
                }
                Ok(file)
            });
            match result {
                Ok(file) => {
                    let parsed = self.parse(file.clone(), false);
                    module.body = ModuleBody::Inline(parsed.items.clone());
                    module.declaration_spans = parsed.item_spans.clone();
                    attach_source(module, &file);
                }
                Err(message) => {
                    let location = module.header_source.as_ref().and_then(|source| {
                        self.files
                            .values()
                            .find(|file| file.source.id == source.id)
                            .map(|file| file.location(module.span))
                    });
                    self.diagnostics
                        .push(Diagnostic::error("source", message, location));
                    module.body = ModuleBody::Inline(Vec::new());
                    return;
                }
            }
        }
        if let ModuleBody::Inline(items) = &mut module.body {
            for item in items {
                if let ModuleItem::ChildModule { module } = item {
                    self.resolve(module, &path, root, used, read);
                }
            }
        }
    }
}

pub(super) fn attach_source(module: &mut Module, file: &FileSnapshot) {
    module.source = Some(file.source.clone());
    module
        .header_source
        .get_or_insert_with(|| file.source.clone());
    if let ModuleBody::Inline(items) = &mut module.body {
        for item in items {
            if let ModuleItem::ChildModule { module } = item {
                attach_source(module, file);
            }
        }
    }
}

pub(super) fn contains(outer: SourceSpan, inner: SourceSpan) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}
