use crate::{
    parse::{parse_module_items_from_source, parse_modules_from_source},
    syntax::{Module, ModuleBody, ModuleItem, SourceFile, SourceId},
};
use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
    sync::Arc,
};

const SOURCE_EXTENSION: &str = "ref";

/// Load the complete module tree starting at an anonymous root source file.
///
/// `\module child;` inside logical module `parent` resolves to
/// `<root directory>/parent/child.ref`.
pub trait SourceProvider {
    fn read(&mut self, path: &Path) -> Result<Arc<SourceFile>, String>;
    fn identity(&self, path: &Path) -> Result<PathBuf, String>;
    fn modules(&mut self, path: &Path) -> Result<Vec<Module>, String> {
        parse_modules_from_source(&self.read(path)?)
    }
    fn items(
        &mut self,
        path: &Path,
    ) -> Result<(Vec<ModuleItem>, Vec<crate::syntax::SourceSpan>), String> {
        parse_module_items_from_source(&self.read(path)?)
    }
}

pub struct DiskSource;
impl SourceProvider for DiskSource {
    fn read(&mut self, path: &Path) -> Result<Arc<SourceFile>, String> {
        Ok(Arc::new(SourceFile {
            id: SourceId(path.to_path_buf()),
            text: read_source(path, "source file")?,
        }))
    }
    fn identity(&self, path: &Path) -> Result<PathBuf, String> {
        path.canonicalize()
            .map_err(|error| format!("cannot open {}: {error}", path.display()))
    }
}

pub fn load_modules_from_root(root_file: &Path) -> Result<Vec<Module>, String> {
    load_modules(root_file, &mut DiskSource)
}

pub fn load_modules(
    root_file: &Path,
    provider: &mut dyn SourceProvider,
) -> Result<Vec<Module>, String> {
    if root_file.extension().and_then(|ext| ext.to_str()) != Some(SOURCE_EXTENSION) {
        return Err(format!(
            "root source file must have the .{} extension: {}",
            SOURCE_EXTENSION,
            root_file.display()
        ));
    }

    let root_source = provider.read(root_file)?;
    let mut modules = provider.modules(root_file)?;
    for module in &mut modules {
        attach_source(module, &root_source);
    }
    let source_root = root_file.parent().unwrap_or_else(|| Path::new("."));
    let mut loader = ModuleLoader {
        source_root,
        provider,
        loaded_files: HashMap::new(),
    };

    for module in &mut modules {
        loader.resolve_module(module, &[])?;
    }
    Ok(modules)
}

struct ModuleLoader<'a> {
    source_root: &'a Path,
    provider: &'a mut dyn SourceProvider,
    loaded_files: HashMap<PathBuf, String>,
}

impl ModuleLoader<'_> {
    fn resolve_module(
        &mut self,
        module: &mut Module,
        parent_module_path: &[String],
    ) -> Result<(), String> {
        let mut module_path = parent_module_path.to_vec();
        module_path.push(module.name.0.clone());
        let display_module_path = format!("root.{}", module_path.join("."));

        if matches!(module.body, ModuleBody::External) {
            let source_path = self.external_source_path(parent_module_path, &module.name.0);
            let canonical_path = self.provider.identity(&source_path)?;

            if let Some(first_module) = self
                .loaded_files
                .insert(canonical_path, display_module_path.clone())
            {
                return Err(format!(
                    "source file {} is used by both module '{}' and module '{}'",
                    source_path.display(),
                    first_module,
                    display_module_path
                ));
            }

            let source = self.provider.read(&source_path)?;
            let (declarations, spans) = self.provider.items(&source_path)?;
            module.body = ModuleBody::Inline(declarations);
            module.declaration_spans = spans;
            attach_source(module, &source);
        }

        let ModuleBody::Inline(declarations) = &mut module.body else {
            unreachable!("external module body was resolved above")
        };
        for declaration in declarations {
            if let ModuleItem::ChildModule { module: child } = declaration {
                self.resolve_module(child, &module_path)?;
            }
        }

        Ok(())
    }

    fn external_source_path(&self, parent_module_path: &[String], name: &str) -> PathBuf {
        let mut path = self.source_root.to_path_buf();
        for component in parent_module_path {
            path.push(component);
        }
        path.push(name);
        path.set_extension(SOURCE_EXTENSION);
        path
    }
}

fn read_source(path: &Path, description: &str) -> Result<String, String> {
    fs::read_to_string(path).map_err(|error| {
        format!(
            "failed to read {} at {}: {}",
            description,
            path.display(),
            error
        )
    })
}

fn attach_source(module: &mut Module, source: &Arc<SourceFile>) {
    module.source = Some(Arc::clone(source));
    module
        .header_source
        .get_or_insert_with(|| Arc::clone(source));
    if let ModuleBody::Inline(items) = &mut module.body {
        for item in items {
            if let ModuleItem::ChildModule { module } = item {
                attach_source(module, source);
            }
        }
    }
}
