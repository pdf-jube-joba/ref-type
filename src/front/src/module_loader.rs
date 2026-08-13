use crate::{
    parse::{str_parse_module_items, str_parse_modules},
    syntax::{Module, ModuleBody, ModuleItem},
};
use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
};

pub const SOURCE_EXTENSION: &str = "ref";

/// Load the complete module tree starting at an anonymous root source file.
///
/// `\module child;` inside logical module `parent` resolves to
/// `<root directory>/parent/child.ref`.
pub fn load_modules_from_root(root_file: &Path) -> Result<Vec<Module>, String> {
    if root_file.extension().and_then(|ext| ext.to_str()) != Some(SOURCE_EXTENSION) {
        return Err(format!(
            "root source file must have the .{} extension: {}",
            SOURCE_EXTENSION,
            root_file.display()
        ));
    }

    let root_source = read_source(root_file, "root source file")?;
    let modules = str_parse_modules(&root_source)
        .map_err(|error| format!("failed to parse {}: {}", root_file.display(), error))?;
    let source_root = root_file.parent().unwrap_or_else(|| Path::new("."));
    let mut loader = ModuleLoader {
        source_root,
        loaded_files: HashMap::new(),
    };

    modules
        .into_iter()
        .map(|module| loader.resolve_module(module, &[]))
        .collect()
}

struct ModuleLoader<'a> {
    source_root: &'a Path,
    loaded_files: HashMap<PathBuf, String>,
}

impl ModuleLoader<'_> {
    fn resolve_module(
        &mut self,
        mut module: Module,
        parent_module_path: &[String],
    ) -> Result<Module, String> {
        let mut module_path = parent_module_path.to_vec();
        module_path.push(module.name.0.clone());
        let display_module_path = format!("root.{}", module_path.join("."));

        if matches!(module.body, ModuleBody::External) {
            let source_path = self.external_source_path(parent_module_path, &module.name.0);
            let canonical_path = source_path.canonicalize().map_err(|error| {
                format!(
                    "module '{}' requires source file {}, but it could not be opened: {}",
                    display_module_path,
                    source_path.display(),
                    error
                )
            })?;

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

            let source = read_source(&source_path, &format!("module '{}'", display_module_path))?;
            let declarations = str_parse_module_items(&source)
                .map_err(|error| format!("failed to parse {}: {}", source_path.display(), error))?;
            module.body = ModuleBody::Inline(declarations);
        }

        let ModuleBody::Inline(declarations) = &mut module.body else {
            unreachable!("external module body was resolved above")
        };
        for declaration in declarations {
            if let ModuleItem::ChildModule { module: child } = declaration {
                **child = self.resolve_module((**child).clone(), &module_path)?;
            }
        }

        Ok(module)
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
