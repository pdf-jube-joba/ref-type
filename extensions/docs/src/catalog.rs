use std::{
    collections::BTreeMap,
    fs,
    path::{Component, Path, PathBuf},
};
use syntax::parse::documentation::{DocumentationItem, parse_documentation};

pub struct Source {
    pub path: PathBuf,
    pub directory: usize,
    pub text: String,
    pub items: Vec<DocumentationItem>,
    pub error: Option<String>,
}

pub struct Directory {
    pub path: PathBuf,
    pub parent: Option<usize>,
    pub directories: Vec<usize>,
    pub files: Vec<usize>,
    pub readme: Option<String>,
}

#[derive(Default)]
pub struct Catalog {
    pub directories: Vec<Directory>,
    pub files: Vec<Source>,
    pub links: BTreeMap<PathBuf, String>,
}

impl Catalog {
    pub fn read(root: &Path) -> Result<Self, String> {
        let root = root.canonicalize().map_err(|e| {
            format!(
                "cannot open library directory {}: {e}. Use --libs PATH.",
                root.display()
            )
        })?;
        if !root.is_dir() {
            return Err(format!(
                "library path is not a directory: {}",
                root.display()
            ));
        }
        let mut catalog = Self::default();
        catalog.visit(&root, Path::new(""), None)?;
        Ok(catalog)
    }

    fn visit(
        &mut self,
        root: &Path,
        relative: &Path,
        parent: Option<usize>,
    ) -> Result<usize, String> {
        let id = self.directories.len();
        self.links.insert(relative.to_owned(), format!("/dir/{id}"));
        self.directories.push(Directory {
            path: relative.to_owned(),
            parent,
            directories: vec![],
            files: vec![],
            readme: None,
        });
        let path = root.join(relative);
        let mut entries = fs::read_dir(&path)
            .map_err(|e| format!("cannot read {}: {e}", path.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| e.to_string())?;
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if name.starts_with('.')
                || matches!(name.as_ref(), "refcache" | "target" | "node_modules")
            {
                continue;
            }
            let kind = entry.file_type().map_err(|e| e.to_string())?;
            // Never follow symlinks, including links to directories inside the tree.
            if kind.is_symlink() {
                continue;
            }
            let relative = relative.join(entry.file_name());
            if kind.is_dir() {
                let child = self.visit(root, &relative, Some(id))?;
                self.directories[id].directories.push(child);
            } else if kind.is_file()
                && (name == "README.md" || relative.extension().is_some_and(|ext| ext == "ref"))
            {
                let text = fs::read_to_string(entry.path())
                    .map_err(|e| format!("cannot read {}: {e}", relative.display()))?;
                if name == "README.md" {
                    self.links.insert(relative, format!("/dir/{id}#readme"));
                    self.directories[id].readme = Some(text);
                } else {
                    let (items, error) = match parse_documentation(&text) {
                        Ok(items) => (items, None),
                        Err(error) => (vec![], Some(error.message())),
                    };
                    let file_id = self.files.len();
                    self.links
                        .insert(relative.clone(), format!("/file/{file_id}"));
                    self.files.push(Source {
                        path: relative,
                        directory: id,
                        text,
                        items,
                        error,
                    });
                    self.directories[id].files.push(file_id);
                }
            }
        }
        Ok(id)
    }

    /// Resolve Markdown links only to indexed resources, never to the filesystem.
    pub fn link(&self, base: &Path, destination: &str) -> Option<String> {
        if destination.starts_with('#')
            || destination.starts_with("https://")
            || destination.starts_with("http://")
            || destination.starts_with("mailto:")
        {
            return Some(destination.to_owned());
        }
        let (path, fragment) = destination.split_once('#').unwrap_or((destination, ""));
        let mut normalized = PathBuf::new();
        for component in base.join(path).components() {
            match component {
                Component::Normal(part) => normalized.push(part),
                Component::CurDir => {}
                Component::ParentDir => {
                    if !normalized.pop() {
                        return None;
                    }
                }
                _ => return None,
            }
        }
        self.links.get(&normalized).map(|link| {
            if fragment.is_empty() {
                link.clone()
            } else {
                let prefix = if normalized.extension().is_some_and(|ext| ext == "md") {
                    "md-"
                } else {
                    ""
                };
                format!(
                    "{}#{prefix}{fragment}",
                    link.split('#').next().unwrap_or(link)
                )
            }
        })
    }
}
