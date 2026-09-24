use super::{Location, tree::ModuleTree};
use crate::syntax::{Module, ModuleBody, ModuleItem, SourceSpan};
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ItemId(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ItemVersion(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ItemKind {
    Module,
    Definition,
    Inductive,
    Record,
    Import,
    Macro,
    Query,
    Error,
    Field,
    Constructor,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ItemKey {
    pub package: Option<super::PackageId>,
    pub module: Vec<String>,
    pub kind: ItemKind,
    pub name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutlineItem {
    pub id: ItemId,
    pub key: ItemKey,
    pub version: ItemVersion,
    pub location: Location,
    pub name_location: Option<Location>,
    pub order: usize,
}

#[derive(Default)]
pub(super) struct ItemInterner {
    next: u64,
    unique: HashMap<ItemKey, ItemId>,
}

impl ItemInterner {
    pub fn outline(&mut self, tree: &ModuleTree) -> Vec<OutlineItem> {
        let mut result = Vec::new();
        for module in &tree.modules {
            collect(tree, module, &[], &mut result);
        }
        // Until lookup dependencies are complete, include the whole reachable
        // workspace. This also covers negative lookups and transparent bodies.
        let mut input_hash = std::collections::hash_map::DefaultHasher::new();
        let mut files = tree.files.values().collect::<Vec<_>>();
        files.sort_by_key(|file| &file.source.id.0);
        for file in files {
            file.source.id.hash(&mut input_hash);
            file.identity.hash(&mut input_hash);
            file.source.text.hash(&mut input_hash);
        }
        let workspace_version = input_hash.finish();
        let mut counts = HashMap::<ItemKey, usize>::new();
        for item in &result {
            *counts.entry(item.key.clone()).or_default() += 1;
        }
        // Old snapshots own their assigned IDs; the matching table only needs
        // names present in the current input, including during repeated renames.
        self.unique.retain(|key, _| counts.get(key) == Some(&1));
        for item in &mut result {
            let mut version = std::collections::hash_map::DefaultHasher::new();
            workspace_version.hash(&mut version);
            item.version.hash(&mut version);
            item.version = ItemVersion(version.finish());
            let mut allocate = || {
                let id = ItemId(self.next);
                self.next += 1;
                id
            };
            let id = if counts[&item.key] == 1
                && !matches!(item.key.kind, ItemKind::Query | ItemKind::Error)
            {
                *self.unique.entry(item.key.clone()).or_insert_with(allocate)
            } else {
                allocate()
            };
            item.id = id;
        }
        result
    }
}

fn collect(tree: &ModuleTree, module: &Module, parent: &[String], result: &mut Vec<OutlineItem>) {
    if let Some(source) = &module.header_source {
        push(
            tree,
            source,
            module.span,
            parent,
            ItemKind::Module,
            (module.name.0.clone(), module.name.span()),
            result,
        );
    }
    let mut path = parent.to_vec();
    path.push(module.name.0.clone());
    if let ModuleBody::Inline(items) = &module.body {
        for (index, item) in items.iter().enumerate() {
            if let ModuleItem::ChildModule { module } = item {
                collect(tree, module, &path, result);
                continue;
            }
            let (kind, name) = match item {
                ModuleItem::Definition { owner, name, .. } => (
                    ItemKind::Definition,
                    owner
                        .as_ref()
                        .map(|owner| format!("{}::{}", owner.type_name.0, name.0))
                        .unwrap_or_else(|| name.0.clone()),
                ),
                ModuleItem::Inductive { type_name, .. } => {
                    (ItemKind::Inductive, type_name.0.clone())
                }
                ModuleItem::Record { type_name, .. } => (ItemKind::Record, type_name.0.clone()),
                ModuleItem::Import { import_name, .. } => (ItemKind::Import, import_name.0.clone()),
                ModuleItem::UserMacro { name, .. } | ModuleItem::MathMacro { name, .. } => {
                    (ItemKind::Macro, name.0.clone())
                }
                ModuleItem::Error { name, .. } => (
                    ItemKind::Error,
                    name.as_ref().map(|name| name.0.clone()).unwrap_or_default(),
                ),
                _ => (ItemKind::Query, String::new()),
            };
            let name_span = match item {
                ModuleItem::Definition { name, .. }
                | ModuleItem::UserMacro { name, .. }
                | ModuleItem::MathMacro { name, .. } => name.span(),
                ModuleItem::Inductive { type_name, .. } | ModuleItem::Record { type_name, .. } => {
                    type_name.span()
                }
                ModuleItem::Import { import_name, .. } => import_name.span(),
                ModuleItem::Error { name, .. } => name.as_ref().and_then(|name| name.span()),
                _ => None,
            };
            if let Some(source) = &module.source {
                push(
                    tree,
                    source,
                    module.declaration_spans[index],
                    &path,
                    kind,
                    (name, name_span),
                    result,
                );
                match item {
                    ModuleItem::Record {
                        type_name, fields, ..
                    } => {
                        for (field, _) in fields {
                            if let Some(span) = field.span() {
                                push(
                                    tree,
                                    source,
                                    span,
                                    &path,
                                    ItemKind::Field,
                                    (format!("{}::{}", type_name.0, field.0), Some(span)),
                                    result,
                                );
                            }
                        }
                    }
                    ModuleItem::Inductive {
                        type_name,
                        constructors,
                        ..
                    } => {
                        for (constructor, _, _) in constructors {
                            if let Some(span) = constructor.span() {
                                push(
                                    tree,
                                    source,
                                    span,
                                    &path,
                                    ItemKind::Constructor,
                                    (format!("{}::{}", type_name.0, constructor.0), Some(span)),
                                    result,
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}

fn push(
    tree: &ModuleTree,
    source: &crate::syntax::SourceFile,
    span: SourceSpan,
    parent: &[String],
    kind: ItemKind,
    (name, name_span): (String, Option<SourceSpan>),
    result: &mut Vec<OutlineItem>,
) {
    let Some(file) = tree.files.values().find(|file| file.source.id == source.id) else {
        return;
    };
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    source
        .text
        .get(span.start..span.end)
        .unwrap_or_default()
        .hash(&mut hasher);
    let name_location = name_span.map(|span| file.location(span));
    result.push(OutlineItem {
        id: ItemId(0),
        key: ItemKey {
            package: tree.file_packages.get(&file.id).copied(),
            module: if parent
                .first()
                .and_then(|name| super::PackageId::from_module_name(name))
                .is_some()
            {
                parent[1..].to_vec()
            } else {
                parent.to_vec()
            },
            kind,
            name,
        },
        version: ItemVersion(hasher.finish()),
        location: file.location(span),
        name_location,
        order: result.len(),
    });
}

#[cfg(test)]
mod tests {
    use crate::AnalysisHost;

    #[test]
    fn repeated_renames_keep_only_current_identity_keys() {
        let mut host = AnalysisHost::new("/virtual/root.ref").unwrap();
        let mut previous = None;
        for index in 0..100 {
            host.sources_mut().set_overlay("/virtual/root.ref", format!(
                r"\module M {{ \definition Keep: \SetKind := \Set; \definition A{index}: \SetKind := \Set; \check \Set: \SetKind; }}"
            ));
            let snapshot = host.snapshot();
            let id = snapshot.outline()[1].id;
            if let Some(previous) = previous {
                assert_eq!(id, previous);
            }
            previous = Some(id);
            assert_eq!(host.identities.borrow().unique.len(), 3);
        }
    }
}
