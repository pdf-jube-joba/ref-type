//! Resolution dependencies, including scopes, imports and macro environments.
use crate::cache::{Fingerprint, fingerprint};
use front_syntax::syntax::{Module, ModuleBody, ModuleInstantiatePath, ModuleItem};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) struct Unit<'a> {
    pub path: Vec<String>,
    pub module: &'a Module,
    pub dependencies: BTreeSet<usize>,
    pub local_key: Fingerprint,
}

pub(crate) struct ModuleGraph<'a> {
    pub roots: &'a [Module],
    pub units: Vec<Unit<'a>>,
    pub indices: BTreeMap<Vec<String>, usize>,
}

impl<'a> ModuleGraph<'a> {
    pub fn new(roots: &'a [Module]) -> Self {
        let mut graph = Self {
            roots,
            units: Vec::new(),
            indices: BTreeMap::new(),
        };
        for root in roots {
            graph.collect(root, &[]);
        }
        // Header and scope membership changes can affect negative name lookups.
        let topology = format!("{:?}", graph.indices.keys().collect::<Vec<_>>());
        let mut aliases: BTreeMap<Vec<String>, BTreeMap<String, Vec<String>>> = BTreeMap::new();
        for index in 0..graph.units.len() {
            let path = graph.units[index].path.clone();
            let parent = &path[..path.len() - 1];
            let mut visible = aliases.get(parent).cloned().unwrap_or_default();
            let mut dependencies = BTreeSet::new();
            if let Some(parent) = graph.indices.get(parent) {
                dependencies.insert(*parent);
            }
            let module = graph.units[index].module;
            // Preserve the source-order identity of repeated module names.
            for (earlier, sibling) in graph.units[..index].iter().enumerate() {
                if sibling.module.name == module.name
                    && sibling.path[..sibling.path.len() - 1] == *parent
                {
                    dependencies.insert(earlier);
                }
            }
            let mut local = format!(
                "{topology}\n{:?}\n{:?}",
                module.parameters,
                module.header_source.as_ref().map(|s| &s.id)
            );
            if !module.parameters.is_empty() {
                local.push_str(&format!("{:?}", module.span));
            }
            if let ModuleBody::Inline(items) = &module.body {
                let namespace = items
                    .iter()
                    .all(|item| matches!(item, ModuleItem::ChildModule { .. }));
                for (item_index, item) in items.iter().enumerate() {
                    if let ModuleItem::ChildModule { module } = item {
                        local.push_str(&format!(
                            "\nchild {} {:?}",
                            module.name.0, module.parameters
                        ));
                        if !namespace {
                            let child = graph
                                .units
                                .iter()
                                .find(|unit| std::ptr::eq(unit.module, module.as_ref()))
                                .expect("child was collected");
                            graph.include_subtree(&child.path, &mut dependencies);
                        }
                        continue;
                    }
                    local.push_str(&format!(
                        "\n{item:?}\n{:?}\n{:?}",
                        module.declaration_spans.get(item_index),
                        module.source.as_ref().map(|s| &s.id)
                    ));
                    if let ModuleItem::Import {
                        path: import,
                        import_name,
                    } = item
                    {
                        let target = match import {
                            ModuleInstantiatePath::FromRoot { calls } => {
                                Some(calls.iter().map(|(name, _)| name.0.clone()).collect())
                            }
                            ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                                path.len().checked_sub(*back_parent).map(|length| {
                                    let mut target = path[..length].to_vec();
                                    target.extend(calls.iter().map(|(name, _)| name.0.clone()));
                                    target
                                })
                            }
                            ModuleInstantiatePath::FromImport { import_name, calls } => {
                                visible.get(import_name.as_str()).map(|base| {
                                    let mut target = base.clone();
                                    target.extend(calls.iter().map(|(name, _)| name.0.clone()));
                                    target
                                })
                            }
                        };
                        if let Some(target) = target {
                            // Instantiation exposes descendants as well as the direct scope.
                            graph.include_subtree(&target, &mut dependencies);
                            visible.insert(import_name.0.clone(), target);
                        } else {
                            // A failed or inherited alias lookup is itself a dependency.
                            dependencies.extend(0..graph.units.len());
                        }
                    }
                }
            }
            dependencies.remove(&index);
            graph.units[index].dependencies = dependencies;
            graph.units[index].local_key = fingerprint(local.as_bytes());
            aliases.insert(path, visible);
        }
        graph
    }

    fn collect(&mut self, module: &'a Module, parent: &[String]) {
        let mut path = parent.to_vec();
        path.push(module.name.0.clone());
        let mut occurrence = 1;
        while self.indices.contains_key(&path) {
            occurrence += 1;
            *path.last_mut().unwrap() = format!("{}#{occurrence}", module.name.0);
        }
        self.indices.insert(path.clone(), self.units.len());
        self.units.push(Unit {
            path: path.clone(),
            module,
            dependencies: BTreeSet::new(),
            local_key: fingerprint(&[]),
        });
        if let ModuleBody::Inline(items) = &module.body {
            for item in items {
                if let ModuleItem::ChildModule { module } = item {
                    self.collect(module, &path);
                }
            }
        }
    }

    fn include_subtree(&self, target: &[String], dependencies: &mut BTreeSet<usize>) {
        for length in 1..target.len() {
            if let Some(&ancestor) = self.indices.get(&target[..length]) {
                dependencies.insert(ancestor);
            }
        }
        for (index, unit) in self.units.iter().enumerate() {
            if unit.path.starts_with(target) {
                dependencies.insert(index);
            }
        }
    }

    pub fn closure(&self, roots: impl IntoIterator<Item = usize>) -> BTreeSet<usize> {
        let mut result = BTreeSet::new();
        let mut pending: Vec<_> = roots.into_iter().collect();
        while let Some(index) = pending.pop() {
            if result.insert(index) {
                pending.extend(&self.units[index].dependencies);
            }
        }
        result
    }

    pub fn key(&self, index: usize, settings: &Fingerprint) -> Fingerprint {
        let mut bytes = settings.to_vec();
        for dependency in self.closure([index]) {
            bytes.extend(self.units[dependency].local_key);
        }
        bytes.extend(format!("{:?}", self.units[index].path).as_bytes());
        fingerprint(&bytes)
    }

    pub fn selected(&self, selected: &BTreeSet<usize>) -> Vec<Module> {
        fn filter(
            graph: &ModuleGraph<'_>,
            module: &Module,
            selected: &BTreeSet<usize>,
        ) -> Option<Module> {
            let index = graph
                .units
                .iter()
                .position(|unit| std::ptr::eq(unit.module, module))?;
            if !selected.contains(&index) {
                return None;
            }
            let mut result = module.clone();
            if let ModuleBody::Inline(items) = &module.body {
                let mut filtered = Vec::new();
                let mut spans = Vec::new();
                for (index, item) in items.iter().enumerate() {
                    let item = match item {
                        ModuleItem::ChildModule { module } => {
                            let Some(module) = filter(graph, module, selected) else {
                                continue;
                            };
                            ModuleItem::ChildModule {
                                module: Box::new(module),
                            }
                        }
                        item => item.clone(),
                    };
                    filtered.push(item);
                    spans.push(
                        module
                            .declaration_spans
                            .get(index)
                            .copied()
                            .unwrap_or(module.span),
                    );
                }
                result.body = ModuleBody::Inline(filtered);
                result.declaration_spans = spans;
            }
            Some(result)
        }
        self.roots
            .iter()
            .filter_map(|root| filter(self, root, selected))
            .collect()
    }
}
