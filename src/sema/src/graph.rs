//! Resolution dependencies, including scopes, imports and macro environments.
use crate::cache::{Fingerprint, fingerprint};
use ::syntax::syntax::{Module, ModuleBody, ModuleInstantiatePath, ModuleItem};
use ::syntax::visit::ModulePaths;
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
    topology: Fingerprint,
}

impl<'a> ModuleGraph<'a> {
    pub fn new(roots: &'a [Module]) -> Self {
        let mut graph = Self {
            roots,
            units: Vec::new(),
            indices: BTreeMap::new(),
            topology: fingerprint(&[]),
        };
        for root in roots {
            graph.collect(root, &[]);
        }
        // Header and scope membership changes can affect negative name lookups.
        graph.topology =
            fingerprint(format!("{:?}", graph.indices.keys().collect::<Vec<_>>()).as_bytes());
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
                "{:?}\n{:?}",
                module.parameters,
                module.header_source.as_ref().map(|s| &s.id)
            );
            if !module.parameters.is_empty() {
                local.push_str(&format!("{:?}", module.span));
            }
            module.parameters.clone().visit_module_paths(&mut |import| {
                graph.include_module_path(import, &path, &visible, &mut dependencies);
            });
            if let ModuleBody::Inline(items) = &module.body {
                for (item_index, item) in items.iter().enumerate() {
                    if let ModuleItem::ChildModule { module } = item {
                        local.push_str(&format!(
                            "\nchild {} {:?}",
                            module.name.0, module.parameters
                        ));
                        continue;
                    }
                    local.push_str(&format!(
                        "\n{item:?}\n{:?}\n{:?}",
                        module.declaration_spans.get(item_index),
                        module.source.as_ref().map(|s| &s.id)
                    ));
                    graph.include_imports(item, &path, &mut visible, &mut dependencies);
                }
            }
            dependencies.remove(&index);
            graph.units[index].dependencies = dependencies;
            graph.units[index].local_key = fingerprint(local.as_bytes());
            aliases.insert(path, visible);
        }
        graph
    }

    fn include_imports(
        &self,
        item: &ModuleItem,
        path: &[String],
        visible: &mut BTreeMap<String, Vec<String>>,
        dependencies: &mut BTreeSet<usize>,
    ) {
        if let ModuleItem::Scoped { items, .. } = item {
            let mut scoped = visible.clone();
            for item in items {
                self.include_imports(item, path, &mut scoped, dependencies);
            }
            return;
        }
        item.clone().visit_module_paths(&mut |import| {
            self.include_module_path(import, path, visible, dependencies);
        });
        if let ModuleItem::Import {
            path: import,
            import_name,
        } = item
            && let Some(target) = Self::module_target(import, path, visible)
        {
            visible.insert(import_name.0.clone(), target);
        }
    }

    fn include_module_path(
        &self,
        import: &ModuleInstantiatePath,
        path: &[String],
        visible: &BTreeMap<String, Vec<String>>,
        dependencies: &mut BTreeSet<usize>,
    ) {
        if let Some(target) = Self::module_target(import, path, visible) {
            self.include_subtree(&target, dependencies);
        } else {
            // A failed or inherited alias lookup is itself a dependency.
            dependencies.extend(0..self.units.len());
        }
    }

    fn module_target(
        import: &ModuleInstantiatePath,
        path: &[String],
        visible: &BTreeMap<String, Vec<String>>,
    ) -> Option<Vec<String>> {
        match import {
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
        }
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
        bytes.extend(self.topology);
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
            let mut result = Module {
                name: module.name.clone(),
                parameters: module.parameters.clone(),
                body: ModuleBody::External,
                span: module.span,
                declaration_spans: module.declaration_spans.clone(),
                source: module.source.clone(),
                header_source: module.header_source.clone(),
            };
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
