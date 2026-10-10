//! Checkpoint identities for prefixes of the resolved checking order.
use crate::{
    cache::{Fingerprint, fingerprint},
    graph::ModuleGraph,
};
use resolve::{
    CheckStep,
    hir::{Module, ModuleBody, ModuleId, ModuleItem},
};
use std::collections::{BTreeSet, HashMap};

pub(crate) struct EnvironmentPlan {
    pub steps: Vec<usize>,
    pub checkpoints: Vec<(usize, Fingerprint)>,
}

impl EnvironmentPlan {
    pub fn new(
        project: &resolve::Project,
        graph: &ModuleGraph<'_>,
        settings: &Fingerprint,
    ) -> Self {
        let _phase = elaboration::profiling::Phase::start("query.environment-plan");
        let _cost = timing::costs::Scope::enter("query.environment-plan");
        fn collect<'a>(
            module: &'a Module,
            parent: &[String],
            modules: &mut Vec<(&'a Module, Vec<String>)>,
            paths: &mut std::collections::HashSet<Vec<String>>,
        ) {
            let mut path = parent.to_vec();
            path.push(module.name.0.clone());
            let mut occurrence = 1;
            while !paths.insert(path.clone()) {
                occurrence += 1;
                *path.last_mut().unwrap() = format!("{}#{occurrence}", module.name.0);
            }
            modules.push((module, path.clone()));
            if let ModuleBody::Inline(items) = &module.body {
                for item in items {
                    if let ModuleItem::ChildModule { module } = item {
                        collect(module, &path, modules, paths);
                    }
                }
            }
        }
        let mut modules = Vec::new();
        let mut paths = std::collections::HashSet::new();
        for module in &project.modules {
            collect(module, &[], &mut modules, &mut paths);
        }
        let mut bindings_by_module: HashMap<_, Vec<_>> = HashMap::new();
        for (id, binding) in &project.bindings {
            bindings_by_module
                .entry(binding.module)
                .or_default()
                .push((id, binding));
        }
        let mut imports_by_module: HashMap<_, Vec<_>> = HashMap::new();
        for (id, import) in &project.imports {
            imports_by_module
                .entry(import.owner)
                .or_default()
                .push((id, import));
        }
        let mut units = HashMap::new();
        let mut module_keys = HashMap::new();
        let mut parameter_keys = HashMap::new();
        let mut layout = settings.to_vec();
        // Resolution allocates module identities before declaration identities.
        // Include that complete layout, including empty and repeated scopes.
        for (module, path) in &modules {
            layout.extend(format!("{:?}:{:?};", module.id, (&module.name.0, path)).as_bytes());
        }
        for (module, path) in &modules {
            // Resolution expands structures into synthetic child modules.
            // Their declarations belong to the enclosing source unit.
            let index = (1..=path.len())
                .rev()
                .find_map(|length| graph.indices.get(&path[..length]))
                .copied()
                .expect("resolved module has a source scope");
            let _time = timing::Scope::module(|| graph.units[index].path.clone());
            units.insert(module.id, index);
            let mut bytes = graph.units[index].local_key.to_vec();
            bytes
                .extend(format!("{:?}{:?}", module.parameters, module.parameter_checks).as_bytes());
            if let ModuleBody::Inline(items) = &module.body {
                for item in items {
                    if let ModuleItem::ChildModule { module } = item {
                        bytes.extend(format!("child {:?}", module.id).as_bytes());
                    } else {
                        bytes.extend(format!("{item:?}").as_bytes());
                    }
                }
            }
            let mut bindings = bindings_by_module.remove(&module.id).unwrap_or_default();
            bindings.sort_by_key(|(id, _)| id.0);
            let parameters: Vec<_> = bindings
                .iter()
                .filter(|(_, binding)| binding.parameter.is_some())
                .collect();
            // Parameters can be scheduled before the module's imported dependencies.
            // A body edit must not invalidate that unchanged initial context.
            parameter_keys.insert(
                module.id,
                fingerprint(
                    format!(
                        "{:?}:{:?}:{:?}:{:?}:{parameters:?}",
                        module.parameters,
                        module.parameter_checks,
                        module.header_source.as_ref().map(|source| &source.id),
                        (!module.parameters.is_empty()).then_some(module.span),
                    )
                    .as_bytes(),
                ),
            );
            bytes.extend(format!("{bindings:?}").as_bytes());
            let mut imports = imports_by_module.remove(&module.id).unwrap_or_default();
            imports.sort_by_key(|(id, _)| id.0);
            for (id, import) in imports {
                let mut remapping: Vec<_> = import.remapping.iter().collect();
                remapping.sort_by_key(|(id, _)| id.0);
                bytes.extend(
                    format!("{id:?}:{:?}:{:?}:{remapping:?}", import.name, import.target)
                        .as_bytes(),
                );
            }
            module_keys.insert(module.id, fingerprint(&bytes));
        }
        let module_of = |step: &CheckStep| -> ModuleId {
            match step {
                CheckStep::Parameters(id) | CheckStep::Declaration { module: id, .. } => *id,
            }
        };
        let mut last = HashMap::new();
        for (index, step) in project.order.iter().enumerate() {
            last.insert(units[&module_of(step)], index + 1);
        }
        let mut prefix = fingerprint(&layout);
        if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
            eprintln!("environment layout: {prefix:?}");
        }
        let mut checkpoints = Vec::new();
        let steps = project
            .order
            .iter()
            .enumerate()
            .map(|(index, step)| {
                let id = module_of(step);
                let mut bytes = prefix.to_vec();
                bytes.extend(match step {
                    CheckStep::Parameters(_) => parameter_keys[&id],
                    CheckStep::Declaration { .. } => module_keys[&id],
                });
                bytes.extend(format!("{step:?}").as_bytes());
                prefix = fingerprint(&bytes);
                if last[&units[&id]] == index + 1 {
                    if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
                        eprintln!(
                            "environment key {}: {:?} {:?}",
                            index + 1,
                            graph.units[units[&id]].path,
                            prefix
                        );
                    }
                    checkpoints.push((index + 1, prefix));
                }
                units[&id]
            })
            .collect();
        Self { steps, checkpoints }
    }

    pub fn save_points(&self) -> BTreeSet<usize> {
        // Bound serialization work as well as retained bytes. Lookups still try
        // every prefix, including checkpoints saved by an earlier checking batch.
        let count = self.checkpoints.len();
        let stride = count.div_ceil(32).max(1);
        self.checkpoints
            .iter()
            .enumerate()
            .filter_map(|(index, (position, _))| {
                ((index + 1) % stride == 0 || index + 1 == count).then_some(*position)
            })
            .collect()
    }

    pub fn end(&self, selected: &BTreeSet<usize>) -> usize {
        self.steps
            .iter()
            .rposition(|index| selected.contains(index))
            .map_or(0, |index| index + 1)
    }
}

/// Retention by bytes, also used for provisional checkpoints.
/// Thin densely spaced checkpoints so earlier dependency environments survive.
/// Arc payloads let a successfully checked batch transfer ownership without copying.
#[derive(Default)]
pub(crate) struct EnvironmentCache {
    entries: HashMap<Fingerprint, std::sync::Arc<[u8]>>,
    order: std::collections::VecDeque<(Fingerprint, u64)>,
    sequence: u64,
    bytes: usize,
}
impl EnvironmentCache {
    const BUDGET: usize = 64 * 1024 * 1024;

    pub fn get(&self, key: &Fingerprint) -> Option<std::sync::Arc<[u8]>> {
        self.entries.get(key).cloned()
    }

    pub fn insert(&mut self, key: Fingerprint, bytes: std::sync::Arc<[u8]>) {
        if bytes.len() > Self::BUDGET {
            return;
        }
        if let Some(previous) = self.entries.remove(&key) {
            self.bytes -= previous.len();
            self.order.retain(|(existing, _)| *existing != key);
        }
        self.bytes += bytes.len();
        self.order.push_back((key, self.sequence));
        self.sequence += 1;
        self.entries.insert(key, bytes);
        while self.bytes > Self::BUDGET {
            // Preserve coverage of the checking order, including its endpoints.
            // With only two entries, keep the newest checkpoint.
            let victim = (1..self.order.len().saturating_sub(1))
                .min_by_key(|&index| self.order[index + 1].1 - self.order[index - 1].1)
                .unwrap_or(0);
            let (key, _) = self.order.remove(victim).unwrap();
            self.bytes -= self.entries.remove(&key).unwrap().len();
        }
    }

    pub fn into_entries(mut self) -> impl Iterator<Item = (Fingerprint, std::sync::Arc<[u8]>)> {
        self.order
            .into_iter()
            .map(move |(key, _)| (key, self.entries.remove(&key).unwrap()))
    }

    pub fn bytes(&self) -> usize {
        self.bytes
    }

    pub fn clear(&mut self) {
        *self = Self::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn checkpoint_retention_is_bounded_and_replacement_updates_accounting() {
        let mut cache = EnvironmentCache::default();
        let bytes: std::sync::Arc<[u8]> = vec![0; 1024 * 1024].into();
        for index in 0..100_u8 {
            cache.insert([index; 32], bytes.clone());
        }
        assert_eq!(cache.bytes(), EnvironmentCache::BUDGET);
        assert!(cache.get(&[0; 32]).is_some());
        assert!((1..99).any(|index| cache.get(&[index; 32]).is_none()));
        assert!(cache.get(&[99; 32]).is_some());
        cache.insert([99; 32], vec![1].into());
        assert_eq!(cache.bytes(), EnvironmentCache::BUDGET - bytes.len() + 1);
        cache.clear();
        assert_eq!(cache.bytes(), 0);
    }
}
