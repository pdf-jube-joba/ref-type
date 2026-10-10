//! Persistent overlays for specialized front-end namespace identities.
use crate::hir::ModuleId;
use std::{collections::HashMap, sync::Arc};

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Default)]
pub struct ModuleMap {
    entries: Arc<HashMap<ModuleId, ModuleId>>,
    parent: Option<Arc<Self>>,
}

impl ModuleMap {
    pub(crate) fn fork(&self) -> Self {
        if self.entries.is_empty() {
            return self.clone();
        }
        Self {
            entries: Arc::default(),
            parent: Some(Arc::new(self.clone())),
        }
    }

    pub fn get(&self, key: &ModuleId) -> Option<&ModuleId> {
        let mut layer = self;
        loop {
            if let Some(value) = layer.entries.get(key) {
                return Some(value);
            }
            layer = layer.parent.as_deref()?;
        }
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty() && self.parent.as_ref().is_none_or(|map| map.is_empty())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&ModuleId, &ModuleId)> {
        let layers = std::iter::successors(Some(self), |map| map.parent.as_deref());
        let mut seen = rustc_hash::FxHashSet::default();
        layers
            .flat_map(|map| map.entries.iter())
            .filter(move |(key, _)| seen.insert(**key))
    }

    pub(crate) fn insert(&mut self, key: ModuleId, value: ModuleId) {
        Arc::make_mut(&mut self.entries).insert(key, value);
    }

    pub(crate) fn values_mut(&mut self) -> impl Iterator<Item = &mut ModuleId> {
        if self.parent.is_some() {
            self.entries = Arc::new(self.iter().map(|(&k, &v)| (k, v)).collect());
            self.parent = None;
        }
        Arc::make_mut(&mut self.entries).values_mut()
    }

    pub(crate) fn owned_len(&self) -> usize {
        self.entries.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn overlays_preserve_shadowing_and_snapshot_isolation() {
        let mut original = ModuleMap::default();
        original.insert(ModuleId(1), ModuleId(2));
        let mut child = original.fork();
        child.insert(ModuleId(1), ModuleId(3));
        child.insert(ModuleId(4), ModuleId(5));
        let saved = child.clone();
        for value in child.values_mut() {
            value.0 += 10;
        }
        assert_eq!(original.get(&ModuleId(1)), Some(&ModuleId(2)));
        assert_eq!(saved.get(&ModuleId(1)), Some(&ModuleId(3)));
        assert_eq!(saved.iter().count(), 2);
        assert_eq!(child.get(&ModuleId(1)), Some(&ModuleId(13)));
        assert_eq!(child.get(&ModuleId(4)), Some(&ModuleId(15)));
        assert_eq!(child.get(&ModuleId(7)), None);
    }
}
