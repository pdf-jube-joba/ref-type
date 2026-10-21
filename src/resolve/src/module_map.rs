//! Persistent overlays for specialized front-end namespace identities.
use crate::hir::ModuleId;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

#[path = "module_map_checkpoint.rs"]
mod checkpoint;
pub(crate) use checkpoint::{MapForest, RestoredMaps};
use std::{collections::HashMap, sync::Arc};

#[derive(artifact::Relocate, Debug, Clone, Default)]
pub struct ModuleMap {
    entries: Arc<HashMap<ModuleId, ModuleId>>,
    parent: Option<Arc<Self>>,
    composition: Option<(Arc<Self>, Arc<Self>)>,
}

impl ModuleMap {
    pub(crate) fn fork(&self) -> Self {
        if self.entries.is_empty() && self.composition.is_none() {
            return self.clone();
        }
        Self {
            entries: Arc::default(),
            parent: Some(Arc::new(self.clone())),
            composition: None,
        }
    }

    /// Compose immutable environments without copying their namespace tables.
    pub(crate) fn after(&self, previous: &Self) -> Self {
        if previous.is_empty() {
            return self.clone();
        }
        if self.is_empty() {
            return previous.clone();
        }
        Self {
            composition: Some((Arc::new(self.clone()), Arc::new(previous.clone()))),
            ..Self::default()
        }
    }

    pub fn get(&self, key: &ModuleId) -> Option<&ModuleId> {
        fn lookup<'a>(
            map: &'a ModuleMap,
            key: ModuleId,
            memo: &mut rustc_hash::FxHashMap<(*const ModuleMap, ModuleId), Option<&'a ModuleId>>,
        ) -> Option<&'a ModuleId> {
            if let Some(value) = map.entries.get(&key) {
                return Some(value);
            }
            let address = (map as *const _, key);
            if let Some(&value) = memo.get(&address) {
                return value;
            }
            let result = if let Some((next, previous)) = &map.composition {
                match lookup(previous, key, memo) {
                    Some(value) => lookup(next, *value, memo).or(Some(value)),
                    None => lookup(next, key, memo),
                }
            } else {
                map.parent
                    .as_deref()
                    .and_then(|parent| lookup(parent, key, memo))
            };
            memo.insert(address, result);
            result
        }
        if let Some(value) = self.entries.get(key) {
            return Some(value);
        }
        lookup(self, *key, &mut rustc_hash::FxHashMap::default())
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty() && self.parent.is_none() && self.composition.is_none()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&ModuleId, &ModuleId)> {
        let mut pending = vec![self];
        let mut visited = rustc_hash::FxHashSet::default();
        let mut tables = Vec::new();
        while let Some(map) = pending.pop() {
            if !visited.insert(map as *const Self) {
                continue;
            }
            tables.push(map.entries.as_ref());
            if let Some(parent) = map.parent.as_deref() {
                pending.push(parent);
            }
            if let Some((next, previous)) = &map.composition {
                pending.extend([next.as_ref(), previous.as_ref()]);
            }
        }
        let mut seen = rustc_hash::FxHashSet::default();
        tables
            .into_iter()
            .flat_map(|table| table.keys())
            .filter(move |key| seen.insert(**key))
            .map(|key| (key, self.get(key).expect("key in namespace map")))
    }

    pub(crate) fn insert(&mut self, key: ModuleId, value: ModuleId) {
        Arc::make_mut(&mut self.entries).insert(key, value);
    }

    pub(crate) fn values_mut(&mut self) -> impl Iterator<Item = &mut ModuleId> {
        if self.parent.is_some() || self.composition.is_some() {
            self.entries = Arc::new(self.iter().map(|(&k, &v)| (k, v)).collect());
            self.parent = None;
            self.composition = None;
        }
        Arc::make_mut(&mut self.entries).values_mut()
    }

    pub(crate) fn owned_len(&self) -> usize {
        self.entries.len()
    }
}

impl Serialize for ModuleMap {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        MapForest(vec![self]).serialize(serializer)
    }
}
impl<'de> Deserialize<'de> for ModuleMap {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let mut maps = RestoredMaps::deserialize(deserializer)?.0;
        if maps.len() != 1 {
            return Err(serde::de::Error::custom("expected one namespace map"));
        }
        Ok(maps.pop().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn composed_imports_keep_original_and_intermediate_names() {
        let mut original = ModuleMap::default();
        original.insert(ModuleId(1), ModuleId(2));
        let mut instance = ModuleMap::default();
        instance.insert(ModuleId(2), ModuleId(3));
        instance.insert(ModuleId(4), ModuleId(5));
        let composed = instance.after(&original);
        assert_eq!(composed.get(&ModuleId(1)), Some(&ModuleId(3)));
        assert_eq!(composed.get(&ModuleId(2)), Some(&ModuleId(3)));
        assert_eq!(composed.get(&ModuleId(4)), Some(&ModuleId(5)));
        assert_eq!(composed.iter().count(), 3);
        let mut child = composed.fork();
        child.insert(ModuleId(1), ModuleId(6));
        assert_eq!(child.get(&ModuleId(1)), Some(&ModuleId(6)));
        assert_eq!(composed.get(&ModuleId(1)), Some(&ModuleId(3)));
        assert_eq!(original.get(&ModuleId(1)), Some(&ModuleId(2)));
    }

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
