//! Shared namespace maps retain composition without copying either operand.
use serde::{Deserialize, Deserializer, Serialize, Serializer, ser::SerializeMap};
use std::{collections::HashMap, hash::Hash, sync::Arc};

pub trait IdLookup<K> {
    fn get(&self, key: &K) -> Option<&K>;
    fn is_empty(&self) -> bool;
}

impl<K: Eq + Hash> IdLookup<K> for HashMap<K, K> {
    fn get(&self, key: &K) -> Option<&K> {
        HashMap::get(self, key)
    }
    fn is_empty(&self) -> bool {
        HashMap::is_empty(self)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct SharedMap<K> {
    entries: Arc<HashMap<K, K>>,
    base: Option<(Arc<Self>, Arc<Self>)>,
}

impl<K> Default for SharedMap<K> {
    fn default() -> Self {
        Self {
            entries: Arc::new(HashMap::new()),
            base: None,
        }
    }
}

impl<K: Copy + Eq + Hash> IdLookup<K> for SharedMap<K> {
    fn get(&self, key: &K) -> Option<&K> {
        if let Some(value) = self.entries.get(key) {
            return Some(value);
        }
        let (next, previous) = self.base.as_ref()?;
        if let Some(intermediate) = previous.get(key) {
            next.get(intermediate).or(Some(intermediate))
        } else {
            next.get(key)
        }
    }
    fn is_empty(&self) -> bool {
        self.entries.is_empty()
            && self
                .base
                .as_ref()
                .is_none_or(|(next, previous)| next.is_empty() && previous.is_empty())
    }
}

impl<K: Copy + Eq + Hash> SharedMap<K> {
    pub(crate) fn get(&self, key: &K) -> Option<&K> {
        IdLookup::get(self, key)
    }
    fn keys(&self) -> impl Iterator<Item = &K> {
        let mut pending = vec![self];
        let mut visited = rustc_hash::FxHashSet::default();
        let mut tables = Vec::new();
        let mut entries = rustc_hash::FxHashSet::default();
        while let Some(map) = pending.pop() {
            if !visited.insert(map as *const Self) {
                continue;
            }
            if !map.entries.is_empty() && entries.insert(Arc::as_ptr(&map.entries)) {
                tables.push(map.entries.as_ref());
            }
            if let Some((next, previous)) = &map.base {
                pending.push(next);
                pending.push(previous);
            }
        }
        let mut seen = rustc_hash::FxHashSet::default();
        tables
            .into_iter()
            .flat_map(|map| map.keys())
            .filter(move |key| seen.insert(**key))
    }
    pub(crate) fn iter(&self) -> impl Iterator<Item = (&K, &K)> {
        self.keys()
            .map(|key| (key, self.get(key).expect("key in a composed map")))
    }
    pub(crate) fn len(&self) -> usize {
        if self.base.is_none() {
            self.entries.len()
        } else {
            self.keys().count()
        }
    }
    pub(crate) fn capacity(&self) -> usize {
        self.entries.capacity()
    }
    fn make_mut(&mut self) -> &mut HashMap<K, K> {
        if self.base.is_some() {
            self.entries = Arc::new(self.iter().map(|(&k, &v)| (k, v)).collect());
            self.base = None;
        }
        Arc::make_mut(&mut self.entries)
    }
    pub(crate) fn insert(&mut self, key: K, value: K) -> Option<K> {
        self.make_mut().insert(key, value)
    }
    #[cfg(test)]
    pub(crate) fn clear(&mut self) {
        *self = Self::default();
    }
    pub(crate) fn values_mut(&mut self) -> impl Iterator<Item = &mut K> {
        self.make_mut().values_mut()
    }
    pub(crate) fn retain(&mut self, f: impl FnMut(&K, &mut K) -> bool) {
        self.make_mut().retain(f);
    }
    pub(crate) fn shrink_to_fit(&mut self) {
        self.make_mut().shrink_to_fit();
    }

    pub(crate) fn after(&self, previous: &Self) -> Self {
        if previous.is_empty() {
            return self.clone();
        }
        if self.is_empty() {
            return previous.clone();
        }
        Self {
            entries: Arc::new(HashMap::new()),
            base: Some((Arc::new(self.clone()), Arc::new(previous.clone()))),
        }
    }
}

// Keep the cache wire format as one ordinary map. Serialization visits shared
// layers without allocating a flattened copy for every inherited namespace.
impl<K: Copy + Eq + Hash + Serialize> Serialize for SharedMap<K> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (key, value) in self.iter() {
            map.serialize_entry(key, value)?;
        }
        map.end()
    }
}
impl<'de, K: Copy + Eq + Hash + Deserialize<'de>> Deserialize<'de> for SharedMap<K> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Self {
            entries: Arc::new(HashMap::deserialize(deserializer)?),
            base: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_compositions_resolve_old_and_new_names() {
        let mut map = SharedMap::default();
        for key in 1u32..128 {
            let mut previous = SharedMap::default();
            previous.insert(key, key - 1);
            map = map.after(&previous);
        }
        for key in 1..128 {
            assert_eq!(map.get(&key), Some(&0));
        }
        assert_eq!(map.get(&128), None);
        assert_eq!(map.len(), 127);
        let saved = map.clone();
        map.insert(127, 128);
        assert_eq!(saved.get(&127), Some(&0));
        assert_eq!(map.get(&127), Some(&128));
    }

    #[test]
    fn composition_preserves_overrides_identity_and_snapshot_isolation() {
        let mut shared = SharedMap::default();
        let mut expected = HashMap::new();
        for key in 0u32..32 {
            shared.insert(key, key + 1);
            expected.insert(key, key + 1);
        }
        for round in 0..16 {
            let snapshot = shared.clone();
            let snapshot_values = expected.clone();
            let mut previous = SharedMap::default();
            previous.insert(round, 31 - round);
            previous.insert(64 + round, round);
            let mut composed = expected.clone();
            for (&source, &middle) in previous.iter() {
                composed.insert(source, expected.get(&middle).copied().unwrap_or(middle));
            }
            shared = shared.after(&previous);
            for key in 0..96 {
                assert_eq!(
                    shared.get(&key).copied().unwrap_or(key),
                    composed.get(&key).copied().unwrap_or(key)
                );
            }
            shared.insert(95, round);
            composed.insert(95, round);
            assert_eq!(
                snapshot
                    .iter()
                    .map(|(&k, &v)| (k, v))
                    .collect::<HashMap<_, _>>(),
                snapshot_values
            );
            expected = composed;
        }
        let bytes = postcard::to_allocvec(&shared).unwrap();
        let ordinary: HashMap<u32, u32> = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(ordinary, expected);
        let restored: SharedMap<u32> = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(
            restored
                .iter()
                .map(|(&k, &v)| (k, v))
                .collect::<HashMap<_, _>>(),
            expected
        );
    }
}
