//! Declaration tables grow one small shard at a time instead of duplicating a
//! multi-gigabyte table during reallocation. Checkpoints retain their wire format.
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
    ops::Index,
};

const SHARDS: usize = 256;

#[derive(Debug)]
pub(crate) struct ShardedMap<K, V> {
    shards: Box<[HashMap<K, V>; SHARDS]>,
    len: usize,
}

impl<K, V> Default for ShardedMap<K, V> {
    fn default() -> Self {
        Self {
            shards: Box::new(std::array::from_fn(|_| HashMap::new())),
            len: 0,
        }
    }
}

impl<K: Eq + Hash, V> ShardedMap<K, V> {
    fn shard(key: &K) -> usize {
        let mut hash = rustc_hash::FxHasher::default();
        key.hash(&mut hash);
        (hash.finish() as usize) & (SHARDS - 1)
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.shards[Self::shard(key)].get(key)
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let previous = self.shards[Self::shard(&key)].insert(key, value);
        self.len += usize::from(previous.is_none());
        previous
    }
}

impl<K, V> ShardedMap<K, V> {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn capacity(&self) -> usize {
        self.shards.iter().map(HashMap::capacity).sum()
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            shards: self.shards.iter(),
            current: None,
        }
    }
}

pub(crate) struct Iter<'a, K, V> {
    shards: std::slice::Iter<'a, HashMap<K, V>>,
    current: Option<std::collections::hash_map::Iter<'a, K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(item) = self.current.as_mut().and_then(Iterator::next) {
                return Some(item);
            }
            self.current = Some(self.shards.next()?.iter());
        }
    }
}

impl<'a, K, V> IntoIterator for &'a ShardedMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<K: Eq + Hash, V> Index<&K> for ShardedMap<K, V> {
    type Output = V;

    fn index(&self, key: &K) -> &V {
        self.get(key).expect("missing declaration table key")
    }
}

impl<K: Eq + Hash, V> Extend<(K, V)> for ShardedMap<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, entries: T) {
        for (key, value) in entries {
            self.insert(key, value);
        }
    }
}

impl<K: Eq + Hash, V> FromIterator<(K, V)> for ShardedMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(entries: T) -> Self {
        let mut map = Self::default();
        map.extend(entries);
        map
    }
}

impl<K: artifact::Relocate + Eq + Hash, V: artifact::Relocate> artifact::Relocate
    for ShardedMap<K, V>
{
    fn relocate(&mut self, relocation: &mut artifact::Relocation) -> artifact::Result<()> {
        let mut relocated = Self::default();
        for shard in self.shards.iter_mut() {
            for (mut key, mut value) in std::mem::take(shard) {
                key.relocate(relocation)?;
                value.relocate(relocation)?;
                if relocated.insert(key, value).is_some() {
                    return Err(artifact::Error("duplicate relocated map key".into()));
                }
            }
        }
        *self = relocated;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::raw::ids::{DefId, ModuleId};
    use artifact::Relocate;

    #[test]
    fn growth_and_replacement_preserve_every_declaration() {
        let mut entries = ShardedMap::default();
        for module in 0..2048 {
            for index in 0..8 {
                let key = DefId {
                    module: ModuleId(module),
                    index,
                };
                assert_eq!(entries.insert(key, module + index), None);
            }
        }
        assert_eq!(entries.len(), 16384);
        for (&key, &value) in &entries {
            assert_eq!(value, key.module.0 + key.index);
        }
        // A complete growth affects only a small fraction of the whole table.
        let largest = entries.shards.iter().map(HashMap::capacity).max().unwrap();
        assert!(largest * 16 < entries.capacity());
        let key = DefId {
            module: ModuleId(512),
            index: 3,
        };
        assert_eq!(entries.insert(key, 999), Some(515));
        assert_eq!(entries.len(), 16384);
        assert_eq!(entries[&key], 999);
        assert_eq!(entries.iter().count(), entries.len());
    }

    #[test]
    fn relocation_rehashes_keys_across_shards_and_rejects_collisions() {
        let mut entries: ShardedMap<_, _> = (0..1024)
            .map(|module| {
                (
                    DefId {
                        module: ModuleId(module),
                        index: 0,
                    },
                    module,
                )
            })
            .collect();
        let mut relocation = artifact::Relocation::default();
        for module in 0..1024 {
            relocation
                .insert("raw.module", module, module + 4096)
                .unwrap();
        }
        entries.relocate(&mut relocation).unwrap();
        for module in 0..1024 {
            let old = DefId {
                module: ModuleId(module),
                index: 0,
            };
            let new = DefId {
                module: ModuleId(module + 4096),
                index: 0,
            };
            assert_eq!(entries.get(&old), None);
            assert_eq!(entries.get(&new), Some(&module));
        }
        assert_eq!(entries.len(), 1024);
        let mut collision = artifact::Relocation::default();
        for module in 4096..5120 {
            collision.insert("raw.module", module, 0).unwrap();
        }
        assert!(entries.relocate(&mut collision).is_err());
    }
}
