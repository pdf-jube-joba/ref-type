//! Sparse declaration slots keep stable IDs without storing each key or growing
//! a hash table containing every payload. Only small chunk pointers are rehashed.
use super::ids::{DefId, ModuleId};
use std::{collections::HashMap, ops::Index};

const CHUNK: usize = 8;
type ChunkKey = (ModuleId, u32);
type Slots<V> = Box<[Option<V>; CHUNK]>;

#[derive(Debug)]
pub(crate) struct DefinitionMap<V> {
    chunks: HashMap<ChunkKey, Slots<V>>,
    len: usize,
}

impl<V> Default for DefinitionMap<V> {
    fn default() -> Self {
        Self {
            chunks: HashMap::new(),
            len: 0,
        }
    }
}

impl<V> DefinitionMap<V> {
    fn position(key: DefId) -> (ChunkKey, usize) {
        (
            (key.module, key.index / CHUNK as u32),
            key.index as usize % CHUNK,
        )
    }

    pub fn get(&self, key: &DefId) -> Option<&V> {
        let (chunk, offset) = Self::position(*key);
        self.chunks.get(&chunk)?.get(offset)?.as_ref()
    }

    pub fn insert(&mut self, key: DefId, value: V) -> Option<V> {
        let (chunk, offset) = Self::position(key);
        let slots = self
            .chunks
            .entry(chunk)
            .or_insert_with(|| Box::new(std::array::from_fn(|_| None)));
        let previous = slots[offset].replace(value);
        self.len += usize::from(previous.is_none());
        previous
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn capacity(&self) -> usize {
        self.chunks.len() * CHUNK
    }

    pub fn iter(&self) -> Iter<'_, V> {
        Iter {
            chunks: self.chunks.iter(),
            current: None,
        }
    }
}

pub(crate) struct Iter<'a, V> {
    chunks: std::collections::hash_map::Iter<'a, ChunkKey, Slots<V>>,
    current: Option<(
        ChunkKey,
        std::iter::Enumerate<std::slice::Iter<'a, Option<V>>>,
    )>,
}

impl<'a, V> Iterator for Iter<'a, V> {
    type Item = (DefId, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(((module, chunk), slots)) = &mut self.current {
                for (offset, value) in slots.by_ref() {
                    if let Some(value) = value {
                        return Some((
                            DefId {
                                module: *module,
                                index: *chunk * CHUNK as u32 + offset as u32,
                            },
                            value,
                        ));
                    }
                }
            }
            let (&key, slots) = self.chunks.next()?;
            self.current = Some((key, slots.iter().enumerate()));
        }
    }
}

impl<'a, V> IntoIterator for &'a DefinitionMap<V> {
    type Item = (DefId, &'a V);
    type IntoIter = Iter<'a, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<V> Index<&DefId> for DefinitionMap<V> {
    type Output = V;

    fn index(&self, key: &DefId) -> &V {
        self.get(key).expect("missing declaration table key")
    }
}

impl<V> Extend<(DefId, V)> for DefinitionMap<V> {
    fn extend<T: IntoIterator<Item = (DefId, V)>>(&mut self, entries: T) {
        for (key, value) in entries {
            self.insert(key, value);
        }
    }
}

impl<V> FromIterator<(DefId, V)> for DefinitionMap<V> {
    fn from_iter<T: IntoIterator<Item = (DefId, V)>>(entries: T) -> Self {
        let mut map = Self::default();
        map.extend(entries);
        map
    }
}

impl<V: artifact::Relocate> artifact::Relocate for DefinitionMap<V> {
    fn relocate(&mut self, relocation: &mut artifact::Relocation) -> artifact::Result<()> {
        let mut relocated = Self::default();
        for ((module, chunk), slots) in std::mem::take(self).chunks {
            for (offset, value) in (*slots).into_iter().enumerate() {
                let Some(mut value) = value else { continue };
                let mut key = DefId {
                    module,
                    index: chunk * CHUNK as u32 + offset as u32,
                };
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
    use artifact::Relocate;

    #[test]
    fn sparse_slots_match_hash_map_for_growth_replacement_and_iteration() {
        let mut entries = DefinitionMap::default();
        let mut expected = HashMap::new();
        let mut state = 0x243f6a8885a308d3_u64;
        for step in 0..20_000 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let key = DefId {
                module: ModuleId((state >> 32) as u32 % 257),
                index: match step % 5 {
                    0 => u32::MAX - step % 17,
                    1 => step % 41,
                    _ => (state >> 16) as u32 % 137,
                },
            };
            assert_eq!(entries.insert(key, step), expected.insert(key, step));
            assert_eq!(entries.get(&key), expected.get(&key));
        }
        assert_eq!(entries.len(), expected.len());
        assert_eq!(
            entries
                .iter()
                .map(|(key, value)| (key, *value))
                .collect::<HashMap<_, _>>(),
            expected
        );
        for module in 0..260 {
            for index in [0, 7, 8, 15, 16, 136, 137, u32::MAX] {
                let key = DefId {
                    module: ModuleId(module),
                    index,
                };
                assert_eq!(entries.get(&key), expected.get(&key));
            }
        }
        // Sparse indices allocate one small chunk, not the preceding holes.
        assert!(entries.capacity() <= CHUNK * entries.len());
    }

    #[test]
    fn directory_growth_does_not_move_existing_payloads_or_duplicate_keys() {
        let key = DefId {
            module: ModuleId(3),
            index: u32::MAX,
        };
        let mut entries = DefinitionMap::default();
        entries.insert(key, std::sync::Arc::new(17));
        let address = &entries[&key] as *const _;
        for module in 0..4096 {
            for index in 0..24 {
                entries.insert(
                    DefId {
                        module: ModuleId(module),
                        index,
                    },
                    std::sync::Arc::new(index),
                );
            }
        }
        assert_eq!(&entries[&key] as *const _, address);
        assert_eq!(entries.capacity(), 4096 * 24 + CHUNK);
        assert_eq!(
            std::mem::size_of::<Option<std::sync::Arc<u32>>>(),
            std::mem::size_of::<std::sync::Arc<u32>>()
        );
        assert!(
            std::mem::size_of::<Slots<std::sync::Arc<u32>>>()
                < std::mem::size_of::<(DefId, std::sync::Arc<u32>)>()
        );
    }

    #[test]
    fn relocation_reindexes_modules_preserves_sparse_indices_and_rejects_collisions() {
        let mut entries: DefinitionMap<_> = (0..1024)
            .map(|module| {
                (
                    DefId {
                        module: ModuleId(module),
                        index: u32::MAX,
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
                index: u32::MAX,
            };
            let new = DefId {
                module: ModuleId(module + 4096),
                index: u32::MAX,
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
        assert_eq!(entries.len(), 0);
        assert_eq!(entries.iter().count(), 0);
    }
}
