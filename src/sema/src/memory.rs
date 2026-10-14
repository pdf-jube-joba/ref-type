//! Query generations bound retained history while callers keep their own Arc handles.
use std::{cell::Cell, collections::HashMap, hash::Hash};

pub(crate) struct GenerationCache<K, V> {
    entries: HashMap<K, (Cell<u64>, V)>,
    generation: u64,
}
impl<K, V> Default for GenerationCache<K, V> {
    fn default() -> Self {
        Self {
            entries: HashMap::new(),
            generation: 0,
        }
    }
}
impl<K: Eq + Hash, V> GenerationCache<K, V> {
    /// Retain the current and previous query's working sets.
    pub fn next_generation(&mut self) {
        self.generation += 1;
        self.entries
            .retain(|_, (generation, _)| generation.get().saturating_add(1) >= self.generation);
    }
    pub fn get(&self, key: &K) -> Option<&V> {
        self.entries.get(key).map(|(generation, value)| {
            generation.set(self.generation);
            value
        })
    }
    pub fn insert(&mut self, key: K, value: V) {
        self.entries
            .insert(key, (Cell::new(self.generation), value));
    }
    pub fn clear(&mut self) {
        self.entries.clear();
    }
    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.entries.values().map(|(_, value)| value)
    }
}

/// These counts describe database-owned retention, not caller-owned snapshots,
/// result Arcs, or the live resolver/checker arenas of an active query.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MemoryCacheStats {
    pub source_entries: usize,
    pub source_bytes: usize,
    pub parse_entries: usize,
    pub parse_source_bytes: usize,
    pub module_results: usize,
    pub query_results: usize,
    pub package_results: usize,
    pub compressed_environment_bytes: usize,
}
