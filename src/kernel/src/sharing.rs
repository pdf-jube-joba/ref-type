//! Small caches shared by immutable syntax arenas.
use rustc_hash::FxHashMap;
use std::{cell::Cell, hash::Hash};

#[derive(Debug)]
struct Entry<V> {
    value: V,
    reused: Cell<bool>,
}

/// Records writes during a scratch operation so cleanup only visits changed entries.
#[derive(Debug)]
pub(crate) struct Cache<K, V, const LIMIT: usize = { 1 << 20 }> {
    entries: FxHashMap<K, Entry<V>>,
    writes: Vec<K>,
    tracking: bool,
}

impl<K, V, const LIMIT: usize> Default for Cache<K, V, LIMIT> {
    fn default() -> Self {
        Self {
            entries: FxHashMap::default(),
            writes: Vec::new(),
            tracking: false,
        }
    }
}

impl<K: Copy + Eq + Hash, V, const LIMIT: usize> Cache<K, V, LIMIT> {
    pub fn get(&self, key: &K) -> Option<&V> {
        let entry = self.entries.get(key)?;
        entry.reused.set(true);
        Some(&entry.value)
    }

    pub fn insert(&mut self, key: K, value: V) {
        // Keep judgements that have actually been reused, including shared
        // dependencies from earlier modules. Leave at least a quarter of the
        // budget free so a hot working set cannot trigger a sweep per insert.
        if self.entries.len() >= LIMIT && !self.entries.contains_key(&key) {
            let budget = LIMIT - LIMIT.div_ceil(4);
            let mut retained = 0;
            self.entries.retain(|_, entry| {
                let keep = entry.reused.replace(false) && retained < budget;
                retained += usize::from(keep);
                keep
            });
            timing::costs::count("kernel.cache-recycles", || 1);
            timing::costs::count("kernel.cache-retained", || retained as u64);
        }
        if self.tracking {
            self.writes.push(key);
        }
        match self.entries.entry(key) {
            std::collections::hash_map::Entry::Occupied(mut entry) => entry.get_mut().value = value,
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(Entry {
                    value,
                    reused: Cell::new(false),
                });
            }
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn clear(&mut self) {
        self.entries.clear();
        self.writes.clear();
    }

    pub fn begin_scratch(&mut self) {
        assert!(!self.tracking, "nested cache scratch operation");
        self.tracking = true;
    }

    pub fn finish_scratch(&mut self, mut keep: impl FnMut(&K, &V) -> bool) {
        self.tracking = false;
        for key in self.writes.drain(..) {
            if self
                .entries
                .get(&key)
                .is_some_and(|entry| !keep(&key, &entry.value))
            {
                self.entries.remove(&key);
            }
        }
    }
}

/// The empty telescope has ID zero. Extensions share their complete prefix.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContextId(u32);

impl ContextId {
    pub(crate) fn within(self, bindings: usize) -> bool {
        self.0 as usize <= bindings
    }
}

#[derive(Debug)]
pub struct ContextInterner<T> {
    extensions: FxHashMap<(ContextId, T), ContextId>,
    bindings: Vec<(ContextId, T)>,
    last: Vec<(T, ContextId)>,
}

impl<T> Default for ContextInterner<T> {
    fn default() -> Self {
        Self {
            extensions: FxHashMap::default(),
            bindings: Vec::new(),
            last: Vec::new(),
        }
    }
}

impl<T: Clone + Eq + Hash> ContextInterner<T> {
    pub fn push(&mut self, parent: ContextId, binding: T) -> ContextId {
        *self
            .extensions
            .entry((parent, binding.clone()))
            .or_insert_with(|| {
                self.bindings.push((parent, binding));
                ContextId(u32::try_from(self.bindings.len()).expect("too many contexts"))
            })
    }

    pub fn parent(&self, context: ContextId) -> ContextId {
        self.bindings[context.0 as usize - 1].0
    }

    pub fn intern(&mut self, bindings: impl IntoIterator<Item = T>) -> ContextId {
        // Frontend traversals repeatedly request the same context or extend its
        // prefix. Compare that prefix directly instead of hashing every binding.
        let mut parent = ContextId::default();
        let mut len = 0;
        for binding in bindings {
            parent = if let Some((_, id)) = self.last.get(len).filter(|(b, _)| *b == binding) {
                *id
            } else {
                self.last.truncate(len);
                let id = self.push(parent, binding.clone());
                self.last.push((binding, id));
                id
            };
            len += 1;
        }
        self.last.truncate(len);
        parent
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    pub(crate) fn truncate(&mut self, mark: usize) {
        self.last
            .truncate(self.last.partition_point(|(_, id)| id.within(mark)));
        for binding in self.bindings.drain(mark..) {
            self.extensions.remove(&binding);
        }
    }

    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interning_reuses_prefixes_across_extensions_and_sibling_contexts() {
        let mut contexts = ContextInterner::default();
        let a = contexts.intern([1, 2, 3]);
        assert_eq!(contexts.intern([1, 2, 3]), a);
        let b = contexts.intern([1, 2]);
        assert_eq!(contexts.parent(a), b);
        let sibling = contexts.intern([1, 4, 3]);
        assert_ne!(sibling, a);
        assert_eq!(contexts.intern([1, 2, 3]), a);
        let extended = contexts.push(a, 5);
        assert_eq!(contexts.intern([1, 2, 3, 5]), extended);
        assert_eq!(contexts.intern([]), ContextId::default());
        assert_eq!(contexts.intern([1, 2, 3]), a);
    }

    #[test]
    fn interning_rebuilds_prefixes_after_scratch_rollback() {
        let mut contexts = ContextInterner::default();
        let prefix = contexts.intern([1]);
        let mark = contexts.len();
        let discarded = contexts.intern([1, 2, 3]);
        contexts.truncate(mark);
        let middle = contexts.push(prefix, 4);
        let sibling = contexts.push(middle, 5);
        assert_eq!(sibling, discarded);
        let rebuilt = contexts.intern([1, 2, 3]);
        assert_ne!(rebuilt, sibling);
        assert_eq!(contexts.parent(contexts.parent(rebuilt)), prefix);
        assert_eq!(contexts.intern([1]), prefix);
    }

    #[test]
    fn scratch_cleanup_visits_writes_including_replaced_entries() {
        let mut cache = Cache::<_, _>::default();
        for key in 0..10_000 {
            cache.insert(key, true);
        }
        cache.begin_scratch();
        cache.insert(5, false);
        cache.insert(10_000, false);
        cache.insert(10_001, true);
        let mut visited = 0;
        cache.finish_scratch(|_, &live| {
            visited += 1;
            live
        });
        assert_eq!(visited, 3);
        assert_eq!(cache.len(), 10_000);
        assert_eq!(cache.get(&4), Some(&true));
        assert_eq!(cache.get(&5), None);
        assert_eq!(cache.get(&10_000), None);
        assert_eq!(cache.get(&10_001), Some(&true));

        cache.begin_scratch();
        cache.insert(10_002, false);
        cache.clear();
        cache.insert(10_003, true);
        cache.finish_scratch(|_, &live| live);
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(&10_003), Some(&true));
    }

    #[test]
    fn eviction_keeps_reused_dependencies_and_respects_scratch_lifetimes() {
        let mut cache = Cache::<_, _, 4>::default();
        for key in 0..4 {
            cache.insert(key, key);
        }
        assert_eq!(cache.get(&0), Some(&0));
        cache.begin_scratch();
        cache.insert(4, 4);
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.get(&0), Some(&0));
        assert_eq!(cache.get(&1), None);
        cache.insert(0, 10);
        cache.finish_scratch(|_, &value| value < 4);
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn hot_cache_leaves_room_and_replacement_does_not_evict() {
        let mut cache = Cache::<_, _, 4>::default();
        for key in 0..4 {
            cache.insert(key, key);
            assert_eq!(cache.get(&key), Some(&key));
        }
        cache.insert(0, 10);
        assert_eq!(cache.len(), 4);
        assert_eq!(cache.get(&1), Some(&1));
        cache.insert(4, 4);
        assert_eq!(cache.len(), 4);
        assert_eq!(cache.get(&4), Some(&4));
        cache.insert(5, 5);
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.get(&4), Some(&4));
    }
}
