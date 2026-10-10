//! Small caches shared by immutable syntax arenas.
use rustc_hash::FxHashMap;
use std::hash::Hash;

/// Records writes during a scratch operation so cleanup only visits changed entries.
#[derive(Debug)]
pub(crate) struct Cache<K, V> {
    entries: FxHashMap<K, V>,
    writes: Vec<K>,
    tracking: bool,
}

impl<K, V> Default for Cache<K, V> {
    fn default() -> Self {
        Self {
            entries: FxHashMap::default(),
            writes: Vec::new(),
            tracking: false,
        }
    }
}

impl<K: Copy + Eq + Hash, V> Cache<K, V> {
    pub fn get(&self, key: &K) -> Option<&V> {
        self.entries.get(key)
    }

    pub fn insert(&mut self, key: K, value: V) {
        // These tables memoize immutable judgements; entries can be recomputed.
        // Bound long-lived conversions and bound summaries as well as ordinary
        // inference, without evicting the arena's canonical syntax identities.
        if self.entries.len() >= 1 << 20 {
            self.clear();
            timing::costs::count("kernel.cache-recycles", || 1);
        }
        if self.tracking {
            self.writes.push(key);
        }
        self.entries.insert(key, value);
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
                .is_some_and(|value| !keep(&key, value))
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
        let mut cache = Cache::default();
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
}
