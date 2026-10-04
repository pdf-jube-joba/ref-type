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
}

impl<T> Default for ContextInterner<T> {
    fn default() -> Self {
        Self {
            extensions: FxHashMap::default(),
            bindings: Vec::new(),
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
        bindings
            .into_iter()
            .fold(ContextId::default(), |parent, binding| {
                self.push(parent, binding)
            })
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    pub(crate) fn truncate(&mut self, mark: usize) {
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
