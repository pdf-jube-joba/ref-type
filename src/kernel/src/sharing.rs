//! Small caches shared by immutable syntax arenas.
use rustc_hash::FxHashMap;
use std::cell::Cell;
use std::hash::Hash;

/// The empty telescope has ID zero. Extensions share their complete prefix.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContextId(u32);

#[derive(Debug)]
pub struct ContextInterner<T> {
    extensions: FxHashMap<(ContextId, T), ContextId>,
    parents: Vec<ContextId>,
}

impl<T> Default for ContextInterner<T> {
    fn default() -> Self {
        Self {
            extensions: FxHashMap::default(),
            parents: Vec::new(),
        }
    }
}

impl<T: Eq + Hash> ContextInterner<T> {
    pub fn push(&mut self, parent: ContextId, binding: T) -> ContextId {
        *self.extensions.entry((parent, binding)).or_insert_with(|| {
            self.parents.push(parent);
            ContextId(u32::try_from(self.parents.len()).expect("too many contexts"))
        })
    }

    pub fn parent(&self, context: ContextId) -> ContextId {
        self.parents[context.0 as usize - 1]
    }

    pub fn intern(&mut self, bindings: impl IntoIterator<Item = T>) -> ContextId {
        bindings
            .into_iter()
            .fold(ContextId::default(), |parent, binding| {
                self.push(parent, binding)
            })
    }

    pub fn len(&self) -> usize {
        self.parents.len()
    }

    pub fn is_empty(&self) -> bool {
        self.parents.is_empty()
    }
}

/// Results created during a scratch allocation scope are promoted only when
/// both their keys and values remain valid after the scope is discarded.
#[derive(Debug)]
pub(crate) struct ScopedCache<K, V> {
    permanent: FxHashMap<K, V>,
    temporary: FxHashMap<K, V>,
    scoped: bool,
}

impl<K, V> Default for ScopedCache<K, V> {
    fn default() -> Self {
        Self {
            permanent: FxHashMap::default(),
            temporary: FxHashMap::default(),
            scoped: false,
        }
    }
}

impl<K: Eq + Hash, V> ScopedCache<K, V> {
    pub(crate) fn get(&self, key: &K) -> Option<&V> {
        self.temporary.get(key).or_else(|| self.permanent.get(key))
    }

    pub(crate) fn insert(&mut self, key: K, value: V) {
        if self.scoped {
            &mut self.temporary
        } else {
            &mut self.permanent
        }
        .insert(key, value);
    }

    pub(crate) fn clear(&mut self) {
        self.permanent.clear();
        self.temporary.clear();
    }

    pub(crate) fn len(&self) -> usize {
        self.permanent.len() + self.temporary.len()
    }

    pub(crate) fn keys(&self) -> impl Iterator<Item = &K> {
        self.permanent.keys().chain(self.temporary.keys())
    }

    pub(crate) fn begin_scope(&mut self) {
        assert!(!self.scoped);
        self.scoped = true;
    }

    pub(crate) fn finish_scope(&mut self, mut retain: impl FnMut(&K, &V) -> bool) {
        for (key, value) in self.temporary.drain() {
            if retain(&key, &value) {
                self.permanent.insert(key, value);
            }
        }
        self.scoped = false;
    }

    pub(crate) fn discard_scope(&mut self) {
        self.temporary.clear();
        self.scoped = false;
    }
}

/// A cached maximum free de Bruijn index, with distinct unknown and closed states.
#[derive(Debug)]
pub struct LooseBound(Cell<usize>);

impl Default for LooseBound {
    fn default() -> Self {
        Self(Cell::new(usize::MAX))
    }
}

impl LooseBound {
    pub fn get(&self) -> Option<Option<usize>> {
        match self.0.get() {
            usize::MAX => None,
            n if n == usize::MAX - 1 => Some(None),
            n => Some(Some(n)),
        }
    }

    pub fn set(&self, bound: Option<usize>) {
        // Extreme indices remain valid inputs; leave them uncached rather than
        // confusing them with the two sentinel states.
        self.0.set(match bound {
            None => usize::MAX - 1,
            Some(n) if n < usize::MAX - 1 => n,
            Some(_) => usize::MAX,
        });
    }
}
