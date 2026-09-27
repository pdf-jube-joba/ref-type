//! Small caches shared by immutable syntax arenas.
use rustc_hash::FxHashMap;
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

    pub(crate) fn bindings(&self) -> impl Iterator<Item = &T> {
        self.extensions.keys().map(|(_, binding)| binding)
    }

    pub fn is_empty(&self) -> bool {
        self.parents.is_empty()
    }
}
