//! Explicit identity relocation at package import/export boundaries.
pub use artifact_derive::Relocate;
pub mod canonical;
mod names;
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    hash::{BuildHasher, Hash},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(pub String);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;

#[derive(
    Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum Identity {
    Scalar {
        space: String,
        value: u64,
    },
    Pair {
        space: String,
        arena: u64,
        index: u32,
    },
}
impl Identity {
    pub fn scalar(space: &str, value: u64) -> Self {
        Self::Scalar {
            space: space.into(),
            value,
        }
    }
    pub fn pair(space: &str, value: (u64, u32)) -> Self {
        Self::Pair {
            space: space.into(),
            arena: value.0,
            index: value.1,
        }
    }
    pub fn space(&self) -> &str {
        match self {
            Self::Scalar { space, .. } | Self::Pair { space, .. } => space,
        }
    }
}

#[derive(Default, Clone)]
pub struct Relocation {
    mappings: HashMap<Identity, Identity>,
    collected: BTreeSet<Identity>,
    collecting: bool,
    shared: HashMap<(std::any::TypeId, usize), std::rc::Rc<dyn std::any::Any>>,
}
impl Relocation {
    pub fn collecting() -> Self {
        Self {
            collecting: true,
            ..Self::default()
        }
    }
    pub fn is_collecting(&self) -> bool {
        self.collecting
    }
    pub fn identities(&self) -> impl Iterator<Item = &Identity> {
        self.collected.iter()
    }
    /// Finish collection and release the memoized shared payloads.
    pub fn into_identities(self) -> BTreeSet<Identity> {
        self.collected
    }
    pub fn mappings(&self) -> impl Iterator<Item = (&Identity, &Identity)> {
        self.mappings.iter()
    }
    pub fn insert_identity(&mut self, old: Identity, new: Identity) -> Result<()> {
        if old.space() != new.space() {
            return Err(Error("identity space mismatch".into()));
        }
        if let Some(previous) = self.mappings.get(&old) {
            if previous != &new {
                return Err(Error(format!("conflicting identity {old:?}")));
            }
        }
        self.mappings.insert(old, new);
        Ok(())
    }
    pub fn lookup(&self, old: &Identity) -> Option<&Identity> {
        self.mappings.get(old)
    }
    pub fn insert_pair(&mut self, space: &str, old: (u64, u32), new: (u64, u32)) -> Result<()> {
        self.insert_identity(Identity::pair(space, old), Identity::pair(space, new))
    }
    pub fn get_pair(&self, space: &str, old: (u64, u32)) -> Option<(u64, u32)> {
        match self.lookup(&Identity::pair(space, old))? {
            Identity::Pair { arena, index, .. } => Some((*arena, *index)),
            _ => None,
        }
    }
    pub fn pair(&mut self, space: &str, old: (u64, u32)) -> Result<(u64, u32)> {
        if self.collecting {
            self.collected.insert(Identity::pair(space, old));
            return Ok(old);
        }
        self.get_pair(space, old)
            .ok_or_else(|| Error(format!("missing {space} identity {old:?}")))
    }
    pub fn insert(&mut self, space: &str, old: u64, new: u64) -> Result<()> {
        self.insert_identity(Identity::scalar(space, old), Identity::scalar(space, new))
    }
    pub fn get(&self, space: &str, old: u64) -> Option<u64> {
        match self.lookup(&Identity::scalar(space, old))? {
            Identity::Scalar { value, .. } => Some(*value),
            _ => None,
        }
    }
    pub fn id(&mut self, space: &str, old: u64) -> Result<u64> {
        if self.collecting {
            self.collected.insert(Identity::scalar(space, old));
            return Ok(old);
        }
        self.get(space, old)
            .ok_or_else(|| Error(format!("missing {space} identity {old}")))
    }
}

pub trait Relocate {
    fn relocate(&mut self, relocation: &mut Relocation) -> Result<()>;
}
macro_rules! inert {
    ($($ty:ty),*) => {$(impl Relocate for $ty {
        fn relocate(&mut self, _: &mut Relocation) -> Result<()> { Ok(()) }
    })*};
}
inert!(
    (),
    bool,
    u8,
    u16,
    u32,
    u64,
    usize,
    i32,
    i64,
    &'static str,
    std::path::PathBuf
);
impl Relocate for String {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        names::relocate(self, r)
    }
}
impl<T: Relocate> Relocate for Vec<T> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        for v in self {
            v.relocate(r)?;
        }
        Ok(())
    }
}
impl<T: Relocate, const N: usize> Relocate for [T; N] {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        for value in self {
            value.relocate(r)?;
        }
        Ok(())
    }
}
impl<T: Relocate> Relocate for Option<T> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        if let Some(v) = self {
            v.relocate(r)?;
        }
        Ok(())
    }
}
impl<T: Relocate + ?Sized> Relocate for Box<T> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        (**self).relocate(r)
    }
}
// Hold both versions so allocator address reuse cannot alias an earlier entry.
// A shared DAG is visited once and retains its sharing after relocation.
impl<T: Relocate + Clone + 'static> Relocate for std::sync::Arc<T> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        let key = (
            std::any::TypeId::of::<Self>(),
            std::sync::Arc::as_ptr(self) as usize,
        );
        if let Some(pair) = r.shared.get(&key) {
            *self = pair
                .downcast_ref::<(Self, Self)>()
                .expect("shared Arc type")
                .1
                .clone();
            return Ok(());
        }
        if r.is_collecting() {
            // Pin and mark the original allocation before visiting a temporary
            // payload. Collection must not build a replacement shared graph.
            r.shared
                .insert(key, std::rc::Rc::new((self.clone(), self.clone())));
            return (**self).clone().relocate(r);
        }
        let original = self.clone();
        std::sync::Arc::make_mut(self).relocate(r)?;
        r.shared
            .insert(key, std::rc::Rc::new((original, self.clone())));
        Ok(())
    }
}
impl<T: Relocate + Clone + 'static> Relocate for std::sync::Arc<[T]> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        let key = (
            std::any::TypeId::of::<Self>(),
            std::sync::Arc::as_ptr(self) as *const T as usize,
        );
        if let Some(pair) = r.shared.get(&key) {
            *self = pair
                .downcast_ref::<(Self, Self)>()
                .expect("shared slice type")
                .1
                .clone();
            return Ok(());
        }
        if r.is_collecting() {
            r.shared
                .insert(key, std::rc::Rc::new((self.clone(), self.clone())));
            return self.as_ref().to_vec().relocate(r);
        }
        let original = self.clone();
        for value in std::sync::Arc::make_mut(self) {
            value.relocate(r)?;
        }
        r.shared
            .insert(key, std::rc::Rc::new((original, self.clone())));
        Ok(())
    }
}
impl<T: Relocate + Clone + 'static> Relocate for std::rc::Rc<T> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        let key = (
            std::any::TypeId::of::<Self>(),
            std::rc::Rc::as_ptr(self) as usize,
        );
        if let Some(pair) = r.shared.get(&key) {
            *self = pair
                .downcast_ref::<(Self, Self)>()
                .expect("shared Rc type")
                .1
                .clone();
            return Ok(());
        }
        if r.is_collecting() {
            r.shared
                .insert(key, std::rc::Rc::new((self.clone(), self.clone())));
            return (**self).clone().relocate(r);
        }
        let original = self.clone();
        std::rc::Rc::make_mut(self).relocate(r)?;
        r.shared
            .insert(key, std::rc::Rc::new((original, self.clone())));
        Ok(())
    }
}
impl<T: Relocate> Relocate for std::cell::RefCell<T> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        self.get_mut().relocate(r)
    }
}
impl<T: Relocate + Copy> Relocate for std::cell::Cell<T> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        self.get_mut().relocate(r)
    }
}
impl<T: Relocate> Relocate for std::cell::OnceCell<T> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        if let Some(v) = self.get_mut() {
            v.relocate(r)?;
        }
        Ok(())
    }
}
impl<K: Relocate + Eq + Hash, V: Relocate, S: BuildHasher + Default> Relocate for HashMap<K, V, S> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        for (mut k, mut v) in std::mem::take(self) {
            k.relocate(r)?;
            v.relocate(r)?;
            if self.insert(k, v).is_some() {
                return Err(Error("duplicate relocated map key".into()));
            }
        }
        Ok(())
    }
}
impl<K: Relocate + Eq + Hash, S: BuildHasher + Default> Relocate for HashSet<K, S> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        for mut k in std::mem::take(self) {
            k.relocate(r)?;
            self.insert(k);
        }
        Ok(())
    }
}
impl<K: Relocate + Ord, V: Relocate> Relocate for BTreeMap<K, V> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        for (mut k, mut v) in std::mem::take(self) {
            k.relocate(r)?;
            v.relocate(r)?;
            self.insert(k, v);
        }
        Ok(())
    }
}
impl<K: Relocate + Ord> Relocate for BTreeSet<K> {
    fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
        for mut k in std::mem::take(self) {
            k.relocate(r)?;
            self.insert(k);
        }
        Ok(())
    }
}
macro_rules! tuples {
    ($($T:ident:$i:tt),*) => {
        impl<$($T: Relocate),*> Relocate for ($($T,)*) {
            fn relocate(&mut self, r: &mut Relocation) -> Result<()> { $(self.$i.relocate(r)?;)* Ok(()) }
        }
    };
}
tuples!(A:0, B:1);
tuples!(A:0, B:1, C:2);
tuples!(A:0, B:1, C:2, D:3);
tuples!(A:0, B:1, C:2, D:3, E:4);

#[macro_export]
macro_rules! identity {
    ($ty:ty, $space:literal) => {
        impl $crate::Relocate for $ty {
            fn relocate(&mut self, r: &mut $crate::Relocation) -> $crate::Result<()> {
                self.0 = r
                    .id($space, self.0 as u64)?
                    .try_into()
                    .map_err(|_| $crate::Error(concat!($space, " identity overflow").into()))?;
                Ok(())
            }
        }
    };
}

#[cfg(test)]
mod sharing_tests {
    use super::*;
    use std::sync::Arc;
    #[derive(Clone, Debug, PartialEq)]
    struct Id(u64);
    identity!(Id, "test");

    #[test]
    fn collection_keeps_shared_allocations_and_visits_each_payload_once() {
        use std::{cell::Cell, rc::Rc};
        #[derive(Clone)]
        struct Counted {
            id: Id,
            visits: Rc<Cell<usize>>,
        }
        impl Relocate for Counted {
            fn relocate(&mut self, r: &mut Relocation) -> Result<()> {
                self.visits.set(self.visits.get() + 1);
                self.id.relocate(r)
            }
        }
        let visits = Rc::new(Cell::new(0));
        let value = Counted {
            id: Id(7),
            visits: visits.clone(),
        };
        let leaf = Arc::new(value.clone());
        let branch = Arc::new(vec![leaf.clone(), leaf.clone()]);
        let local = Rc::new(value.clone());
        let slice: Arc<[Counted]> = Arc::from(vec![value]);
        let mut roots = (
            vec![branch.clone(), branch.clone()],
            vec![local.clone(), local.clone()],
            vec![slice.clone(), slice.clone()],
        );
        let mut collector = Relocation::collecting();
        roots.relocate(&mut collector).unwrap();
        assert_eq!(visits.get(), 3);
        assert!(Arc::ptr_eq(&roots.0[0], &branch));
        assert!(Arc::ptr_eq(&roots.0[0][0], &leaf));
        assert!(Rc::ptr_eq(&roots.1[0], &local));
        assert!(Arc::ptr_eq(&roots.2[0], &slice));
        assert_eq!(
            collector.into_identities(),
            BTreeSet::from([Identity::scalar("test", 7)])
        );
        assert_eq!(leaf.id, Id(7));
    }

    #[test]
    fn relocated_shared_dag_preserves_aliases_and_original_values() {
        let leaf = Arc::new(vec![Id(7)]);
        let branch = Arc::new(vec![leaf.clone(), leaf.clone()]);
        let mut roots = vec![branch.clone(), branch.clone()];
        let mut relocation = Relocation::default();
        relocation.insert("test", 7, 11).unwrap();
        roots.relocate(&mut relocation).unwrap();
        assert!(Arc::ptr_eq(&roots[0], &roots[1]));
        assert!(Arc::ptr_eq(&roots[0][0], &roots[0][1]));
        assert_eq!(&*roots[0][0], &vec![Id(11)]);
        assert_eq!(&*leaf, &vec![Id(7)]);
        assert_eq!(relocation.shared.len(), 2);
    }
}
