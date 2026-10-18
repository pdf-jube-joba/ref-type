//! Restore immutable namespace tables with the sharing used by live imports.
use super::*;
use serde::{
    Deserializer,
    de::{SeqAccess, Visitor},
};

struct Maps<K, V>(FxHashMap<u64, Vec<Arc<HashMap<K, V>>>>);
impl<K, V> Default for Maps<K, V> {
    fn default() -> Self {
        Self(Default::default())
    }
}
impl<K: Eq + Hash, V: Eq + Hash> Maps<K, V> {
    fn share(&mut self, value: &mut Arc<HashMap<K, V>>) {
        // Hash table iteration order varies; equality still verifies collisions.
        let hash = value.iter().fold(0_u64, |sum, pair| {
            let mut hash = rustc_hash::FxHasher::default();
            pair.hash(&mut hash);
            sum.wrapping_add(hash.finish())
        });
        let candidates = self.0.entry(hash).or_default();
        if let Some(shared) = candidates.iter().find(|candidate| *candidate == value) {
            *value = shared.clone();
        } else {
            candidates.push(value.clone());
        }
    }
}

fn share<T: Eq + Hash>(values: &mut HashSet<Arc<T>>, value: &mut Arc<T>) {
    if let Some(shared) = values.get(value) {
        *value = shared.clone();
    } else {
        values.insert(value.clone());
    }
}

#[allow(clippy::vec_box)]
pub(super) fn deserialize<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<Box<ModuleEnv>>, D::Error> {
    struct Modules;
    impl<'de> Visitor<'de> for Modules {
        type Value = Vec<Box<ModuleEnv>>;
        fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("namespace modules")
        }
        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
            let mut names = Maps::default();
            let mut hir_names = Maps::default();
            let mut hir_items = Maps::default();
            let mut labels = HashSet::new();
            let mut constructors = HashSet::new();
            let mut modules = Vec::new();
            while let Some(mut module) = seq.next_element::<Box<ModuleEnv>>()? {
                names.share(&mut module.names);
                hir_names.share(&mut module.hir_names);
                hir_items.share(&mut module.hir_items);
                for item in &mut module.items {
                    match item {
                        ModuleItem::Definition { name, .. } | ModuleItem::Record { name, .. } => {
                            share(&mut labels, name);
                        }
                        ModuleItem::Inductive {
                            name,
                            constructor_names,
                            ..
                        }
                        | ModuleItem::ProgramInductive {
                            name,
                            constructor_names,
                            ..
                        } => {
                            share(&mut labels, name);
                            share(&mut constructors, constructor_names);
                        }
                    }
                    if let ModuleItem::ProgramInductive {
                        record_fields: Some(fields),
                        ..
                    } = item
                    {
                        share(&mut constructors, fields);
                    }
                }
                modules.push(module);
            }
            Ok(modules)
        }
    }
    deserializer.deserialize_seq(Modules)
}
