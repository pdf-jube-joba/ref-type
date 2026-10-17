use super::*;
use artifact::{Relocate, Result};
use std::collections::HashSet;

pub(crate) struct Boundary {
    atoms: HashSet<kernel::syntax::MetaId>,
    reflections: HashSet<kernel::ids::ProgramInductiveId>,
    captures: HashSet<kernel::ids::InductiveId>,
    definitions: HashSet<kernel::ids::DefinitionId>,
}

#[derive(serde::Serialize, serde::Deserialize, Relocate)]
pub(crate) struct Export {
    pub atoms: Vec<(kernel::syntax::MetaId, Atom)>,
    reflections: Vec<(kernel::ids::ProgramInductiveId, kernel::ids::InductiveId)>,
    captures: Vec<(kernel::ids::InductiveId, (Vec<ModuleParamId>, usize))>,
    definitions: Vec<(kernel::ids::DefinitionId, DefinitionView)>,
}

/// Index table keys once; payloads are traversed only when a key is reached.
pub(crate) struct Reachability<'a> {
    export: &'a Export,
    entries: rustc_hash::FxHashMap<artifact::Identity, Vec<(u8, usize)>>,
    visited: HashSet<(u8, artifact::Identity)>,
}
impl Reachability<'_> {
    pub(crate) fn extend(
        &mut self,
        identities: &[artifact::Identity],
        references: &mut artifact::Relocation,
    ) -> Result<()> {
        for id in identities {
            for &(table, index) in self.entries.get(id).into_iter().flatten() {
                if !self.visited.insert((table, id.clone())) {
                    continue;
                }
                match table {
                    0 => self.export.atoms[index].1.clone().relocate(references)?,
                    1 => self.export.reflections[index]
                        .1
                        .clone()
                        .relocate(references)?,
                    2 => self.export.captures[index].1.clone().relocate(references)?,
                    3 => self.export.definitions[index]
                        .1
                        .clone()
                        .relocate(references)?,
                    _ => unreachable!("raw arena table"),
                }
            }
        }
        Ok(())
    }
}

impl Arena {
    pub(crate) fn boundary(&self) -> Boundary {
        Boundary {
            atoms: self.atoms.borrow().keys.keys().copied().collect(),
            reflections: self.datatype_reflections.borrow().keys().copied().collect(),
            captures: self.inductive_captures.borrow().keys().copied().collect(),
            definitions: self.definitions.borrow().keys().copied().collect(),
        }
    }
    pub(crate) fn export_since(&self, base: &Boundary) -> Export {
        Export {
            atoms: self
                .atoms
                .borrow()
                .keys
                .iter()
                .filter(|(k, _)| !base.atoms.contains(k))
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            reflections: self
                .datatype_reflections
                .borrow()
                .iter()
                .filter(|(k, _)| !base.reflections.contains(k))
                .map(|(k, v)| (*k, *v))
                .collect(),
            captures: self
                .inductive_captures
                .borrow()
                .iter()
                .filter(|(k, _)| !base.captures.contains(k))
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
            definitions: self
                .definitions
                .borrow()
                .iter()
                .filter(|(k, _)| !base.definitions.contains(k))
                .map(|(k, v)| (*k, v.clone()))
                .collect(),
        }
    }
    pub(crate) fn import_export(&mut self, export: Export) -> Result<()> {
        let atoms = self.atoms.get_mut();
        for (id, atom) in export.atoms {
            if let Some(previous) = atoms.keys.get(&id) {
                if previous != &atom {
                    return Err(artifact::Error("conflicting imported raw atom".into()));
                }
                continue;
            }
            atoms.ids.insert(atom.clone(), id);
            atoms.keys.insert(id, atom);
        }
        self.datatype_reflections
            .get_mut()
            .extend(export.reflections);
        self.inductive_captures.get_mut().extend(export.captures);
        self.definitions.get_mut().extend(export.definitions);
        Ok(())
    }
}

impl Export {
    /// These vectors encode keyed tables, not source or binder order.
    pub(crate) fn canonicalize(&mut self) {
        fn identity<T: Relocate + Copy>(mut id: T) -> artifact::Identity {
            let mut relocation = artifact::Relocation::collecting();
            id.relocate(&mut relocation).expect("collect identity");
            relocation
                .identities()
                .next()
                .expect("table identity")
                .clone()
        }
        self.atoms.sort_by_key(|(id, _)| identity(*id));
        self.reflections.sort_by_key(|(id, _)| id.0);
        self.captures.sort_by_key(|(id, _)| id.0);
        self.definitions.sort_by_key(|(id, _)| identity(*id));
    }

    pub(crate) fn reachability(&self) -> Result<Reachability<'_>> {
        let _phase = crate::profiling::Phase::start("artifact.arena-index");
        let mut traversal = Reachability {
            export: self,
            entries: rustc_hash::FxHashMap::default(),
            visited: HashSet::new(),
        };
        fn index<K: Relocate + Clone>(
            entries: &mut rustc_hash::FxHashMap<artifact::Identity, Vec<(u8, usize)>>,
            table: u8,
            keys: impl Iterator<Item = K>,
        ) -> Result<()> {
            for (position, mut key) in keys.enumerate() {
                let mut collector = artifact::Relocation::collecting();
                key.relocate(&mut collector)?;
                let id = collector.into_identities().into_iter().next().unwrap();
                entries.entry(id).or_default().push((table, position));
            }
            Ok(())
        }
        index(
            &mut traversal.entries,
            0,
            self.atoms.iter().map(|(key, _)| *key),
        )?;
        index(
            &mut traversal.entries,
            1,
            self.reflections.iter().map(|(key, _)| *key),
        )?;
        index(
            &mut traversal.entries,
            2,
            self.captures.iter().map(|(key, _)| *key),
        )?;
        index(
            &mut traversal.entries,
            3,
            self.definitions.iter().map(|(key, _)| *key),
        )?;
        Ok(traversal)
    }

    pub(crate) fn retain_reachable(
        &mut self,
        identities: &std::collections::BTreeSet<artifact::Identity>,
    ) {
        fn retained<T: Relocate + Clone>(
            value: &T,
            identities: &std::collections::BTreeSet<artifact::Identity>,
        ) -> bool {
            let mut collector = artifact::Relocation::collecting();
            value
                .clone()
                .relocate(&mut collector)
                .expect("collect table identity");
            collector.identities().any(|id| identities.contains(id))
        }
        self.atoms.retain(|(id, _)| retained(id, identities));
        self.reflections.retain(|(id, _)| retained(id, identities));
        self.captures.retain(|(id, _)| retained(id, identities));
        self.definitions.retain(|(id, _)| retained(id, identities));
    }

    /// Inference atoms not reachable from retained package data are transient.
    pub(crate) fn retain_reachable_atoms(
        &mut self,
        identities: &std::collections::BTreeSet<artifact::Identity>,
    ) -> Result<()> {
        self.atoms.retain(|(id, _)| {
            let mut r = artifact::Relocation::collecting();
            let mut id = *id;
            id.relocate(&mut r).expect("identity collection");
            r.identities().any(|id| identities.contains(id))
        });
        if self
            .atoms
            .iter()
            .any(|(_, atom)| matches!(atom, Atom::Meta(..)))
        {
            return Err(artifact::Error(
                "unresolved frontend metavariable in package export".into(),
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::raw::ids::ModuleId;
    use artifact::Identity;
    use std::collections::BTreeSet;

    fn identity<T: Relocate + Clone>(value: &T) -> Identity {
        let mut collector = artifact::Relocation::collecting();
        value.clone().relocate(&mut collector).unwrap();
        collector.into_identities().into_iter().next().unwrap()
    }

    #[test]
    fn indexed_arena_reachability_matches_full_scan_across_all_metadata_tables() {
        let arena = Arena::default();
        let mut export = arena.export_since(&arena.boundary());
        let meta: kernel::syntax::MetaId =
            postcard::from_bytes(&postcard::to_allocvec(&(1u64, 2u32)).unwrap()).unwrap();
        let definition: kernel::ids::DefinitionId =
            postcard::from_bytes(&postcard::to_allocvec(&(1u64, 3u32)).unwrap()).unwrap();
        let reflected = kernel::ids::InductiveId(40);
        let datatype = kernel::ids::ProgramInductiveId(41);
        export.atoms.push((
            meta,
            Atom::Definition(DefId {
                module: ModuleId(42),
                index: 2,
            }),
        ));
        export.reflections.push((datatype, reflected));
        export.captures.push((
            reflected,
            (
                vec![ModuleParamId {
                    module: ModuleId(43),
                    position: 4,
                }],
                1,
            ),
        ));
        export.definitions.push((
            definition,
            DefinitionView {
                source: Some(DefId {
                    module: ModuleId(44),
                    index: 5,
                }),
                contextual: false,
                captures: vec![],
                body: arena.core.bound(0),
            },
        ));
        // This table entry must stay unreachable even though its key is indexed.
        export.captures.push((
            kernel::ids::InductiveId(45),
            (
                vec![ModuleParamId {
                    module: ModuleId(46),
                    position: 6,
                }],
                1,
            ),
        ));
        let roots = BTreeSet::from([identity(&meta), identity(&datatype), identity(&definition)]);
        let mut expected = roots.clone();
        let mut visited = HashSet::new();
        loop {
            let before = expected.len();
            let mut references = artifact::Relocation::collecting();
            macro_rules! scan {
                ($table:expr, $entries:expr) => {
                    for (key, value) in $entries {
                        let id = identity(key);
                        if expected.contains(&id) && visited.insert(($table, id)) {
                            value.clone().relocate(&mut references).unwrap();
                        }
                    }
                };
            }
            scan!(0, &export.atoms);
            scan!(1, &export.reflections);
            scan!(2, &export.captures);
            scan!(3, &export.definitions);
            expected.extend(references.into_identities());
            if expected.len() == before {
                break;
            }
        }
        let mut traversal = export.reachability().unwrap();
        let mut actual = roots;
        let mut pending: Vec<_> = actual.iter().cloned().collect();
        while !pending.is_empty() {
            let mut references = artifact::Relocation::collecting();
            traversal.extend(&pending, &mut references).unwrap();
            pending.clear();
            for id in references.into_identities() {
                if actual.insert(id.clone()) {
                    pending.push(id);
                }
            }
        }
        assert_eq!(actual, expected);
        assert!(actual.contains(&identity(&reflected)));
        assert!(actual.contains(&Identity::scalar("raw.module", 43)));
        assert!(!actual.contains(&Identity::scalar("raw.module", 46)));
        // Repeated frontiers do not repeat metadata payload traversal.
        let mut references = artifact::Relocation::collecting();
        traversal
            .extend(&actual.into_iter().collect::<Vec<_>>(), &mut references)
            .unwrap();
        assert!(references.into_identities().is_empty());
    }
}
