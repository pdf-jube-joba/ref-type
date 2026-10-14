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

    pub(crate) fn collect_reachable(
        &self,
        identities: &std::collections::BTreeSet<artifact::Identity>,
        visited: &mut std::collections::BTreeSet<(u8, artifact::Identity)>,
        references: &mut artifact::Relocation,
    ) -> Result<()> {
        fn visit<K: Relocate + Clone, V: Relocate + Clone>(
            table: u8,
            entries: &[(K, V)],
            identities: &std::collections::BTreeSet<artifact::Identity>,
            visited: &mut std::collections::BTreeSet<(u8, artifact::Identity)>,
            references: &mut artifact::Relocation,
        ) -> Result<()> {
            for (key, value) in entries {
                let mut collector = artifact::Relocation::collecting();
                key.clone().relocate(&mut collector)?;
                let id = collector.into_identities().into_iter().next().unwrap();
                if identities.contains(&id) && visited.insert((table, id)) {
                    value.clone().relocate(references)?;
                }
            }
            Ok(())
        }
        visit(0, &self.atoms, identities, visited, references)?;
        visit(1, &self.reflections, identities, visited, references)?;
        visit(2, &self.captures, identities, visited, references)?;
        visit(3, &self.definitions, identities, visited, references)
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
