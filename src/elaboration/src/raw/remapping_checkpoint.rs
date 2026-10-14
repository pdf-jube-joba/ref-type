//! Preserve sharing between the namespace maps of different specializations.
use super::{
    environment::{DeclarationRemapping, RemappingId, RemappingSnapshotId},
    ids::*,
    shared_map::{MapForest, RestoredMaps},
};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Checkpoints encode live and frozen roots in one forest so staging preserves
/// the Arc identities used by portable dependency references.
#[derive(Debug, Clone, artifact::Relocate)]
pub(crate) struct Tables {
    pub(crate) live: Vec<DeclarationRemapping>,
    pub(crate) snapshots: std::cell::RefCell<Vec<DeclarationRemapping>>,
}

impl Default for Tables {
    fn default() -> Self {
        let builtin = DeclarationRemapping::default();
        Self {
            live: vec![builtin.clone()],
            snapshots: std::cell::RefCell::new(vec![builtin]),
        }
    }
}

impl std::ops::Deref for Tables {
    type Target = Vec<DeclarationRemapping>;
    fn deref(&self) -> &Self::Target {
        &self.live
    }
}

impl std::ops::DerefMut for Tables {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.live
    }
}

impl Serialize for Tables {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let _cost = timing::costs::Scope::enter("query.serialize-remappings");
        let snapshots = self.snapshots.borrow();
        let roots = || self.live.iter().chain(snapshots.iter());
        (
            self.live.len(),
            MapForest(roots().map(|map| &map.module_ids).collect()),
            MapForest(roots().map(|map| &map.definition_ids).collect()),
            MapForest(roots().map(|map| &map.inductive_ids).collect()),
            MapForest(roots().map(|map| &map.program_inductive_ids).collect()),
        )
            .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Tables {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let (live_count, modules, definitions, inductives, datatypes): (
            usize,
            RestoredMaps<ModuleId>,
            RestoredMaps<DefId>,
            RestoredMaps<InductiveId>,
            RestoredMaps<ProgramInductiveId>,
        ) = Deserialize::deserialize(deserializer)?;
        if [definitions.0.len(), inductives.0.len(), datatypes.0.len()]
            .into_iter()
            .any(|length| length != modules.0.len())
            || live_count == 0
            || live_count >= modules.0.len()
        {
            return Err(serde::de::Error::custom("inconsistent remapping roots"));
        }
        let mut live: Vec<_> = modules
            .0
            .into_iter()
            .zip(definitions.0)
            .zip(inductives.0)
            .zip(datatypes.0)
            .map(
                |(((module_ids, definition_ids), inductive_ids), program_inductive_ids)| {
                    DeclarationRemapping {
                        module_ids,
                        definition_ids,
                        inductive_ids,
                        program_inductive_ids,
                    }
                },
            )
            .collect();
        let snapshots = std::cell::RefCell::new(live.split_off(live_count));
        Ok(Self { live, snapshots })
    }
}

/// Portable remapping roots whose inherited map nodes remain dependency refs.
#[derive(Serialize, Deserialize, artifact::Relocate)]
pub(crate) struct Export {
    pub ids: Vec<RemappingId>,
    pub snapshots: Vec<RemappingSnapshotId>,
    modules: super::shared_map::exports::Export<ModuleId>,
    definitions: super::shared_map::exports::Export<DefId>,
    inductives: super::shared_map::exports::Export<InductiveId>,
    datatypes: super::shared_map::exports::Export<ProgramInductiveId>,
}
impl Export {
    pub(crate) fn empty() -> Self {
        Self {
            ids: Vec::new(),
            snapshots: Vec::new(),
            modules: super::shared_map::exports::Export::empty(),
            definitions: super::shared_map::exports::Export::empty(),
            inductives: super::shared_map::exports::Export::empty(),
            datatypes: super::shared_map::exports::Export::empty(),
        }
    }

    pub(crate) fn canonicalize(&mut self) -> artifact::Result<()> {
        if self.snapshots.len() != self.ids.len() {
            return Err(artifact::Error(
                "inconsistent remapping snapshot roots".into(),
            ));
        }
        let mut order: Vec<_> = (0..self.ids.len()).collect();
        order.sort_unstable_by_key(|&index| self.ids[index].0);
        self.modules.reorder_roots(&order)?;
        self.definitions.reorder_roots(&order)?;
        self.inductives.reorder_roots(&order)?;
        self.datatypes.reorder_roots(&order)?;
        self.snapshots = order.iter().map(|&index| self.snapshots[index]).collect();
        self.ids = order.into_iter().map(|index| self.ids[index]).collect();
        Ok(())
    }

    /// Retain the owned remapping roots reached by exported declarations.
    pub(crate) fn capture_selected(
        maps: &[DeclarationRemapping],
        start: usize,
        selected: &std::collections::BTreeSet<usize>,
        snapshot_dependency_roots: &[(RemappingSnapshotId, &DeclarationRemapping)],
        own_snapshot_ids: Vec<RemappingSnapshotId>,
    ) -> artifact::Result<Self> {
        if start > maps.len() {
            return Err(artifact::Error(
                "invalid remapping ownership boundary".into(),
            ));
        }
        let ids: Vec<_> = selected.range(start..).copied().map(RemappingId).collect();
        if ids.iter().any(|id| id.0 >= maps.len()) {
            return Err(artifact::Error(
                "invalid selected remapping identity".into(),
            ));
        }
        if own_snapshot_ids.len() != ids.len() {
            return Err(artifact::Error(
                "inconsistent remapping snapshot roots".into(),
            ));
        }
        if ids.is_empty() {
            return Ok(Self::empty());
        }
        macro_rules! capture {
            ($field:ident) => {{
                let roots: Vec<_> = ids.iter().map(|id| &maps[id.0].$field).collect();
                let dependencies: Vec<_> = snapshot_dependency_roots
                    .iter()
                    .map(|(id, map)| (*id, &map.$field))
                    .collect();
                super::shared_map::exports::Export::capture(&roots, &dependencies)?
            }};
        }
        Ok(Self {
            modules: capture!(module_ids),
            definitions: capture!(definition_ids),
            inductives: capture!(inductive_ids),
            datatypes: capture!(program_inductive_ids),
            ids,
            snapshots: own_snapshot_ids,
        })
    }
    pub(crate) fn restore(
        self,
        existing: &[(RemappingSnapshotId, &DeclarationRemapping)],
    ) -> artifact::Result<Vec<(RemappingId, RemappingSnapshotId, DeclarationRemapping)>> {
        macro_rules! restore {
            ($forest:ident, $field:ident) => {{
                let dependencies: Vec<_> = existing
                    .iter()
                    .map(|(id, map)| (*id, &map.$field))
                    .collect();
                self.$forest.restore(&dependencies)?
            }};
        }
        let modules = restore!(modules, module_ids);
        let definitions = restore!(definitions, definition_ids);
        let inductives = restore!(inductives, inductive_ids);
        let datatypes = restore!(datatypes, program_inductive_ids);
        if [
            self.snapshots.len(),
            modules.len(),
            definitions.len(),
            inductives.len(),
            datatypes.len(),
        ]
        .into_iter()
        .any(|len| len != self.ids.len())
        {
            return Err(artifact::Error(
                "inconsistent imported remapping root counts".into(),
            ));
        }
        Ok(self
            .ids
            .into_iter()
            .zip(self.snapshots)
            .zip(modules)
            .zip(definitions)
            .zip(inductives)
            .zip(datatypes)
            .map(
                |(
                    ((((id, snapshot), module_ids), definition_ids), inductive_ids),
                    program_inductive_ids,
                )| {
                    (
                        id,
                        snapshot,
                        DeclarationRemapping {
                            module_ids,
                            definition_ids,
                            inductive_ids,
                            program_inductive_ids,
                        },
                    )
                },
            )
            .collect())
    }
}
