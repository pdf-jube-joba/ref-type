//! Semantic identities and the environment owning their checked representations.
use super::*;

#[derive(Debug, Default)]
pub struct KernelEnvironment {
    pub(super) kernel: ke::Environment,
    pub(super) ids: IdMap,
}

impl KernelEnvironment {
    pub fn transfer(&self) -> Result<Self, String> {
        self.transfer_with_stats()
            .map(|(environment, _)| environment)
    }

    pub fn transfer_with_stats(&self) -> Result<(Self, kernel::transfer::TransferStats), String> {
        let (kernel, relocation) = self.kernel.transfer()?;
        let ids = IdMap {
            definitions: self
                .ids
                .definitions
                .iter()
                .filter_map(|(&raw, old)| relocation.globals.get(old).map(|&new| (raw, new)))
                .collect(),
            inductives: self
                .ids
                .inductives
                .iter()
                .filter_map(|(&raw, old)| relocation.inductives.get(old).map(|&new| (raw, new)))
                .collect(),
            datatypes: self
                .ids
                .datatypes
                .iter()
                .filter_map(|(&raw, old)| relocation.datatypes.get(old).map(|&new| (raw, new)))
                .collect(),
            parameters: self.ids.parameters.clone(),
        };
        Ok((Self { kernel, ids }, relocation.stats))
    }

    pub fn definition(&self, id: DefId) -> Option<&ke::Definition> {
        let id = *self.ids.definitions.get(&id)?;
        self.kernel
            .definition(id)
            .or_else(|| self.kernel.definition_template(id))
    }
}

impl std::ops::Deref for KernelEnvironment {
    type Target = ke::Environment;
    fn deref(&self) -> &Self::Target {
        &self.kernel
    }
}

impl std::ops::DerefMut for KernelEnvironment {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.kernel
    }
}

#[derive(Debug, Default)]
pub(super) struct IdMap {
    definitions: FxHashMap<DefId, kernel::ids::GlobalId>,
    inductives: FxHashMap<InductiveId, kernel::ids::InductiveId>,
    datatypes: FxHashMap<ProgramInductiveId, kernel::ids::ProgramInductiveId>,
    pub(super) parameters: FxHashMap<ModuleParamId, usize>,
}

impl Lowerer<'_> {
    pub(super) fn definition_id(&mut self, id: DefId) -> kernel::ids::GlobalId {
        *self
            .ids
            .definitions
            .entry(id)
            .or_insert_with(|| self.kernel.fresh_global_id())
    }

    pub(super) fn inductive_id(&mut self, id: InductiveId) -> kernel::ids::InductiveId {
        *self
            .ids
            .inductives
            .entry(id)
            .or_insert_with(|| self.kernel.fresh_inductive_id())
    }

    pub(super) fn datatype_id(
        &mut self,
        id: ProgramInductiveId,
    ) -> kernel::ids::ProgramInductiveId {
        *self
            .ids
            .datatypes
            .entry(id)
            .or_insert_with(|| self.kernel.fresh_datatype_id())
    }

    pub(super) fn parameter_id(&mut self, id: ModuleParamId) -> usize {
        self.ids.parameters[&id]
    }

    pub(super) fn checked_definition(&mut self, id: DefId) -> Option<&ke::Definition> {
        let id = self.definition_id(id);
        self.kernel
            .definition(id)
            .or_else(|| self.kernel.definition_template(id))
    }
}
