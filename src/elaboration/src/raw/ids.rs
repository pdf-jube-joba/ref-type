//! Frontend identities for module membership and elaboration.
pub use kernel::ids::SymbolId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(pub u32);
impl ModuleId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleParamId {
    pub module: ModuleId,
    pub position: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId {
    pub module: ModuleId,
    pub index: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InductiveId {
    pub module: ModuleId,
    pub index: u32,
}

/// Stable identity of a CBPV value datatype.  Its Set reflection is stored as
/// a separate [`InductiveId`] in the environment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProgramInductiveId {
    pub module: ModuleId,
    pub index: u32,
}

/// Identity of an elaboration-time metavariable.
///
/// Used by the front-end's unclassified elaboration syntax. The kernel's indexed node families
/// contain no metavariable constructor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MetaVarId(pub u32);

impl MetaVarId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

// Encoding is owned by the frontend; the kernel treats these numbers as opaque.
impl From<DefId> for kernel::ids::GlobalId {
    fn from(id: DefId) -> Self {
        Self((u64::from(id.module.0) << 32) | u64::from(id.index))
    }
}
impl From<InductiveId> for kernel::ids::InductiveId {
    fn from(id: InductiveId) -> Self {
        Self((u64::from(id.module.0) << 32) | u64::from(id.index))
    }
}
impl From<ProgramInductiveId> for kernel::ids::ProgramInductiveId {
    fn from(id: ProgramInductiveId) -> Self {
        Self((u64::from(id.module.0) << 32) | u64::from(id.index))
    }
}
