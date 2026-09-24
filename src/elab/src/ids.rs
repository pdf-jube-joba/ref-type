//! Identities used by elaboration terms.
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

/// Identity local to one elaboration unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MetaVarId(pub u32);
impl MetaVarId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
