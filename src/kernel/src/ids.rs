//! Stable identifiers shared by expressions and the environment.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

impl SymbolId {
    pub const ANONYMOUS: Self = Self(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

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
pub struct ModuleInstanceId {
    pub owner: ModuleId,
    pub local: u32,
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
/// Used by the front-end's unclassified elaboration syntax. None of the
/// kernel's nine indexed node families admits a metavariable constructor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MetaVarId(pub u32);

impl MetaVarId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
