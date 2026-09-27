//! Stable identifiers shared by expressions and the environment.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

impl SymbolId {
    pub const ANONYMOUS: Self = Self(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Handle into the owning environment's immutable definition arena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefinitionId {
    pub(crate) arena: u64,
    pub(crate) index: u32,
}

/// Opaque nominal identity of a logical inductive type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InductiveId(pub u64);

/// Opaque nominal identity of a Program datatype.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProgramInductiveId(pub u64);

/// Rigid parameter identity used while closing a module declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParameterId(pub u64);
