//! Stable identifiers shared by expressions and the environment.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

impl SymbolId {
    pub const ANONYMOUS: Self = Self(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Caller-owned label for a declaration or annotated expression.
/// It has no effect on typing or conversion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GlobalId(pub u64);

/// Opaque nominal identity of a logical inductive type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InductiveId(pub u64);

/// Opaque nominal identity of a Program datatype.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProgramInductiveId(pub u64);
