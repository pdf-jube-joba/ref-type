//! Stable identifiers shared by expressions and the environment.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

impl SymbolId {
    pub const ANONYMOUS: Self = Self(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

// Nominal identities are allocated by their owning checking environment.
macro_rules! identity {
    ($($name:ident),*) => {$(
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name {
            pub(crate) owner: crate::syntax::ArenaId,
            pub(crate) index: u32,
        }
    )*};
}
identity!(GlobalId, InductiveId, ProgramInductiveId);
