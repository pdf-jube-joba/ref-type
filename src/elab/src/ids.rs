//! Identities used by elaboration terms.
pub use kernel::ids::*;

/// Identity local to one elaboration unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MetaVarId(pub u32);
impl MetaVarId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
