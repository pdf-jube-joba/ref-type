//! Unclassified elaboration syntax and raw evaluation. Never a kernel certificate.
pub mod calculus;
pub mod dependencies;
pub mod derivation;
pub mod environment;
pub mod exp;
pub mod inductive;
pub mod namespaces;
pub mod printing;
pub mod program;
pub mod program_calculus;
pub mod program_definitions;
pub mod program_derivation;
pub mod program_inductive;
pub mod reflection;
pub mod sort;
pub mod traversal;
pub mod utils;
pub mod ids {
    /// Identity local to one elaboration unit.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct MetaVarId(pub u32);

    impl MetaVarId {
        pub fn index(self) -> usize {
            self.0 as usize
        }
    }

    pub use kernel::ids::*;
}
#[cfg(test)]
mod tests;
