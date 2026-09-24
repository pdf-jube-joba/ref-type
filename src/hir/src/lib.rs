//! Semantic syntax between parsing and elaboration.
//! Proof blocks remain structured until their expected type is known.
pub use syntax::{
    Identifier, InductiveKind, MacroSeqAtom, MacroToken, MetaKind, Sort, SourceFile, SourceId,
    SourceLocation, SourceSpan, TokenMatchPattern,
};
/// A definition-site scope interpreted by the semantic resolver.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(pub u32);

/// A reference into the owning semantic environment's capture table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CapturedId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaOrigin {
    Source,
    Template,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SurfaceMeta {
    pub kind: MetaKind,
    pub origin: MetaOrigin,
}

impl SurfaceMeta {
    pub fn implicit() -> Self {
        Self::source(MetaKind::Implicit)
    }
    pub fn goal() -> Self {
        Self::source(MetaKind::Goal)
    }
    pub fn named(number: u32) -> Self {
        Self::source(MetaKind::Named(number))
    }
    fn source(kind: MetaKind) -> Self {
        Self {
            kind,
            origin: MetaOrigin::Source,
        }
    }
}

mod lower;
pub mod visit;

mod expr;
mod item;
pub use expr::*;
pub use item::*;
