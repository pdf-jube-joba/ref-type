//! Semantic syntax between parsing and elaboration.
//! Proof blocks remain structured until their expected type is known.
pub use syntax::{
    AstId, InductiveKind, MacroToken, MetaKind, Sort, SourceFile, SourceId, SourceLocation,
    SourceSpan,
};
pub type Identifier = syntax::Identifier<AstId>;
pub type MacroSeqAtom = syntax::MacroSeqAtom<AstId>;
pub type TokenMatchPattern = syntax::TokenMatchPattern<AstId>;
pub use syntax::{DerivedOrigin, GenerationReason, SourceMap};
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
pub mod origins;
pub mod visit;

mod expr;
mod item;
pub use expr::*;
pub use item::*;

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn lowering_and_program_classification_resolve_through_the_ast_map() {
        let text = r"\cfun (x: A) => \return x";
        let ast = syntax::parse::str_parse_exp(text).unwrap();
        let mut map = syntax::SourceMap::default();
        map.insert(
            &ast,
            &Arc::new(SourceFile {
                id: SourceId("test.ref".into()),
                text: text.into(),
            }),
        );
        let mut hir = SExp::from(ast.clone());
        visit::walk_sexp_mut(&mut hir, &mut |node| {
            assert!(map.location(node.origin.unwrap()).is_some());
        });
        let program = ComputationTermExp::try_from(hir).unwrap();
        assert_eq!(program.origin, Some(ast.source.unwrap().id));
        let ComputationTermExpKind::Lambda { body, .. } = program.kind else {
            panic!("lambda")
        };
        let location = map.location(body.origin.unwrap()).unwrap();
        assert_eq!(&text[location.span.start..location.span.end], r"\return x");
        let ComputationTermExpKind::Return(value) = body.kind else {
            panic!("return")
        };
        let location = map.location(value.origin.unwrap()).unwrap();
        assert_eq!(&text[location.span.start..location.span.end], "x");
    }
}
