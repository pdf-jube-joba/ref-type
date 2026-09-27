//! Errors retain the failing judgement and its syntax across scratch scopes.
use crate::{
    environment::{Classifier, Context},
    syntax::{Arena, Expression, ExpressionNode},
};
use rustc_hash::FxHashMap;
use std::fmt;

#[derive(Debug, Clone)]
pub struct TypeMismatch {
    pub context: Context,
    pub term: Expression,
    pub inferred: Classifier,
    pub expected: Classifier,
    nodes: FxHashMap<Expression, ExpressionNode>,
}

impl TypeMismatch {
    pub(crate) fn capture(
        arena: &Arena,
        context: &Context,
        term: Expression,
        inferred: Classifier,
        expected: Classifier,
    ) -> Self {
        let mut pending = vec![term];
        pending.extend(context.iter().map(|b| b.classifier));
        for classifier in [inferred, expected] {
            if let Classifier::Expression(e) = classifier {
                pending.push(e);
            }
        }
        let mut nodes = FxHashMap::default();
        while let Some(e) = pending.pop() {
            if let std::collections::hash_map::Entry::Vacant(entry) = nodes.entry(e) {
                entry.insert(arena.node(e));
                crate::structure::visit_children(arena, e, |child, _| pending.push(child));
            }
        }
        Self {
            context: context.clone(),
            term,
            inferred,
            expected,
            nodes,
        }
    }

    pub fn node(&self, expression: Expression) -> &ExpressionNode {
        &self.nodes[&expression]
    }
}

#[derive(Debug, Clone)]
pub enum CheckError {
    Message(String),
    TypeMismatch(Box<TypeMismatch>),
}

impl From<String> for CheckError {
    fn from(message: String) -> Self {
        Self::Message(message)
    }
}
impl From<&str> for CheckError {
    fn from(message: &str) -> Self {
        Self::Message(message.into())
    }
}
impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Message(message) => f.write_str(message),
            Self::TypeMismatch(error) => write!(
                f,
                "types are not convertible in the same family and level\ninferred: {:?}\nexpected: {:?}",
                error.inferred, error.expected
            ),
        }
    }
}
impl std::error::Error for CheckError {}
