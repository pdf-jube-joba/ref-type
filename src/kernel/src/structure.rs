//! Shared operations over typed syntax; no erased node representation.
use super::{ids::*, sort::*, syntax::*};
mod comparison;
mod traversal;
mod views;
pub(crate) use comparison::compare_children;
pub(crate) use traversal::{map_children, visit_children};
pub(crate) use views::*;
#[derive(Clone, Copy)]
pub(crate) enum Traversal {
    All,
    Head,
    Evaluation,
}
