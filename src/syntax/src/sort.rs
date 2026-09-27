//! Sort names accepted by the surface parser.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Set(usize),     // predicative SET(i):
    SetKind(usize), // SET(i): SETKind(i)
    Prop,           // proposition
    PropKind,       // Prop: PropKind
}
