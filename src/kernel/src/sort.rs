//! Pure type system sorts and their formation relations.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Sort {
    Set(usize),     // predicative SET(i):
    SetKind(usize), // SET(i): SETKind(i)
    Prop,           // proposition
    PropKind,       // Prop: PropKind
    Type,           // for programming language
    TypeKind,       // Type: TypeKind
}

impl Sort {
    /// Return the sort assigned by the functional PTS axiom relation.
    pub fn type_of_sort(self) -> Option<Self> {
        match self {
            Sort::Prop => Some(Sort::PropKind),
            Sort::PropKind => None,
            Sort::Type => Some(Sort::TypeKind),
            Sort::TypeKind => None,
            Sort::Set(i) => Some(Sort::SetKind(i)),
            Sort::SetKind(_) => None,
        }
    }

    /// Return the unique product sort assigned by the functional PTS relation.
    pub fn relation_of_sort(self, other: Self) -> Option<Self> {
        match (self, other) {
            // Prop: PropKind part (non-dependent)
            (Sort::Prop, Sort::Prop) => Some(Sort::Prop),
            (Sort::PropKind, Sort::PropKind) => Some(Sort::PropKind),
            (Sort::PropKind, Sort::Prop) => Some(Sort::Prop), // Prop is impredicative
            (Sort::Prop, Sort::PropKind) => None,
            // Set(i): SetKind(i) part (predicative)
            (Sort::Set(i), Sort::Set(j)) => Some(Sort::Set(i.max(j))),
            (Sort::Set(i), Sort::SetKind(j)) => Some(Sort::SetKind(i.max(j))),
            (Sort::SetKind(i), Sort::SetKind(j)) => Some(Sort::SetKind(i.max(j))),
            (Sort::SetKind(i), Sort::Set(j)) => Some(Sort::Set((i + 1).max(j))),
            // Type: TypeKind (dependent and impredicative)
            (Sort::Type | Sort::TypeKind, Sort::Type | Sort::TypeKind) => Some(other),
            // Relations between Set and Prop
            (Sort::Set(_), Sort::PropKind) => Some(Sort::PropKind),
            (Sort::Set(_), Sort::Prop) => Some(Sort::Prop),
            (Sort::Prop | Sort::PropKind, Sort::Set(_)) => None,
            _ => None,
        }
    }

    /// Check the large-elimination restriction for an inductive type.
    pub fn relation_of_sort_indelim(self, other: Self) -> Option<()> {
        match (self, other) {
            (
                Sort::PropKind
                | Sort::Prop
                | Sort::Set(_)
                | Sort::SetKind(_)
                | Sort::Type
                | Sort::TypeKind,
                Sort::Prop,
            ) => Some(()),
            (Sort::Set(i), Sort::Set(j)) if i <= j => Some(()),
            (Sort::Set(_), Sort::PropKind) => Some(()),
            (Sort::PropKind, Sort::PropKind) => Some(()),
            (Sort::Type, Sort::Type) => Some(()),
            _ => None,
        }
    }

    pub fn can_lift_to(self, to: Self) -> bool {
        match (self, to) {
            (Sort::Set(i), Sort::Set(j)) if i <= j => true,
            (Sort::SetKind(i), Sort::SetKind(j)) if i <= j => true,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Sort;

    #[test]
    fn set_products_use_the_least_common_universe() {
        assert_eq!(
            Sort::Set(1).relation_of_sort(Sort::Set(3)),
            Some(Sort::Set(3))
        );
        assert_eq!(
            Sort::Set(2).relation_of_sort(Sort::SetKind(0)),
            Some(Sort::SetKind(2))
        );
        assert_eq!(
            Sort::SetKind(1).relation_of_sort(Sort::SetKind(4)),
            Some(Sort::SetKind(4))
        );
        assert_eq!(
            Sort::SetKind(0).relation_of_sort(Sort::Set(1)),
            Some(Sort::Set(1))
        );
        assert_eq!(
            Sort::SetKind(2).relation_of_sort(Sort::Set(1)),
            Some(Sort::Set(3))
        );
    }
}
