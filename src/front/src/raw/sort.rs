//! Pure type system sorts and their formation relations.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Set(usize),     // predicative SET(i):
    SetKind(usize), // SET(i): SETKind(i)
    Prop,           // proposition
    PropKind,       // Prop: PropKind
}

impl Sort {
    /// Return the sort assigned by the functional PTS axiom relation.
    pub fn type_of_sort(self) -> Option<Self> {
        match self {
            Self::Prop => Some(Self::PropKind),
            Self::Set(i) => Some(Self::SetKind(i)),
            Self::PropKind | Self::SetKind(_) => None,
        }
    }

    /// Return the unique product sort assigned by the functional PTS relation.
    pub fn relation_of_sort(self, other: Self) -> Option<Self> {
        match (self, other) {
            // Prop is impredicative.
            (_, Self::Prop) => Some(Self::Prop),
            (Self::PropKind | Self::Set(_) | Self::SetKind(_), Self::PropKind) => {
                Some(Self::PropKind)
            }
            // Set(i): SetKind(i) part (predicative)
            (Self::Set(i), Self::Set(j)) => Some(Self::Set(i.max(j))),
            (Self::Set(i) | Self::SetKind(i), Self::SetKind(j)) => Some(Self::SetKind(i.max(j))),
            (Self::SetKind(i), Self::Set(j)) => Some(Self::Set((i + 1).max(j))),
            _ => None,
        }
    }

    /// Check the large-elimination restriction for an inductive type.
    pub fn relation_of_sort_indelim(self, other: Self) -> Option<()> {
        match (self, other) {
            (_, Self::Prop) | (Self::Set(_) | Self::PropKind, Self::PropKind) => Some(()),
            (Self::Set(i), Self::Set(j)) if i <= j => Some(()),
            _ => None,
        }
    }

    pub fn can_lift_to(self, to: Self) -> bool {
        matches!(
            (self, to),
            (Self::Set(i), Self::Set(j)) | (Self::SetKind(i), Self::SetKind(j)) if i == j
        )
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

    #[test]
    fn prop_is_impredicative_over_set_types() {
        assert_eq!(Sort::Set(0).relation_of_sort(Sort::Prop), Some(Sort::Prop));
        assert_eq!(
            Sort::SetKind(3).relation_of_sort(Sort::Prop),
            Some(Sort::Prop)
        );
    }
}
