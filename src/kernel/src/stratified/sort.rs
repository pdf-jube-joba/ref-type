//! The non-cumulative product signature of stratification4 §2.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SetSort {
    Set(usize),
    Prop,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BaseSort {
    Set(usize),
    Prop,
    Value(usize),
    Computation(usize),
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    Base(BaseSort),
    Upper(BaseSort),
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProductRule {
    pub domain: Sort,
    pub body: Sort,
    pub result: Sort,
}
impl From<SetSort> for BaseSort {
    fn from(s: SetSort) -> Self {
        match s {
            SetSort::Set(i) => Self::Set(i),
            SetSort::Prop => Self::Prop,
        }
    }
}
impl TryFrom<BaseSort> for SetSort {
    type Error = String;
    fn try_from(s: BaseSort) -> Result<Self, String> {
        match s {
            BaseSort::Set(i) => Ok(Self::Set(i)),
            BaseSort::Prop => Ok(Self::Prop),
            _ => Err("expected Set/Prop sort".into()),
        }
    }
}
impl BaseSort {
    pub fn level(self) -> Option<usize> {
        match self {
            Self::Set(i) | Self::Value(i) | Self::Computation(i) => Some(i),
            Self::Prop => None,
        }
    }
    pub fn is_program(self) -> bool {
        matches!(self, Self::Value(_) | Self::Computation(_))
    }
    pub fn reflected(self) -> Self {
        match self {
            Self::Value(i) | Self::Computation(i) => Self::Set(i),
            s => s,
        }
    }
}
impl Sort {
    pub fn base(self) -> BaseSort {
        match self {
            Self::Base(b) | Self::Upper(b) => b,
        }
    }
    pub fn is_upper(self) -> bool {
        matches!(self, Self::Upper(_))
    }
    pub fn reflected(self) -> Self {
        match self {
            Self::Base(b) => Self::Base(b.reflected()),
            Self::Upper(b) => Self::Upper(b.reflected()),
        }
    }
    pub fn product(self, body: Self) -> Option<Self> {
        use BaseSort::*;
        use Sort::{Base as B, Upper as U};
        match (self, body) {
            (B(Set(i)), B(Set(j))) => Some(B(Set(i.max(j)))),
            (B(Set(i)), U(Set(j))) | (U(Set(i)), U(Set(j))) => Some(U(Set(i.max(j)))),
            (U(Set(i)), B(Set(j))) => Some(B(Set(i.checked_add(1)?.max(j)))),
            (B(Prop), B(Prop)) | (U(Prop), B(Prop)) => Some(B(Prop)),
            (U(Prop), U(Prop)) => Some(U(Prop)),
            (B(Set(_)) | U(Set(_)), b @ (B(Prop) | U(Prop))) => Some(b),
            (B(Value(i)), B(Computation(j))) => Some(B(Computation(i.max(j)))),
            (U(Value(i)) | U(Computation(i)), B(Computation(j))) => {
                Some(B(Computation(i.checked_add(1)?.max(j))))
            }
            (U(Value(i)) | U(Computation(i)), U(Value(j))) => Some(U(Value(i.max(j)))),
            (U(Value(i)) | U(Computation(i)), U(Computation(j))) => Some(U(Computation(i.max(j)))),
            _ => None,
        }
    }
}
impl ProductRule {
    pub fn new(domain: Sort, body: Sort) -> Result<Self, String> {
        Ok(Self {
            domain,
            body,
            result: domain
                .product(body)
                .ok_or("no product rule for these sorts")?,
        })
    }
    pub fn validate(self) -> Result<(), String> {
        if self.domain.product(self.body) == Some(self.result) {
            Ok(())
        } else {
            Err("invalid product rule label".into())
        }
    }
    pub fn reflected(self) -> Self {
        Self {
            domain: self.domain.reflected(),
            body: self.body.reflected(),
            result: self.result.reflected(),
        }
    }
}
