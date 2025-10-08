// this file is for core expression definition and its type checking
// represented in de Bruijn index

use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Set(usize), // predicateive SET(0): SET(1): SET(2) ...
    Prop,       // proposition
    Univ,       // Prop: UNiv
    Type,       // for programming language
}

// functional なものしか考えないのでよい。
impl Sort {
    // functional なので、
    // (s1, s2) in A な s2 は s1 に対して一意 ... それを返す。
    pub fn type_of_sort(self) -> Option<Self> {
        match self {
            Sort::Univ => None,
            Sort::Set(i) => Some(Sort::Set(i + 1)),
            Sort::Prop => Some(Sort::Univ),
            Sort::Type => Some(Sort::Univ),
        }
    }

    // functional なので、
    // (s1, s2, s3) in R な s3 は (s1, s2) に対して一意 ... それを返す。
    pub fn relation_of_sort(self, other: Self) -> Option<Self> {
        match (self, other) {
            // CoC 部分
            (Sort::Prop, Sort::Prop) => Some(Sort::Prop),
            (Sort::Univ, Sort::Univ) => Some(Sort::Univ),
            (Sort::Univ, Sort::Prop) => Some(Sort::Prop), // Prop は impredicative
            (Sort::Prop, Sort::Univ) => None,             // prop は dependent ではない
            // Set を入れる部分
            (Sort::Set(i), Sort::Set(j)) => Some(Sort::Set(std::cmp::max(i, j))),
            (Sort::Set(_), Sort::Univ) => Some(Sort::Univ),
            (Sort::Set(_), Sort::Prop) => Some(Sort::Prop),
            (Sort::Prop, Sort::Set(_)) => None,
            (Sort::Univ, Sort::Set(_)) => None, // Set は predicative
            // Type を入れる部分
            (Sort::Type, Sort::Type) => Some(Sort::Type),
            (Sort::Type, Sort::Univ) => Some(Sort::Univ),
            (Sort::Univ, Sort::Type) => Some(Sort::Type),
            (Sort::Type, _) => None,
            (_, Sort::Type) => None,
            // Univ 用
        }
    }

    // inductive type の elimination の制限用
    pub fn ind_type_rel(self, other: Self) -> Option<()> {
        match (self, other) {
            (Sort::Univ | Sort::Set(_) | Sort::Type | Sort::Prop, Sort::Prop) => Some(()),
            (Sort::Set(_) | Sort::Type, Sort::Univ) => Some(()),
            (Sort::Univ, Sort::Univ) => Some(()),
            (Sort::Univ | Sort::Type, Sort::Type) => Some(()),
            (Sort::Set(_), Sort::Set(_)) => Some(()),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoreExp {
    Sort(Sort),
    Var(usize),
    Prod {
        ty: Box<CoreExp>,
        body: Box<CoreExp>, // bind one variable
    },
    Lam {
        ty: Box<CoreExp>,
        body: Box<CoreExp>, // bind one variable
    },
    App {
        func: Box<CoreExp>,
        arg: Box<CoreExp>,
    },
    IndType {
        ty: Rc<InductiveTypeSpecs>,
        args: Vec<CoreExp>,
    },
    IndTypeCst {
        ty: Rc<InductiveTypeSpecs>,
        idx: usize,
        args: Vec<CoreExp>,
    },
    IndTypeElim {
        ty: Rc<InductiveTypeSpecs>,
        elim: Box<CoreExp>,
        return_type: Box<CoreExp>,
        cases: Vec<CoreExp>,
    },
    Proof {
        exp: Box<CoreExp>,
    },
    PowerSet {
        exp: Box<CoreExp>,
    },
    SubSet {
        exp: Box<CoreExp>,
        predicate: Box<CoreExp>, // bind one variable
    },
    Pred {
        superset: Box<CoreExp>,
        subset: Box<CoreExp>,
        predicate: Box<CoreExp>,
    },
    TypeLift {
        superset: Box<CoreExp>,
        subset: Box<CoreExp>,
    },
    Equal {
        left: Box<CoreExp>,
        right: Box<CoreExp>,
    },
    Exists {
        ty: Box<CoreExp>,
    },
    Take {
        map: Box<CoreExp>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveTypeSpecs {
    pub parameter: Vec<CoreExp>,
    pub arity: Vec<CoreExp>,
    pub constructors: Vec<(Vec<IndParam>, Vec<CoreExp>)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IndParam {
    StrictPositive(Vec<CoreExp>, Vec<CoreExp>),
    Simple(CoreExp),
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_macros() {}
}
