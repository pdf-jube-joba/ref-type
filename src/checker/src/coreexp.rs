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
    // (x: A) -> B where x is bound in B but not in A
    Prod {
        ty: Box<CoreExp>,
        body: Box<CoreExp>, // bind one variable
    },
    // (x: A) => B where x is bound in B but not in A
    Lam {
        ty: Box<CoreExp>,
        body: Box<CoreExp>, // bind one variable
    },
    App {
        func: Box<CoreExp>,
        arg: Box<CoreExp>,
    },
    IndType {
        ty: Rc<crate::inductive::InductiveTypeSpecs>,
        args: Vec<CoreExp>,
    },
    IndTypeCst {
        ty: Rc<crate::inductive::InductiveTypeSpecs>,
        idx: usize,
        args: Vec<CoreExp>,
    },
    // this is primitive recursion
    // no binding in elim, return_type, cases
    IndTypeElim {
        ty: Rc<crate::inductive::InductiveTypeSpecs>,
        elim: Box<CoreExp>,
        return_type: Box<CoreExp>,
        cases: Vec<CoreExp>,
    },
    Cast {
        exp: Box<CoreExp>,
        to: Box<CoreExp>,
    },
    Proof {
        exp: Box<CoreExp>,
    },
    PowerSet {
        exp: Box<CoreExp>,
    },
    // {x: A | P} where x is bound in P but not in A
    SubSet {
        exp: Box<CoreExp>,
        predicate: Box<CoreExp>, // bind one variable
    },
    Pred {
        superset: Box<CoreExp>,
        subset: Box<CoreExp>,
        element: Box<CoreExp>,
    },
    TypeLift {
        superset: Box<CoreExp>,
        subset: Box<CoreExp>,
    },
    Equal {
        left: Box<CoreExp>,
        right: Box<CoreExp>,
    },
    // just non-emptyness proposition
    Exists {
        ty: Box<CoreExp>,
    },
    Take {
        map: Box<CoreExp>,
        domain: Box<CoreExp>,
        codomain: Box<CoreExp>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Context(pub Vec<CoreExp>);

impl Context {
    pub fn extend(&self, ty: CoreExp) -> Self {
        let mut new_ctx = self.0.clone();
        new_ctx.push(ty);
        Context(new_ctx)
    }
    pub fn get(&self, idx: usize) -> Option<&CoreExp> {
        self.0.get(self.0.len() - 1 - idx)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeJudge {
    pub ctx: Context,
    pub term: CoreExp,
    pub ty: CoreExp,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Provable {
    pub ctx: Context,
    pub prop: CoreExp,
}

// this is for representing failure of proof
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FailJudge(pub String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Judgement {
    Type(TypeJudge),
    Provable(Provable),
    FailJudge(FailJudge),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Derivation {
    pub conclusion: Judgement,
    pub premises: Vec<Derivation>,
    pub rule: String,
    pub meta: Option<String>,
}

impl Derivation {
    pub fn make_goal(ctx: Context, prop: CoreExp) -> Self {
        Derivation {
            conclusion: Judgement::Provable(Provable { ctx, prop }),
            premises: vec![],
            rule: "Goal".to_string(),
            meta: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProveCommandBy {
    Construct {
        ctx: Context,
        proof_term: CoreExp,
    },
    ExactElem {
        ctx: Context,
        elem: CoreExp,
        ty: CoreExp,
    },
    SubsetElim {
        ctx: Context,
        elem: CoreExp,
        subset: CoreExp,
        superset: CoreExp,
    },
    IdRefl {
        ctx: Context,
        elem: CoreExp,
        ty: CoreExp,
    },
    IdElim {
        ctx: Context,
        elem1: CoreExp,
        elem2: CoreExp,
        ty: Box<CoreExp>,
        predicate: Box<CoreExp>,
    },
    TakeEq {
        func: Box<CoreExp>,
        elem: Box<CoreExp>,
    },
    Axiom(Axiom),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Axiom {
    ExcludedMiddle {
        ctx: Context,
        prop: CoreExp,
    },
    FunctionExtensionality {
        ctx: Context,
        func1: CoreExp,
        func2: CoreExp,
    },
    EmsemblesExtensionality {
        ctx: Context,
        set1: CoreExp,
        set2: CoreExp,
        superset: CoreExp,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_macros() {
        let _ = CoreExp::Sort(Sort::Prop);
    }
}
