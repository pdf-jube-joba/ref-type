// this file is for core expression definition and its type checking
// variable is represented as std::rc::Rc<String>

use std::{
    fmt::{Debug, Display},
    rc::Rc,
};

#[derive(Clone)]
pub struct Var(pub Rc<String>);

impl Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{:p}]", self.0, self.0)
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Var {
    pub fn new(name: &str) -> Self {
        Var(Rc::new(name.to_string()))
    }
    pub fn name(&self) -> &str {
        &self.0
    }
    pub fn is_eq_ptr(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Set(usize), // predicateive SET(0): SET(1): SET(2) ...
    Prop,       // proposition
    Univ,       // Prop: UNiv
    Type,       // for programming language
}

// functional なものしか考えないのでよい。
impl Sort {
    // functional pure type system, i.e. foraeach s1, (s1, s2) in R => s2 is unique
    pub fn type_of_sort(self) -> Option<Self> {
        match self {
            Sort::Univ => None,
            Sort::Set(i) => Some(Sort::Set(i + 1)),
            Sort::Prop => Some(Sort::Univ),
            Sort::Type => Some(Sort::Univ),
        }
    }

    // functional pure type system, i.e. foraeach s1, s2, (s1, s2, s3) in R => s3 is unique
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

    // inductive type relation (restiction for large elimination)
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

#[derive(Debug, Clone)]
pub enum CoreExp {
    Sort(Sort),
    Var(Var),
    // (x: A) -> B where x is bound in B but not in A
    Prod {
        var: Var,
        ty: Box<CoreExp>,
        body: Box<CoreExp>, // bind one variable
    },
    // (x: A) => B where x is bound in B but not in A
    Lam {
        var: Var,
        ty: Box<CoreExp>,
        body: Box<CoreExp>, // bind one variable
    },
    App {
        func: Box<CoreExp>,
        arg: Box<CoreExp>,
    },
    // uncurry with parameter
    IndType {
        ty: Rc<crate::inductive::InductiveTypeSpecs>,
        parameters: Vec<CoreExp>,
    },
    // uncurry with parameter
    IndTypeCst {
        ty: Rc<crate::inductive::InductiveTypeSpecs>,
        idx: usize,
        parameter: Vec<CoreExp>,
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
        var: Var,
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

#[derive(Debug, Clone)]
pub struct Context(pub Vec<(Var, CoreExp)>);

impl Context {
    pub fn extend(&self, varty: (Var, CoreExp)) -> Self {
        let mut new_ctx = self.0.clone();
        new_ctx.push(varty);
        Context(new_ctx)
    }
    pub fn get(&self, var: &Var) -> Option<&CoreExp> {
        for (v, ty) in self.0.iter().rev() {
            if v.is_eq_ptr(var) {
                return Some(ty);
            }
        }
        None
    }
}

#[derive(Debug, Clone)]
pub struct TypeJudge {
    pub ctx: Context,
    pub term: CoreExp,
    pub ty: CoreExp,
}

#[derive(Debug, Clone)]
pub struct Provable {
    pub ctx: Context,
    pub prop: CoreExp,
}

// this is for representing failure of proof
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FailJudge(pub String);

#[derive(Debug, Clone)]
pub enum Judgement {
    Type(TypeJudge),
    Provable(Provable),
    FailJudge(FailJudge),
}

#[derive(Debug, Clone)]
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

// given (ctx |= prop)
#[derive(Debug, Clone)]
pub enum ProveCommandBy {
    // ctx |= prop
    //   ctx |- proof_term : prop
    Construct {
        proof_term: CoreExp,
        prop: CoreExp,
    },
    // ctx |= nonempty(ty)
    //   ctx |- elem: ty, ctx |- ty: Set(i)
    ExactElem {
        elem: CoreExp,
        ty: CoreExp,
    },
    // ctx |= Pred(supserset, subset, elem)
    //   ctx |- elem: Typelift(superset, subset), ctx |- Typelift(superset, subset): Set(i)
    SubsetElim {
        elem: CoreExp,
        subset: CoreExp,
        superset: CoreExp,
    },
    // ctx |= elem = elem
    //   ctx |- elem: ty, ctx |- ty: Set(i)
    IdRefl {
        ctx: Context,
        elem: CoreExp,
    },
    // ctx |= predicate(elem2)
    //   ctx |- elem1: ty, ctx |- elem2: ty, ctx |- ty: Set(i), ctx |- predicate: ty -> Prop
    //   ctx |= predicate(elem1), ctx |= elem1 = elem2
    IdElim {
        ctx: Context,
        elem1: CoreExp,
        elem2: CoreExp,
        ty: Box<CoreExp>,
        predicate: Box<CoreExp>,
    },
    // ctx |= Take f = f elem
    //  ctx |- func: (_: domain) -> codomain, ctx |- elem: domain
    //  ctx |- Take f: docomain
    TakeEq {
        func: Box<CoreExp>,
        domain: Box<CoreExp>,
        codomain: Box<CoreExp>,
        elem: Box<CoreExp>,
    },
    // axioms
    Axiom(Axiom),
}

#[derive(Debug, Clone)]
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
