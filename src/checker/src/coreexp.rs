// this file is for core expression definition and its type checking
// variable is represented as std::rc::Rc<String>

use std::{
    fmt::{Debug, Display},
    rc::Rc,
};

#[derive(Clone)]
pub struct Var(Rc<String>);

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

// functional pure type system
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
    pub fn relation_of_sort_indelim(self, other: Self) -> Option<()> {
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
pub enum Exp {
    Sort(Sort),
    Var(Var),
    // (x: A) -> B where x is bound in B but not in A
    Prod {
        var: Var,
        ty: Box<Exp>,
        body: Box<Exp>, // bind one variable
    },
    // (x: A) => B where x is bound in B but not in A
    Lam {
        var: Var,
        ty: Box<Exp>,
        body: Box<Exp>, // bind one variable
    },
    App {
        func: Box<Exp>,
        arg: Box<Exp>,
    },
    // uncurry with parameter
    IndType {
        ty: Rc<crate::inductive::InductiveTypeSpecs>,
        parameters: Vec<Exp>,
    },
    // uncurry with parameter
    IndCtor {
        ty: Rc<crate::inductive::InductiveTypeSpecs>,
        parameters: Vec<Exp>,
        idx: usize,
    },
    // this is primitive recursion (no binding representation)
    IndElim {
        ty: Rc<crate::inductive::InductiveTypeSpecs>,
        elim: Box<Exp>,
        return_type: Box<Exp>,
        sort: Sort,
        cases: Vec<Exp>,
    },
    Cast {
        exp: Box<Exp>,
        to: Box<Exp>,
    },
    Proof {
        prop: Box<Exp>,
    },
    PowerSet {
        set: Box<Exp>,
    },
    // {x: A | P} where x is bound in P but not in A
    SubSet {
        var: Var,
        set: Box<Exp>,
        predicate: Box<Exp>, // bind one variable
    },
    Pred {
        superset: Box<Exp>,
        subset: Box<Exp>,
        element: Box<Exp>,
    },
    TypeLift {
        superset: Box<Exp>,
        subset: Box<Exp>,
    },
    Equal {
        left: Box<Exp>,
        right: Box<Exp>,
    },
    // just non-emptyness proposition
    Exists {
        set: Box<Exp>,
    },
    Take {
        map: Box<Exp>,
        domain: Box<Exp>,
        codomain: Box<Exp>,
    },
}

#[derive(Debug, Clone)]
pub struct Context(pub Vec<(Var, Exp)>);

impl Context {
    pub fn extend(&self, varty: (Var, Exp)) -> Self {
        let mut new_ctx = self.0.clone();
        new_ctx.push(varty);
        Context(new_ctx)
    }
    pub fn get(&self, var: &Var) -> Option<&Exp> {
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
    pub term: Exp,
    pub ty: Exp,
}

#[derive(Debug, Clone)]
pub struct Provable {
    pub ctx: Context,
    pub prop: Exp,
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
    pub fn make_goal(ctx: Context, prop: Exp) -> Self {
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
        proof_term: Exp,
        prop: Exp,
    },
    // ctx |= nonempty(ty)
    //   ctx |- elem: ty, ctx |- ty: Set(i)
    ExactElem {
        elem: Exp,
        ty: Exp,
    },
    // ctx |= Pred(supserset, subset, elem)
    //   ctx |- elem: Typelift(superset, subset), ctx |- Typelift(superset, subset): Set(i)
    SubsetElim {
        elem: Exp,
        subset: Exp,
        superset: Exp,
    },
    // ctx |= elem = elem
    //   ctx |- elem: ty, ctx |- ty: Set(i)
    IdRefl {
        ctx: Context,
        elem: Exp,
    },
    // ctx |= predicate(elem2)
    //   ctx |- elem1: ty, ctx |- elem2: ty, ctx |- ty: Set(i), ctx |- predicate: ty -> Prop
    //   ctx |= predicate(elem1), ctx |= elem1 = elem2
    IdElim {
        ctx: Context,
        elem1: Exp,
        elem2: Exp,
        ty: Box<Exp>,
        predicate: Box<Exp>,
    },
    // ctx |= Take f = f elem
    //  ctx |- func: (_: domain) -> codomain, ctx |- elem: domain
    //  ctx |- Take f: docomain
    TakeEq {
        func: Box<Exp>,
        domain: Box<Exp>,
        codomain: Box<Exp>,
        elem: Box<Exp>,
    },
    // axioms
    Axiom(Axiom),
}

#[derive(Debug, Clone)]
pub enum Axiom {
    ExcludedMiddle {
        ctx: Context,
        prop: Exp,
    },
    FunctionExtensionality {
        ctx: Context,
        func1: Exp,
        func2: Exp,
    },
    EmsemblesExtensionality {
        ctx: Context,
        set1: Exp,
        set2: Exp,
        superset: Exp,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_macros() {
        let _ = Exp::Sort(Sort::Prop);
    }
}
