// this file is for core expression definition and its type checking

use std::{fmt::Debug, rc::Rc};

// variable is represented as std::rc::Rc<String>
#[derive(Clone)]
pub struct Var(Rc<String>);

impl Var {
    pub fn new(name: &str) -> Self {
        Var(Rc::new(name.to_string()))
    }
    pub fn name(&self) -> &str {
        &self.0
    }
    pub fn ptr(&self) -> *const String {
        Rc::as_ptr(&self.0)
    }
    pub fn is_eq_ptr(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Set(usize), // predicative SET(0): SET(1): SET(2) ...
    Prop,       // proposition
    PropKind,   // Prop: PropKind
    Type,       // for programming language
    TypeKind,   // Type: TypeKind
}

// functional pure type system
impl Sort {
    // functional pure type system, i.e. foraeach s1, (s1, s2) in R => s2 is unique
    pub fn type_of_sort(self) -> Option<Self> {
        match self {
            Sort::PropKind => None,
            Sort::Prop => Some(Sort::PropKind),
            Sort::Type => Some(Sort::PropKind),
            Sort::TypeKind => None,
            Sort::Set(i) => Some(Sort::Set(i + 1)),
        }
    }

    // functional pure type system, i.e. for each s1, s2, (s1, s2, s3) in R => s3 is unique
    pub fn relation_of_sort(self, other: Self) -> Option<Self> {
        match (self, other) {
            // Prop: PropKind part（ non dependent ）
            (Sort::Prop, Sort::Prop) => Some(Sort::Prop),
            (Sort::PropKind, Sort::PropKind) => Some(Sort::PropKind),
            (Sort::PropKind, Sort::Prop) => Some(Sort::Prop), // Prop は impredicative
            (Sort::Prop, Sort::PropKind) => None,             // dependent なし
            // Set(i): Set(i + 1) part (predicative)
            (Sort::Set(i), Sort::Set(j)) => Some(Sort::Set(std::cmp::max(i, j))),
            // Type: TypeKind (include dependent, impredicative)
            (Sort::Type | Sort::TypeKind, Sort::Type | Sort::TypeKind) => Some(other),
            // relation of set and prop
            (Sort::Set(_), Sort::PropKind) => Some(Sort::PropKind),
            (Sort::Set(_), Sort::Prop) => Some(Sort::Prop),
            (Sort::Prop | Sort::PropKind, Sort::Set(_)) => None,
            // other => None
            _ => None,
        }
    }

    // inductive type relation (restiction for large elimination)
    pub fn relation_of_sort_indelim(self, other: Self) -> Option<()> {
        match (self, other) {
            (
                Sort::PropKind | Sort::Prop | Sort::Set(_) | Sort::Type | Sort::TypeKind,
                Sort::Prop,
            ) => Some(()),
            (Sort::Set(i), Sort::Set(j)) => {
                if i <= j {
                    Some(())
                } else {
                    None
                }
            }
            (Sort::Set(_), Sort::PropKind) => Some(()),
            (Sort::PropKind, Sort::PropKind) => Some(()),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Exp {
    Sort(Sort),
    Var(Var),
    // (var: ty) -> body where var is bound in body but not in ty
    Prod {
        var: Var,
        ty: Box<Exp>,
        body: Box<Exp>, // bind one variable
    },
    // (var: ty) -> body where var is bound in body but not in ty
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
        withgoals: Vec<ProveGoal>,
    },
    ProveLater {
        prop: Box<Exp>,
    },
    ProofTermRaw {
        command: Box<ProveCommandBy>,
    },
    PowerSet {
        set: Box<Exp>,
    },
    // {var: set | predicate} where var is bound in predicate but not in A
    SubSet {
        var: Var,
        set: Box<Exp>,
        predicate: Box<Exp>,
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

impl Exp {
    pub fn let_in_ty(var: Var, ty: Exp, val: Exp, body: Exp) -> Exp {
        Exp::App {
            func: Box::new(Exp::Lam {
                var,
                ty: Box::new(ty),
                body: Box::new(body),
            }),
            arg: Box::new(val),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ProveGoal {
    pub extended_ctx: Context,
    pub goal_prop: Exp,
    pub proof_term: Exp,
}

// given (ctx |= prop)
#[derive(Debug, Clone)]
pub enum ProveCommandBy {
    // ctx |= prop
    //   ctx |- proof_term : prop
    Construct {
        proof_term: Exp,
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
    Provable(Rc<Provable>),
    FailJudge(FailJudge),
}

#[derive(Debug, Clone)]
pub enum Derivation {
    Tree {
        conclusion: Judgement,
        premises: Vec<Derivation>,
        rule: String,
        meta: Meta,
    },
    Stop(Rc<Provable>), // stop derivation at this provable judgment
}

#[derive(Debug, Clone)]
pub enum Meta {
    Usual(String),   // usual type derivation
    Through(String), // pass through with that function (nothing happens with it)
    Stop,            // stop by proposition
}

impl Derivation {
    pub fn new_tree(
        conclusion: Judgement,
        premises: Vec<Derivation>,
        rule: &str,
        meta: Meta,
    ) -> Self {
        Derivation::Tree {
            conclusion,
            premises,
            rule: rule.to_string(),
            meta,
        }
    }
    pub fn stop(ctx: Context, prop: Exp) -> Self {
        Derivation::Stop(Rc::new(Provable { ctx, prop }))
    }
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
