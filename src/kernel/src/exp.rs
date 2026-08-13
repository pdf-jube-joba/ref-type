use std::{fmt::Debug, rc::Rc};

use serde::{Deserialize, Serialize};

use crate::serialize::serialize_rc_ptr;

// variable is represented as std::rc::Rc<String>
#[derive(Clone)]
pub struct Var(Rc<String>);

impl Var {
    pub fn new(name: &str) -> Self {
        Var(Rc::new(name.to_string()))
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
    pub fn ptr(&self) -> *const String {
        Rc::as_ptr(&self.0)
    }
    pub fn is_eq_ptr(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
    pub fn dummy() -> Self {
        Var(Rc::new("_".to_string()))
    }
}

impl PartialEq for Var {
    fn eq(&self, other: &Self) -> bool {
        self.ptr() == other.ptr()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Sort {
    Set(usize),     // predicative SET(i):
    SetKind(usize), // SET(i): SETKind(i)
    Prop,           // proposition
    PropKind,       // Prop: PropKind
    Univ,           // for programming language
    UnivKind,       // Type: TypeKind
}

// functional pure type system
impl Sort {
    // functional pure type system, i.e. foraeach s1, (s1, s2) in R => s2 is unique
    pub fn type_of_sort(self) -> Option<Self> {
        match self {
            Sort::Prop => Some(Sort::PropKind),
            Sort::PropKind => None,
            Sort::Univ => Some(Sort::PropKind),
            Sort::UnivKind => None,
            Sort::Set(i) => Some(Sort::SetKind(i)),
            Sort::SetKind(_) => None,
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
            // Set(i): SetKind(i) part (predicative)
            (Sort::Set(i), Sort::Set(j)) if i == j => Some(Sort::Set(i)),
            (Sort::Set(i), Sort::SetKind(j)) if i == j => Some(Sort::SetKind(i)),
            (Sort::SetKind(i), Sort::SetKind(j)) if i == j => Some(Sort::SetKind(i)),
            (Sort::SetKind(i), Sort::Set(j)) if i == j => Some(Sort::Set(i + 1)),
            (Sort::Set(_) | Sort::SetKind(_), Sort::Set(_) | Sort::SetKind(_)) => None,
            // Type: TypeKind (include dependent, impredicative)
            (Sort::Univ | Sort::UnivKind, Sort::Univ | Sort::UnivKind) => Some(other),
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
                Sort::PropKind
                | Sort::Prop
                | Sort::Set(_)
                | Sort::SetKind(_)
                | Sort::Univ
                | Sort::UnivKind,
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

    pub fn can_lift_to(self, to: Self) -> bool {
        match (self, to) {
            (Sort::Set(i), Sort::Set(j)) if i <= j => true,
            (Sort::SetKind(i), Sort::SetKind(j)) if i <= j => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct DefinedConstant {
    pub ty: Exp,
    pub body: Exp,
}

#[derive(Debug, Clone, Serialize)]
pub enum Exp {
    Sort(Sort),
    Var(Var),
    // (var: ty) -> body where var is bound in body but not in ty
    Prod {
        var: Var,
        ty: Box<Exp>,
        body: Box<Exp>, // bind one variable
    },
    // (var: ty) => body where var is bound in body but not in ty
    Lam {
        var: Var,
        ty: Box<Exp>,
        body: Box<Exp>, // bind one variable
    },
    // usual application (f x)
    App {
        func: Box<Exp>,
        arg: Box<Exp>,
    },
    DefinedConstant(#[serde(serialize_with = "serialize_rc_ptr")] Rc<DefinedConstant>),
    IndType {
        #[serde(serialize_with = "serialize_rc_ptr")]
        indspec: Rc<crate::inductive::InductiveTypeSpecs>,
        parameters: Vec<Exp>, // uncurry with parameter
    },
    IndCtor {
        #[serde(serialize_with = "serialize_rc_ptr")]
        indspec: Rc<crate::inductive::InductiveTypeSpecs>,
        parameters: Vec<Exp>, // uncurry with parameter
        idx: usize,
    },
    IndElim {
        // this is primitive recursion
        #[serde(serialize_with = "serialize_rc_ptr")]
        indspec: Rc<crate::inductive::InductiveTypeSpecs>,
        elim: Box<Exp>,
        return_type: Box<Exp>,
        cases: Vec<Exp>, // no bindings
    },
    // Introduce `element` into `subset` of `superset` using `proof`.
    // This is a typing annotation and erases to `element` computationally.
    SubsetIntro {
        superset: Box<Exp>,
        subset: Box<Exp>,
        element: Box<Exp>,
        proof: Box<Exp>,
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
        domain: Box<Exp>,
        codomain: Box<Exp>,
        map: Box<Exp>,
        existence: Box<Exp>,
        uniqueness: Option<Box<Exp>>,
    },
    ExistsIntro {
        element: Box<Exp>,
        set: Box<Exp>,
    },
    SubsetElim {
        element: Box<Exp>,
        subset: Box<Exp>,
        superset: Box<Exp>,
    },
    IdRefl {
        element: Box<Exp>,
    },
    IdElim {
        left: Box<Exp>,
        right: Box<Exp>,
        ty: Box<Exp>,
        var: Var,
        predicate: Box<Exp>,
        base: Box<Exp>,
        equality: Box<Exp>,
    },
    TakeEq {
        func: Box<Exp>,
        domain: Box<Exp>,
        codomain: Box<Exp>,
        element: Box<Exp>,
        existence: Box<Exp>,
        uniqueness: Option<Box<Exp>>,
    },
}

impl Exp {
    pub fn refinement(v: Var, set: Exp, predicate: Exp) -> Exp {
        Exp::TypeLift {
            superset: Box::new(set.clone()),
            subset: Box::new(Exp::SubSet {
                var: v,
                set: Box::new(set),
                predicate: Box::new(predicate),
            }),
        }
    }
    pub fn as_var(&self) -> Option<&Var> {
        if let Exp::Var(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

pub type Context = Vec<(Var, Exp)>;

/// Return a new context that is `ctx` extended with one (Var, Exp)
pub fn ctx_extend(ctx: &Context, varty: (Var, Exp)) -> Context {
    let mut new_ctx = ctx.clone();
    new_ctx.push(varty);
    new_ctx
}

/// Lookup a variable in the context by pointer-equality (same semantics as previous implementation)
pub fn ctx_get<'a>(ctx: &'a Context, var: &'a Var) -> Option<&'a Exp> {
    for (v, ty) in ctx.iter().rev() {
        if v.is_eq_ptr(var) {
            return Some(ty);
        }
    }
    None
}

#[derive(Debug, Clone, Serialize)]
pub struct ErrorFrame {
    pub rule: String,
    pub phase: String,
    pub expected: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct JudgementError {
    pub cause: String,
    pub frames: Vec<ErrorFrame>,
}

impl JudgementError {
    pub fn caused(cause: impl Into<String>) -> Self {
        Self {
            cause: cause.into(),
            frames: Vec::new(),
        }
    }

    pub fn with_frame(
        mut self,
        rule: impl Into<String>,
        phase: impl Into<String>,
        expected: impl Into<String>,
    ) -> Self {
        self.frames.push(ErrorFrame {
            rule: rule.into(),
            phase: phase.into(),
            expected: expected.into(),
        });
        self
    }
}
