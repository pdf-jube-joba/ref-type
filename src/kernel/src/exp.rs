use std::{fmt::Debug, rc::Rc};

use serde::{Deserialize, Serialize};

use crate::serialize::{serialize_opt_rc_ptr, serialize_rc_ptr};

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
    // cast `exp` to `to`
    Cast {
        exp: Box<Exp>,
        to: Box<Exp>,
    },
    ProveHere {
        exp: Box<Exp>,
        goals: Vec<ProveGoal>,
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

#[derive(Debug, Clone, Serialize)]
pub struct ProveGoal {
    pub extended_ctx: Context,
    pub goal_prop: Exp,
    pub command: ProveCommandBy,
}

// given (ctx |= prop)
#[derive(Debug, Clone, Serialize)]
pub enum ProveCommandBy {
    // ctx |= prop
    //   ctx |- proof_term : prop
    Construct(Exp),
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
        elem: Exp,
    },
    // ctx |= ((var: ty) => predicate) elem2
    //   ctx |- elem1: ty, ctx |- elem2: ty, ctx |- ty: Set(i), ctx::(var, ty) |- predicate: Prop
    //   ctx |= ((var: ty) => predicate) elem1, ctx |= elem1 = elem2
    IdElim {
        left: Exp,
        right: Exp,
        ty: Exp,
        var: Var,
        predicate: Exp,
    },
    // ctx |= Take f = f elem
    //  ctx |- func: (_: domain) -> codomain, ctx |- elem: domain
    //  ctx |- Take f: docomain
    TakeEq {
        func: Exp,
        domain: Exp,
        codomain: Exp,
        elem: Exp,
    },
    // axioms
    Axiom(Axiom),
}

#[derive(Debug, Clone, Serialize)]
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

pub type Context = Vec<(Var, Exp)>;

/// Return a new context that is `ctx` extended with one (Var, Exp)
pub fn ctx_extend(ctx: &Context, varty: (Var, Exp)) -> Context {
    let mut new_ctx = ctx.clone();
    new_ctx.push(varty);
    new_ctx
}

/// Return a new context that is `ctx` extended by `other` (append other's bindings)
pub fn ctx_extend_ctx(ctx: &Context, other: &Context) -> Context {
    let mut new_ctx = ctx.clone();
    new_ctx.extend(other.iter().cloned());
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
pub struct GoalGenerated {
    pub ctx: Context,
    pub proposition: Exp,
    #[serde(serialize_with = "serialize_opt_rc_ptr")]
    pub solvetree: Option<Rc<DerivationSuccess>>,
}

#[derive(Debug, Clone, Serialize)]
pub struct DerivationBase {
    pub premises: Vec<DerivationSuccess>,
    pub rule: String,
    pub phase: String,
}

#[derive(Debug, Clone, Serialize)]
pub enum SuccessHead {
    TypeJudgement {
        ctx: Context,
        term: Exp,
        ty: Exp,
    },
    ProofJudgement {
        ctx: Context,
        prop: Exp,
    },
    WellFormednessInductive {
        ctx: Context,
        #[serde(serialize_with = "serialize_rc_ptr")]
        indspec: Rc<crate::inductive::InductiveTypeSpecs>,
    },
    Solve(#[serde(serialize_with = "serialize_rc_ptr")] Rc<DerivationSuccess>),
}

#[derive(Debug, Clone, Serialize)]
pub struct DerivationSuccess {
    pub base: DerivationBase,
    pub head: SuccessHead,
    pub generated_goals: Vec<GoalGenerated>,
    pub through: bool,
}

#[derive(Debug, Clone, Serialize)]
pub enum FailHead {
    TypeJudgement {
        ctx: Context,
        term: Exp,
        ty: Option<Exp>,
    },
    ProofJudgement {
        ctx: Context,
        prop: Option<Exp>,
    },
    WellFormednessInductive {
        ctx: Context,
        #[serde(serialize_with = "serialize_rc_ptr")]
        indspec: Rc<crate::inductive::InductiveTypeSpecs>,
    },
    Solve(#[serde(serialize_with = "serialize_rc_ptr")] Rc<DerivationSuccess>),
}

#[derive(Debug, Clone, Serialize)]
pub enum FailKind {
    Caused {
        cause: String,
    },
    Propagate {
        fail: Box<DerivationFail>,
        expect: String,
    },
}

#[derive(Debug, Clone, Serialize)]
pub struct DerivationFail {
    pub base: Box<DerivationBase>,
    pub head: FailHead,
    pub kind: FailKind,
}

impl DerivationSuccess {
    pub fn type_of(&self) -> Option<&Exp> {
        match self {
            DerivationSuccess {
                head: SuccessHead::TypeJudgement { ty, .. },
                ..
            } => Some(ty),
            _ => None,
        }
    }
    pub fn prop_of(&self) -> Option<&Exp> {
        match self {
            DerivationSuccess {
                head: SuccessHead::ProofJudgement { prop, .. },
                ..
            } => Some(prop),
            _ => None,
        }
    }
    pub fn ctx_of(&self) -> Option<&Context> {
        match self {
            DerivationSuccess {
                head: SuccessHead::TypeJudgement { ctx, .. },
                ..
            } => Some(ctx),
            DerivationSuccess {
                head: SuccessHead::ProofJudgement { ctx, .. },
                ..
            } => Some(ctx),
            DerivationSuccess {
                head: SuccessHead::WellFormednessInductive { ctx, .. },
                ..
            } => Some(ctx),
            _ => None,
        }
    }
    pub fn first_unproved_mut(&mut self) -> Option<&mut GoalGenerated> {
        let DerivationSuccess {
            base: DerivationBase { premises, .. },
            generated_goals,
            ..
        } = self;
        // first, find from premises
        for premise in premises.iter_mut() {
            if let Some(found) = premise.first_unproved_mut() {
                return Some(found);
            }
        }
        // then, find from generated goals of this tree
        generated_goals
            .iter_mut()
            .find(|goal| goal.solvetree.is_none())
    }
}
