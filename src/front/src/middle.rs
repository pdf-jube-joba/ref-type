// middle intermediate representation after
// - name resolution (binding variables and bindee)
// - macro expansion

use std::fmt::Debug;

use kernel::exp::{Sort, Var};

#[derive(Debug, Clone)]
pub struct MirModule {
    pub name: kernel::exp::Var,
    pub parameters: Vec<(kernel::exp::Var, Mir)>,
    pub items: Vec<MirModuleItem>,
}

#[derive(Debug, Clone)]
pub struct MirModuleInstantiated {
    pub mod_name: Var,
    pub arguments: Vec<Mir>,
}

#[derive(Debug, Clone)]
pub enum MirModuleItem {
    Definition {
        name: kernel::exp::Var,
        ty: Mir,
        body: Mir,
        goals: Vec<WithGoal>,
    },
    Inductive {
        name: kernel::exp::Var,
        ind_defs: InductiveTypeSpecsMid,
    },
}

#[derive(Debug, Clone)]
pub struct InductiveTypeSpecsMid {
    pub parameters: Vec<(kernel::exp::Var, Mir)>,
    pub indices: Vec<(kernel::exp::Var, Mir)>,
    pub sort: Sort,
    pub constructors: Vec<(Vec<ParamCtor>, Vec<Mir>)>,
}

#[derive(Debug, Clone)]
pub enum ParamCtor {
    StrictPositive(Vec<(kernel::exp::Var, Mir)>, Vec<Mir>),
    Simple(kernel::exp::Var, Mir),
}

#[derive(Debug, Clone)]
pub struct WithGoal {
    pub extend_ctx: Vec<(kernel::exp::Var, Mir)>,
    pub goal_prop: Mir,
    pub proof: Mir,
}

#[derive(Debug, Clone)]
pub enum Mir {
    ModAccessDef {
        path: MirModuleInstantiated,
        name: kernel::exp::Var,
    },
    Sort(kernel::exp::Sort),
    Var(kernel::exp::Var),
    Prod {
        var: kernel::exp::Var,
        ty: Box<Mir>,
        body: Box<Mir>,
    },
    Lam {
        var: kernel::exp::Var,
        ty: Box<Mir>,
        body: Box<Mir>,
    },
    App {
        func: Box<Mir>,
        arg: Box<Mir>,
    },
    Cast {
        exp: Box<Mir>,
        ty: Box<Mir>,
    },
    IndType {
        path: MirModuleInstantiated,
        idx: usize, // index to items[idx] of MirModule ... it should be `ModItem::Inductive``
    },
    IndCtor {
        path: MirModuleInstantiated,
        idx: usize, // index to items[idx] of MirModule ... it should be `ModItem::Inductive``
        ctor_name: kernel::exp::Var,
    },
    IndElim {
        path: MirModuleInstantiated,
        idx: usize, // index to items[idx] of MirModule ... it should be `ModItem::Inductive``
        elim: Box<Mir>,
        return_type: Box<Mir>,
        sort: kernel::exp::Sort,
        cases: Vec<Mir>,
    },
    ProofLater {
        prop: Box<Mir>,
    },
    PowerSet {
        base: Box<Mir>,
    },
    Subset {
        var: kernel::exp::Var,
        base: Box<Mir>,
        predicate: Box<Mir>,
    },
    Predicate {
        superset: Box<Mir>,
        subset: Box<Mir>,
        element: Box<Mir>,
    },
    TypeLift {
        superset: Box<Mir>,
        subset: Box<Mir>,
    },
    Equal {
        left: Box<Mir>,
        right: Box<Mir>,
    },
    Exists {
        base: Box<Mir>,
    },
    Take {
        var: kernel::exp::Var,
        ty: Box<Mir>,
        body: Box<Mir>,
        codomain: Box<Mir>,
    },
    ProofBy(MirProofBy),
    Block(MirBlock),
}

#[derive(Debug, Clone)]
pub enum MirProofBy {}

#[derive(Debug, Clone)]
pub struct MirBlock {
    pub statements: Vec<MirStatement>,
    pub result: Box<Mir>,
}

#[derive(Debug, Clone)]
pub enum MirStatement {
    Let {
        name: kernel::exp::Var,
        ty: Box<Mir>,
        value: Box<Mir>,
    },
    Fix {
        name: kernel::exp::Var,
        ty: Box<Mir>,
    },
    Take {
        name: kernel::exp::Var,
        ty: Box<Mir>,
    },
}
