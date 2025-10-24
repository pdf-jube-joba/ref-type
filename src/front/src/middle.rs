// middle intermediate representation after
// - name resolution (binding variables and bindee)
// - macro expansion

use std::fmt::Debug;

// root of middle intermediate representation
pub struct MirGlobal {
    pub mods: Vec<MirModule>,
    pub order: Vec<usize>, // evaluation order of root modules
}

#[derive(Debug)]
pub struct MirModule {
    pub parameters: Vec<(kernel::exp::Var, Mir)>,
    pub items: Vec<MirModuleItem>,
}

#[derive(Debug)]
pub struct MirModuleInstantiated {
    pub module: usize,
    pub arguments: Vec<(kernel::exp::Var, Mir)>,
}

#[derive(Debug)]
pub enum MirModuleItem {
    Definition {
        name: kernel::exp::Var,
        ty: Mir,
        body: Mir,
        goals: Vec<WithGoal>,
    },
    Inductive {
        ind_defs: InductiveTypeSpecs,
    },
    ChildModule(usize),
}

#[derive(Debug)]
pub struct InductiveTypeSpecs {
    pub parameters: Vec<(kernel::exp::Var, Mir)>,
    pub indices: Vec<(kernel::exp::Var, Mir)>,
    pub sort: Mir,
    pub constructors: Vec<(kernel::exp::Var, Vec<ParamCtor>, Vec<Mir>)>,
}

#[derive(Debug)]
pub enum ParamCtor {
    StrictPositive(Vec<(kernel::exp::Var, Mir)>, Vec<Mir>),
    Simple(kernel::exp::Var, Mir),
}

#[derive(Debug)]
pub struct WithGoal {
    pub extend_ctx: Vec<(kernel::exp::Var, Mir)>,
    pub goal_prop: Mir,
    pub proof: Mir,
}

#[derive(Debug)]
pub enum Mir {
    ModAccessDef {
        path: MirModuleInstantiated,
        name: kernel::exp::Var,
    },
    Let {
        name: kernel::exp::Var,
        ty: Box<Mir>,
        body: Box<Mir>,
        value: Box<Mir>,
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
    Annotation {
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

#[derive(Debug)]
pub enum MirProofBy {}

#[derive(Debug)]
pub struct MirBlock {
    pub statements: Vec<MirStatement>,
    pub result: Box<Mir>,
}

#[derive(Debug)]
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
}
