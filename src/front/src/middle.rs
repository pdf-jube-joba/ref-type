// middle intermediate representation after
// - name resolution (binding variables and bindee)
// - macro expansion

use std::rc::Rc;

use crate::syntax::Sort;

#[derive(Clone)]
pub struct Name(Rc<String>);

pub struct MirModule {
    pub name: String,
    pub parent: Option<usize>,
    pub parameters: Vec<(Name, Mir)>,
    pub items: Vec<MirModuleItem>,
}

pub struct MirModuleInstantiated {
    pub module: usize,
    pub arguments: Vec<(Name, Mir)>,
}

pub struct ModulePath(Vec<MirModuleInstantiated>);

pub enum MirModuleItem {
    Definition { name: Name, ty: Mir, body: Mir },
    Inductive { ind_defs: InductiveTypeSpecs },
}

pub struct InductiveTypeSpecs {
    pub type_name: String,
    pub parameters: Vec<(Name, Mir)>,
    pub indices: Vec<(Name, Mir)>,
    pub sort: Mir,
    pub constructors: Vec<(Name, Vec<ParamCtor>, Vec<Mir>)>,
}

pub enum ParamCtor {
    StrictPositive(Vec<(Name, Mir)>, Vec<Mir>),
    Simple(Name, Mir),
}

pub enum Mir {
    ModAccessDef {
        path: ModulePath,
        name: Name,
    },
    Let {
        name: Name,
        ty: Box<Mir>,
        body: Box<Mir>,
        value: Box<Mir>,
    },
    Sort(Sort),
    Var(Name),
    Prod {
        var: Name,
        ty: Box<Mir>,
        body: Box<Mir>,
    },
    Lam {
        var: Name,
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
        path: ModulePath,
        type_name: Name,
    },
    IndCtor {
        path: ModulePath,
        type_name: Name,
        ctor_name: Name,
    },
    IndElim {
        path: ModulePath,
        ty: Box<Mir>,
        elim: Box<Mir>,
        return_type: Box<Mir>,
        sort: Sort,
        cases: Vec<Mir>,
    },
    ProofLater {
        prop: Box<Mir>,
    },
    PowerSet {
        base: Box<Mir>,
    },
    Subset {
        var: Name,
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
        var: Name,
        ty: Box<Mir>,
        body: Box<Mir>,
        codomain: Box<Mir>,
    },
    ProofBy(MirProofBy),
    Block(MirBlock),
}

pub enum MirProofBy {}

pub struct MirBlock {
    pub statements: Vec<MirStatement>,
    pub result: Box<Mir>,
}

pub enum MirStatement {
    Let {
        name: Name,
        ty: Box<Mir>,
        value: Box<Mir>,
    },
}
