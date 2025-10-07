// this file describes the syntax tree after parsing + early name resolution
// it is not type checked yet but should be well scoped
use either::Either;

// root of the environment
pub struct Environment {
    pub modules: Vec<Module>,
}

// module definition
#[derive(Debug, Clone)]
pub struct Module {
    pub name: Name,
    pub parent: Option<usize>,          // None for top level module
    pub parameters: Vec<(Name, Exp)>,   // given parameters for module
    pub declarations: Vec<Declaration>, // sensitive to order
}

// parameter instantiated module
// e.g. modA(B := x, C := y)
// internally, it is represented as ModuleInstantiated { module_name: modA, arguments: [x, y] }
// this is after name resolution)
#[derive(Debug, Clone)]
pub struct ModuleInstantiated {
    pub module_name: usize, // index to Environment.modules
    pub arguments: Vec<Exp>,
}

// path of module access
// e.g. [A, B(x1 := y1, x2 := y2), C] for A.B(x1 := y1, x2 := y2).C.name
// if it is empty, it means current module
#[derive(Debug, Clone)]
pub struct ModPath {
    pub abs_path: Vec<ModuleInstantiated>, // absolute path from root module
    pub represented_path: String,          // for display purpose only
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Definition {
        name: Name,
        ty: Exp,
        body: Exp,
    },
    Theorem {
        name: Name,
        ty: Exp,
        body: Exp,
    },
    Inductive {
        ind_defs: InductiveTypeSpecs,
    },
    ChildModule {
        module: usize, // index to Environment.modules
    },
    // this is only for display purpose
    // after name resolution, any mod access should be replaced with absolute path
    Import {
        instantiated_module: ModPath,
        import_name: Name,
    },
    // currently not supported
    // MathMacro {
    //     before: Vec<Either<MacroToken, Var>>,
    //     after: Vec<Either<Exp, Var>>,
    // },
    // UserMacro {
    //     name: Name,
    //     before: Vec<Either<MacroToken, Var>>,
    //     after: Vec<Var>,
    // },
}

// later use
// ```
// definition x: A := t where {
// - y: B := u;
// - z: C := v;
// }
// ```
#[derive(Debug, Clone)]
pub struct WhereClause(Vec<(Name, Exp, Exp)>);

// later use
// theorem x: A := t proof {
// - goal: A1 := t1;
// - goal: A2 := t2;
// }
#[derive(Debug, Clone)]
pub struct ProofClause(Vec<(Exp, Exp)>);

#[derive(Debug, Clone)]
pub struct InductiveTypeSpecs {
    pub type_name: Name,
    pub parameter: Vec<(Name, Exp)>,
    pub arity: (Vec<(Name, Exp)>, Sort),
    pub constructors: Vec<(Name, Vec<ParamCstSyntax>, Vec<Exp>)>,
}

#[derive(Debug, Clone)]
pub enum ParamCstSyntax {
    Positive((Vec<(Name, Exp)>, Vec<Exp>)),
    Simple((Name, Exp)),
}

// this is internal representation
#[derive(Debug, Clone)]
pub enum Exp {
    // --- module access
    // module access `path.name`
    // if name pointed to a inductive type, it should IndType
    // this contains both Definition and Theorem pointing
    ModAccess {
        path: ModPath,
        name: Name,
    },
    // --- macro
    // shared macro for math symbols
    MathMacro {
        tokens: Vec<Either<MacroToken, Exp>>,
    },
    // currently not supported
    // UserMacro {
    //     name: Name,
    //     tokens: Vec<Either<MacroToken, Exp>>,
    // },
    // --- lambda calculus
    // sort: Prop, Set(i), Univ, Type
    Sort(Sort),
    // variable defined by De Bruijn index
    // de Bruijn index is (local, global)
    // it should not point to a module defined name
    Var(Var),
    // (x: A) -> B  or  (x: A | P) -> B
    Prod {
        var: Var,
        ty: Box<Exp>,
        predicate: Option<Box<Exp>>,
        body: Box<Exp>,
    },
    // (x: A) => t  or  (x: A | P) => t
    Lam {
        var: Var,
        ty: Box<Exp>,
        predicate: Option<Box<Exp>>,
        body: Box<Exp>,
    },
    // usual application (f x)
    App {
        func: Box<Exp>,
        arg: Box<Exp>,
    },
    // pipeline style application (x |> f)
    AppByPipe {
        func: Box<Exp>,
        arg: Box<Exp>,
    },
    // type annotation (exp as ty)
    Ann {
        exp: Box<Exp>,
        ty: Box<Exp>,
    },
    // --- inductive type
    // name of inductive type
    IndType {
        path: ModPath,
        ind_type_name: String,
    },
    // constructor of inductive type
    IndCst {
        path: ModPath,
        ind_type_name: String,
        constructor_name: String,
    },
    // primitive elimination for inductive type
    // Elim(ind_type_name, eliminated_exp, return_type){cases[0], ..., cases[m]}
    IndTypeElim {
        ind_type_name: String,
        eliminated_exp: Box<Exp>,
        return_type: Box<Exp>,
        cases: Vec<(String, Vec<Var>, Exp)>,
    },
    // --- set theory
    // \Proof term ... "prove this later"
    Proof {
        term: Box<Exp>,
    },
    // \Power power
    Pow {
        power: Box<Exp>,
    },
    // { x: A | P }
    Sub {
        var: Var,
        ty: Box<Exp>,
        predicate: Box<Exp>,
    },
    // \Pred (superset, subset, elem)
    Pred {
        superset: Box<Exp>,
        subset: Box<Exp>,
        elem: Box<Exp>,
    },
    // \TypeLift (superset, subset)
    TypeLift {
        superset: Box<Exp>,
        subset: Box<Exp>,
    },
    // --- proposition
    // a = b
    Equal {
        left: Box<Exp>,
        right: Box<Exp>,
    },
    // \exists (x: A | P) or \exists (x: A)
    Exists {
        var: Var,
        ty: Box<Exp>,
        predicate: Option<Box<Exp>>,
    },
    // --- opaque description (specified but not constructed)
    // \take (x: A) => t or \take (x: A | P) => t
    Take {
        var: Var,
        ty: Box<Exp>,
        predicate: Option<Box<Exp>>,
        body: Box<Exp>,
    },
    // --- "proof by" terms
    ProofBy(ProofBy),
    Block(Block),
}

// token for macros
// which is (not identifier) /\ (not keyword)
// e.g. "+", "*", "==>", "||", ...
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MacroToken(pub String);

// identifier for any naming
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub String);

// no free variable
// De bruijn index with local and global
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Var {
    Bound(usize), // de bruijn index for bound variable
    Module(Name), // "unique" reference for module parameter
                  // maybe this mentioning to a parent module
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

#[derive(Debug, Clone)]
pub enum ProofBy {
    Construct {
        term: Box<Exp>,
    },
    Exact {
        term: Box<Exp>,
        set: Box<Exp>,
    },
    SubElim {
        superset: Box<Exp>,
        subset: Box<Exp>,
        elem: Box<Exp>,
    },
    IdRefl {
        term: Box<Exp>,
        ty: Box<Exp>,
    },
    IdElim {
        left: Box<Exp>,
        right: Box<Exp>,
        var: Var,
        ty: Box<Exp>,
        predicate: Box<Exp>,
    },
    TakeEq {
        func: Box<Exp>,
        elem: Box<Exp>,
    },
    AxiomLEM {
        proposition: Box<Exp>,
    },
    AxiomFunctionExt {
        func1: Box<Exp>,
        func2: Box<Exp>,
        domain: Box<Exp>,
    },
    AxiomEmsembleExt {
        set1: Box<Exp>,
        set2: Box<Exp>,
        superset: Box<Exp>,
    },
}

#[derive(Debug, Clone)]
pub struct Block {
    pub declarations: Vec<Statement>, // sensitive to order
    pub term: Box<Exp>,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Fix(Vec<(Var, Exp)>), // fix x: A; y: B;
    Have {
        var: Var,
        ty: Exp,
        body: Exp,
    }, // have x: A := t;
    Take {
        var: Var,
        ty: Exp,
        predicate_proof: Option<(Option<Exp>, Exp)>,
    }, // take x: A; or take x: A | P; or take x: A | h: P;
    Sufficient {
        prop: Exp,
        implication: Exp,
    }, // suffices A by (h: A -> B);
}
