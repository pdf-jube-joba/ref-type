// this file describes the syntax tree after (parsing + early name resolution)
// it is not type checked yet but should be well scoped
// any variable should be replaced as de Bruijn index

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
    pub children: Vec<usize>,           // index to Environment.modules
    pub parameters: Vec<(Name, Exp)>,   // given parameters for module
    pub declarations: Vec<Declaration>, // sensitive to order
}

// parameter instantiated module
// e.g. modA(B := x, C := y)
// internally, it is represented as ModuleInstantiated { module_name: n, arguments: [x, y] }
// this is after name resolution
#[derive(Debug, Clone)]
pub struct ModuleInstantiated {
    pub module_name: usize, // index to Environment.modules
    pub arguments: Vec<Exp>,
}

// path of module access
// e.g. [A, B(x1 := y1, x2 := y2), C] for A.B(x1 := y1, x2 := y2).C.name
#[derive(Debug, Clone)]
pub struct ModPath {
    pub abs_path: Vec<ModuleInstantiated>, // absolute path from root environment
    pub represented_path: String,          // for display purpose only
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Definition {
        // display name for user
        display_name: Name,
        ty: Exp,
        body: Exp,
    },
    Theorem {
        // display name for user
        display_name: Name,
        ty: Exp,
        body: Exp,
    },
    Inductive {
        ind_defs: InductiveTypeSpecs,
    },
    // these are only for display purpose
    // after name resolution, any mod access should be replaced with absolute path
    ChildModule {
        module: usize, // index to Environment.modules
    },
    Import {
        instantiated_module: ModPath,
        import_name: Name,
    },
    MathMacro {
        before: Vec<Either<MacroToken, Name>>,
        after: Vec<Either<Exp, Name>>,
    },
    UserMacro {
        name: Name,
        before: Vec<Either<MacroToken, Name>>,
        after: Vec<Name>,
    },
}

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

#[derive(Debug, Clone)]
// general binding syntax
// A = (_: A), (x: A), (x: A | P), (x: A | h: P),
// binding variable is for display purpose only (de Bruijn)
pub struct Bind {
    pub var: Option<Name>,
    pub ty: Box<Exp>,
    pub predicate: Option<(Option<Name>, Box<Exp>)>,
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
    // before type checking, it is expanded to normal expression
    MathMacro {
        tokens: Vec<Either<MacroToken, Exp>>,
    },
    // currently not supported
    // UserMacro {
    //     name: Name,
    //     tokens: Vec<Either<MacroToken, Exp>>,
    // },
    // --- expression with clauses
    // where clauses to define local variables
    Where {
        exp: Box<Exp>,
        clauses: Vec<(Name, Exp, Exp)>,
    },
    // goal proving  given by type checker
    WithProof {
        exp: Box<Exp>,
        proofs: Vec<(Vec<(Name, Exp)>, Exp, Exp)>,
    },
    // --- lambda calculus
    // sort: Prop, Set(i), Univ, Type
    Sort(Sort),
    // variable defined by De Bruijn index
    // de Bruijn index is (local, global)
    // it should not point to a module defined name
    Var(Var),
    // bind -> B
    Prod {
        bind: Bind,
        body: Box<Exp>,
    },
    // bind => t
    Lam {
        bind: Bind,
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
        path: ModPath,
        ind_type_name: String,
        eliminated_exp: Box<Exp>,
        return_type: Box<Exp>,
        cases: Vec<(String, Exp)>,
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
        var: Name,
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
    // Bracket type ... \exists (x: A), (x: A | P)
    Exists {
        bind: Bind,
    },
    // --- opaque description (specified but not constructed)
    // \take (x: A) => t or \take (x: A | P) => t
    Take {
        bind: Bind,
        body: Box<Exp>,
    },
    // --- "proof by" terms
    ProofBy(ProofBy),
    // --- block of statements
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
    Bound(usize),  // de Bruijn index for local bound variable
    Module(usize), // de Bruijn index to parameters of current delcaration module
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
        var: Name,
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
    pub term: Box<Exp>,               // returning term of the block
}

#[derive(Debug, Clone)]
pub enum Statement {
    Fix(Vec<(Name, Exp)>), // fix x: A; y: B;
    Have {
        var: Name,
        ty: Exp,
        body: Exp,
    }, // have x: A := t;
    Take {
        var: Name,
        ty: Exp,
        predicate_proof: Option<(Option<Exp>, Exp)>,
    }, // take x: A; or take x: A | P; or take x: A | h: P;
    Sufficient {
        prop: Exp,
        implication: Exp,
    }, // suffices A by (h: A -> B);
}
