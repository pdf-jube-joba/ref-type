// this file describes the surface syntax tree

use either::Either;

// identifier for any naming
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Identifier(pub String);

// module definition
#[derive(Debug, Clone)]
pub struct Module {
    pub name: Identifier,
    pub parameters: Vec<(Identifier, SExp)>, // given parameters for module
    pub declarations: Vec<ModuleItem>,       // sensitive to order
}

// parameter instantiated module
// e.g. modA(B := x, C := y)
#[derive(Debug, Clone)]
pub struct ModuleInstantiated {
    pub module_name: Identifier,            // name of the module
    pub arguments: Vec<(Identifier, SExp)>, // given arguments for parameters
}

// path of module access
// pattern 1 (absolute path): root.name1(arg1, ...).name2(...).name3(...)
// pattern 2 (relatice path): name1(arg1, ...).name2(...).name3(...), or parent.parent. ... .parent.name1(...).name2(...).name3(...)
// pattern 3 (start from named): name.name2(...).name3(...)
#[derive(Debug, Clone)]
pub enum ModPath {
    Root(Vec<ModuleInstantiated>), // relative path from named module
}

#[derive(Debug, Clone)]
pub enum ModuleItem {
    Definition {
        var: Identifier,
        ty: SExp,
        body: SExp,
    },
    Inductive {
        ind_defs: SInductiveTypeSpecs,
    },
    ChildModule {
        module: Box<Module>,
    },
    Import {
        instantiated_module: ModPath,
        import_name: Identifier,
    },
    MathMacro {
        before: Vec<Either<MacroToken, Identifier>>,
        after: Vec<Either<SExp, Identifier>>,
    },
    UserMacro {
        name: Identifier,
        before: Vec<Either<MacroToken, Identifier>>,
        after: Vec<Identifier>,
    },
}

#[derive(Debug, Clone)]
pub struct SInductiveTypeSpecs {
    pub type_name: Identifier,
    pub parameter: Vec<(Identifier, SExp)>,
    pub indices: Vec<(Identifier, SExp)>,
    pub sort: kernel::exp::Sort,
    pub constructors: Vec<(Identifier, SExp)>,
}

#[derive(Debug, Clone)]
// general binding syntax
// A = (_: A), (x: A), (x: A | P), (x: A | h: P),
pub struct Bind {
    pub var: Option<Identifier>,
    pub ty: Box<SExp>,
    pub predicate: Option<(Option<Identifier>, Box<SExp>)>,
}

// this is internal representation
#[derive(Debug, Clone)]
pub enum SExp {
    // --- module access
    // module access `path.name`
    // if name pointed to a inductive type, it should IndType
    // this contains both Definition and Theorem pointing
    ModAccessDef {
        path: ModPath,
        name: Identifier,
    },
    // --- macro
    // shared macro for math symbols
    // before type checking, it is expanded to normal expression
    MathMacro {
        tokens: Vec<Either<MacroToken, SExp>>,
    },
    // macro specified by name
    NamedMacro {
        path: ModPath,
        name: Identifier,
        tokens: Vec<Either<MacroToken, SExp>>,
    },
    // --- expression with clauses
    // where clauses to define local variables
    Where {
        exp: Box<SExp>,
        clauses: Vec<(Identifier, SExp, SExp)>,
    },
    // solve goals given by type checker
    WithProof {
        exp: Box<SExp>,
        proofs: Vec<WithGoal>,
    },
    // --- lambda calculus
    // sort: Prop, Set(i), Univ, Type
    Sort(kernel::exp::Sort),
    // variable defined by name
    Var(Identifier), // updated to use Identifier directly
    // bind -> B
    Prod {
        bind: Bind,
        body: Box<SExp>,
    },
    // bind => t
    Lam {
        bind: Bind,
        body: Box<SExp>,
    },
    // usual application (f x)
    App {
        func: Box<SExp>,
        arg: Box<SExp>,
        piped: bool, // (x | f) to indicate piped application
    },
    // type annotation (exp as ty)
    Annotation {
        exp: Box<SExp>,
        ty: Box<SExp>,
    },
    // --- inductive type
    // name of inductive type
    IndType {
        path: ModPath,
        ind_type_name: String,
    },
    // constructor of inductive type
    IndCtor {
        path: ModPath,
        ind_type_name: String,
        constructor_name: String,
    },
    // primitive elimination for inductive type
    // Elim(ind_type_name, eliminated_exp, return_type){cases[0], ..., cases[m]}
    IndElim {
        path: ModPath,
        ind_type_name: String,
        eliminated_exp: Box<SExp>,
        return_type: Box<SExp>,
        cases: Vec<(String, SExp)>,
    },
    // --- set theory
    // \Proof term ... "prove this later"
    Proof {
        term: Box<SExp>,
    },
    // \Power power
    Pow {
        power: Box<SExp>,
    },
    // { x: A | P }
    Sub {
        var: Identifier,
        ty: Box<SExp>,
        predicate: Box<SExp>,
    },
    // \Pred (superset, subset, elem)
    Pred {
        superset: Box<SExp>,
        subset: Box<SExp>,
        elem: Box<SExp>,
    },
    // \TypeLift (superset, subset)
    TypeLift {
        superset: Box<SExp>,
        subset: Box<SExp>,
    },
    // --- proposition
    // a = b
    Equal {
        left: Box<SExp>,
        right: Box<SExp>,
    },
    // Bracket type ... \exists (x: A), (x: A | P)
    Exists {
        bind: Bind, // updated to use the new Bind structure
    },
    // --- opaque description (specified but not constructed)
    // \take (x: A) => t or \take (x: A | P) => t
    Take {
        bind: Bind, // updated to use the new Bind structure
        body: Box<SExp>,
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

#[derive(Debug, Clone)]
pub enum ProofBy {
    Construct {
        term: Box<SExp>,
    },
    Exact {
        term: Box<SExp>,
        set: Box<SExp>,
    },
    SubElim {
        superset: Box<SExp>,
        subset: Box<SExp>,
        elem: Box<SExp>,
    },
    IdRefl {
        term: Box<SExp>,
        ty: Box<SExp>,
    },
    IdElim {
        left: Box<SExp>,
        right: Box<SExp>,
        var: Identifier,
        ty: Box<SExp>,
        predicate: Box<SExp>,
    },
    TakeEq {
        func: Box<SExp>,
        elem: Box<SExp>,
    },
    AxiomLEM {
        proposition: Box<SExp>,
    },
    AxiomFunctionExt {
        func1: Box<SExp>,
        func2: Box<SExp>,
        domain: Box<SExp>,
    },
    AxiomEmsembleExt {
        set1: Box<SExp>,
        set2: Box<SExp>,
        superset: Box<SExp>,
    },
}

#[derive(Debug, Clone)]
pub struct Block {
    pub declarations: Vec<Statement>, // sensitive to order
    pub term: Box<SExp>,              // returning term of the block
}

#[derive(Debug, Clone)]
pub enum Statement {
    Fix(Vec<(Identifier, SExp)>), // fix x: A; y: B;
    Have {
        var: Identifier,
        ty: SExp,
        body: SExp,
    }, // have x: A := t;
    Take {
        var: Identifier, // updated to use Identifier directly
        ty: SExp,
        predicate_proof: Option<(Option<SExp>, SExp)>, // no changes needed here
    }, // take x: A; or take x: A | P; or take x: A | h: P;
    Sufficient {
        prop: SExp,
        implication: SExp,
    }, // suffices A by (h: A -> B);
}

#[derive(Debug, Clone)]
pub struct WithGoal {
    pub extended_ctx: Vec<(Identifier, SExp)>, // extended context
    pub goal: SExp,                            // goal to prove
    pub proof_term: SExp,                      // proof term to fill in
}
