// this file describes the surface syntax tree

use either::Either;

// identifier for any naming
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Identifier(pub String);

impl From<Identifier> for kernel::exp::Var {
    fn from(value: Identifier) -> Self {
        kernel::exp::Var::new(&value.0)
    }
}

impl From<&Identifier> for kernel::exp::Var {
    fn from(value: &Identifier) -> Self {
        kernel::exp::Var::new(&value.0)
    }
}

impl From<String> for Identifier {
    fn from(value: String) -> Self {
        Identifier(value)
    }
}

impl From<&str> for Identifier {
    fn from(value: &str) -> Self {
        Identifier(value.to_string())
    }
}

// module definition
#[derive(Debug, Clone)]
pub struct Module {
    pub name: Identifier,
    pub parameters: Vec<(Identifier, SExp)>, // given parameters for module
    pub declarations: Vec<ModuleItem>,       // sensitive to order
}

// parameter instantiated module
// e.g. modA(B := x, C := y)
// WARNING: we assume the order of arguments is the same as parameters
#[derive(Debug, Clone)]
pub struct ModuleInstantiated {
    pub module_name: Identifier,            // name of the module
    pub arguments: Vec<(Identifier, SExp)>, // given arguments for parameters
}

#[derive(Debug, Clone)]
pub enum ModuleItem {
    Definition {
        var: Identifier,
        ty: SExp,
        body: SExp,
    },
    Inductive {
        type_name: Identifier,
        parameter: Vec<(Identifier, SExp)>,
        arity: Box<SExp>,
        constructors: Vec<(Identifier, SExp)>,
    },
    // too complicated to implement for now
    // ChildModule {
    //     module: Box<Module>,
    // },
    Import {
        path: ModuleInstantiated,
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
pub enum MacroExp {
    Exp(SExp),
    Tok(MacroToken),
    Seq(Vec<MacroExp>),
}

#[derive(Debug, Clone)]
// general binding syntax
// A = (_: A), (x: A), (x: A | P), (x: A | h: P),
pub enum Bind {
    Anonymous {
        ty: Box<SExp>,
    },
    Named {
        var: Identifier,
        ty: Box<SExp>,
    },
    Subset {
        var: Identifier,
        ty: Box<SExp>,
        predicate: Box<SExp>,
    },
    SubsetWithProof {
        var: Identifier,
        ty: Box<SExp>,
        predicate: Box<SExp>,
        proof: Identifier,
    },
}

// this is internal representation
#[derive(Debug, Clone)]
pub enum SExp {
    // accessessing something
    // len == 1 => locally binded variable | current module defined item (definition, inductive type name) | module parameter
    // len == 2 => named module's item access | current module's inductive type constructor access
    // l3n == 3 => named module's inductive type constructor access
    // too ad-hoc TODO: improve this design
    AccessPath(Vec<Identifier>),

    // --- macro
    // shared macro for math symbols
    // before type checking, it is expanded to normal expression
    MathMacro {
        tokens: Box<MacroExp>,
    },
    // macro specified by name
    NamedMacro {
        name: Identifier,
        tokens: Box<MacroExp>,
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
    // primitive elimination for inductive type
    // Elim(ind_type_name, eliminated_exp, return_type){cases[0], ..., cases[m]}
    IndElim {
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
