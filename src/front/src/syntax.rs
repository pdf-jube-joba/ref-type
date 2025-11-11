// this file describes the surface syntax tree
use either::Either;

// identifier for any naming
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Identifier(pub String);

impl Identifier {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

// token for macros
// which is (not identifier) /\ (not keyword)
// e.g. "+", "*", "==>", "||", ...
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MacroToken(pub String);

// module definition
#[derive(Debug, Clone)]
pub struct Module {
    pub name: Identifier,
    pub parameters: Vec<RightBind>,    // given parameters for module
    pub declarations: Vec<ModuleItem>, // sensitive to order
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
pub enum ModuleAccessPath {
    FromCurrent {
        back_parent: usize,
        args: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
    FromRoot {
        args: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
}

#[derive(Debug, Clone)]
pub enum ModuleItem {
    Definition {
        name: Identifier,
        ty: SExp,
        body: SExp,
    },
    Inductive {
        type_name: Identifier,
        parameters: Vec<RightBind>,
        arity: SExp,
        constructors: Vec<(Identifier, SExp)>,
    },
    ChildModule {
        module: Box<Module>,
    },
    Import {
        path: ModuleAccessPath,
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
    Eval {
        exp: SExp,
    },
    Normalize {
        exp: SExp,
    },
    Check {
        exp: SExp,
        ty: SExp,
    },
    Infer {
        exp: SExp,
    },
}

#[derive(Debug, Clone)]
pub enum MacroExp {
    Exp(SExp),
    Tok(MacroToken),
    Seq(Vec<MacroExp>),
}

#[derive(Debug, Clone)]
pub struct RightBind {
    pub vars: Vec<Identifier>,
    pub ty: Box<SExp>,
}

#[derive(Debug, Clone)]
// general binding syntax
// A = (_: A), (x: A), ((x: A) | P), ((x: A) | h: P),
pub enum Bind {
    Anonymous {
        ty: Box<SExp>,
    },
    Named(RightBind),
    Subset {
        var: Identifier,
        ty: Box<SExp>,
        predicate: Box<SExp>,
    },
    SubsetWithProof {
        var: Identifier,
        ty: Box<SExp>,
        predicate: Box<SExp>,
        proof_var: Identifier,
    },
}

#[derive(Debug, Clone)]
pub enum AccessPath {
    Plain {
        segments: Vec<Identifier>,
    },
    WithParams {
        segments: Vec<Identifier>,
        parameters: Vec<SExp>, // len >= 1
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
    AccessPath(AccessPath),

    // --- macro
    // shared macro for math symbols
    // before type checking, it is expanded to normal expression
    MathMacro {
        tokens: Vec<MacroExp>,
    },
    // macro specified by name
    NamedMacro {
        name: Identifier,
        tokens: Vec<MacroExp>,
    },
    // --- expression with clauses
    // where clauses to define local variables
    Where {
        exp: Box<SExp>,
        clauses: Vec<(Identifier, SExp, SExp)>,
    },
    // solve goals given by type checker
    WithProofs {
        exp: Box<SExp>,
        proofs: Vec<GoalProof>,
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
    Cast {
        exp: Box<SExp>,
        to: Box<SExp>,
    },
    // --- inductive type
    // name of inductive type
    // primitive elimination for inductive type
    // Elim(ind_type_name, eliminated_exp, return_type){cases[0], ..., cases[m]}
    IndElim {
        path: AccessPath,
        elim: Box<SExp>,
        return_type: Box<SExp>,
        cases: Vec<(Identifier, SExp)>,
    },
    IndElimPrim {
        path: AccessPath,
        sort: kernel::exp::Sort,
    },
    // --- set theory
    // \Proof (term) ... "prove this later"
    ProveLater {
        term: Box<SExp>,
    },
    // \Power(power)
    PowerSet {
        set: Box<SExp>,
    },
    // \SubSet (var, set, predicate)
    SubSet {
        var: Identifier,
        set: Box<SExp>,
        predicate: Box<SExp>,
    },
    // \Pred (superset, subset, elem)
    Pred {
        superset: Box<SExp>,
        subset: Box<SExp>,
        element: Box<SExp>,
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

#[derive(Debug, Clone)]
pub enum ProofBy {
    Construct {
        term: Box<SExp>,
    },
    Exact {
        term: Box<SExp>,
        set: Box<SExp>,
    },
    SubsetElim {
        superset: Box<SExp>,
        subset: Box<SExp>,
        elem: Box<SExp>,
    },
    IdRefl {
        term: Box<SExp>,
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
        domain: Box<SExp>,
        codomain: Box<SExp>,
    },
    Axiom(Axiom),
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<Statement>, // sensitive to order
    pub result: Box<SExp>,          // returning term of the block
}

#[derive(Debug, Clone)]
pub enum Statement {
    Fix(Vec<RightBind>), // fix x: A; y: B;
    Let {
        var: Identifier,
        ty: SExp,
        body: SExp,
    }, // have x: A := t;
    Take {
        bind: Bind,
    },
    Sufficient {
        map: SExp,
        map_ty: SExp,
    }, // suffices A by (h: A -> B);
}

#[derive(Debug, Clone)]
pub struct GoalProof {
    pub extended_ctx: Vec<RightBind>, // extended context
    pub goal: SExp,                   // goal to prove
    pub proofby: ProofBy,             // proof term to fill in
}

#[derive(Debug, Clone)]
pub enum Axiom {
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
