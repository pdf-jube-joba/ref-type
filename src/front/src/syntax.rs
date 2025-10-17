// this file describes the surface syntax tree

use either::Either;

// identifier for any naming
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Identifier(pub String);

// module definition
#[derive(Debug, Clone)]
pub struct Module {
    pub name: Identifier,
    pub parameters: Vec<(Identifier, Exp)>, // given parameters for module
    pub declarations: Vec<ModuleItem>,      // sensitive to order
}

// parameter instantiated module
// e.g. modA(B := x, C := y)
#[derive(Debug, Clone)]
pub struct ModuleInstantiated {
    pub module_name: Identifier,           // name of the module
    pub arguments: Vec<(Identifier, Exp)>, // given arguments for parameters
}

// path of module access
// pattern 1 (absolute path): root.name1(arg1, ...).name2(...).name3(...)
// pattern 2 (relatice path): name1(arg1, ...).name2(...).name3(...), or parent.parent. ... .parent.name1(...).name2(...).name3(...)
// pattern 3 (start from named): name.name2(...).name3(...)
#[derive(Debug, Clone)]
pub enum ModPath {
    Root(Vec<ModuleInstantiated>),    // absolute path from project root
    Current(Vec<ModuleInstantiated>), // relative path from current module
    Name(Identifier, Vec<ModuleInstantiated>), // relative path from named module
}

#[derive(Debug, Clone)]
pub enum ModuleItem {
    Definition {
        var: Identifier,
        ty: Exp,
        body: Exp,
    },
    Inductive {
        ind_defs: InductiveTypeSpecs,
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
        after: Vec<Either<Exp, Identifier>>,
    },
    UserMacro {
        name: Identifier,
        before: Vec<Either<MacroToken, Identifier>>,
        after: Vec<Identifier>,
    },
}

#[derive(Debug, Clone)]
pub struct InductiveTypeSpecs {
    pub type_name: Identifier,
    pub parameter: Vec<(Identifier, Exp)>,
    pub indices: Vec<(Identifier, Exp)>,
    pub sort: Sort,
    pub constructors: Vec<(Identifier, Vec<ParamCstSyntax>, Vec<Exp>)>,
}

#[derive(Debug, Clone)]
pub enum ParamCstSyntax {
    Positive((Vec<(Identifier, Exp)>, Vec<Exp>)),
    Simple((Identifier, Exp)),
}

#[derive(Debug, Clone)]
// general binding syntax
// A = (_: A), (x: A), (x: A | P), (x: A | h: P),
// binding variable now uses Identifier directly
pub struct Bind {
    pub var: Identifier, // variable name (was Option<Name>)
    pub ty: Box<Exp>,
    pub predicate: Option<(Option<Identifier>, Box<Exp>)>, // predicate now uses Identifier
}

// this is internal representation
#[derive(Debug, Clone)]
pub enum Exp {
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
        clauses: Vec<(Identifier, Exp, Exp)>,
    },
    // goal proving  given by type checker
    WithProof {
        exp: Box<Exp>,
        proofs: Vec<WithGoal>,
    },
    // --- lambda calculus
    // sort: Prop, Set(i), Univ, Type
    Sort(Sort),
    // variable defined by name
    Var(Identifier), // updated to use Identifier directly
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
    Annotation {
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
        var: Identifier,
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
        bind: Bind, // updated to use the new Bind structure
    },
    // --- opaque description (specified but not constructed)
    // \take (x: A) => t or \take (x: A | P) => t
    Take {
        bind: Bind, // updated to use the new Bind structure
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
        var: Identifier,
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
    Fix(Vec<(Identifier, Exp)>), // fix x: A; y: B;
    Have {
        var: Identifier,
        ty: Exp,
        body: Exp,
    }, // have x: A := t;
    Take {
        var: Identifier, // updated to use Identifier directly
        ty: Exp,
        predicate_proof: Option<(Option<Exp>, Exp)>, // no changes needed here
    }, // take x: A; or take x: A | P; or take x: A | h: P;
    Sufficient {
        prop: Exp,
        implication: Exp,
    }, // suffices A by (h: A -> B);
}

#[derive(Debug, Clone)]
pub struct WithGoal {
    pub extended_ctx: Vec<(Identifier, Exp)>, // extended context
    pub goal: Exp,                            // goal to prove
    pub proof_term: Exp,                      // proof term to fill in
}
