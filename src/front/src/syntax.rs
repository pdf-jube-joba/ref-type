// this file describes the surface syntax tree
use either::Either;
use kernel::exp::{DefinedConstant, Exp, Var};
use kernel::inductive::{CtorBinder, InductiveTypeSpecs};
use kernel::utils;
use std::rc::Rc;

// identifier for any naming
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Identifier(pub String);

impl Identifier {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

// token for macros
//   which is (not identifier) /\ (not keyword)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MacroToken(pub String);

// module definition
#[derive(Debug, Clone)]
pub struct Module {
    pub name: Identifier,
    pub parameters: Vec<RightBind>,    // given parameters for module
    pub declarations: Vec<ModuleItem>, // sensitive to order
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
        indices: Vec<RightBind>,
        sort: kernel::exp::Sort,
        constructors: Vec<(Identifier, Vec<RightBind>, SExp)>,
    },
    Record {
        type_name: Identifier,
        parameters: Vec<RightBind>,
        sort: kernel::exp::Sort,
        fields: Vec<(Identifier, SExp)>,
    },
    ChildModule {
        module: Box<Module>,
    },
    Import {
        path: ModuleInstantiatePath,
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
pub enum ModuleInstantiatePath {
    FromCurrent {
        back_parent: usize,
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
    FromRoot {
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
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
// some access path to access defined constant or inductive type
pub enum LocalAccess {
    // accessing inductive type or defined constant
    Current {
        access: Identifier,
    },
    Named {
        access: Identifier,
        child: Identifier,
    },
}

// this is internal representation
#[derive(Debug, Clone)]
pub enum SExp {
    // --- access something
    // variable binded by lambda or somethings, defined constant, inductive type, record type (itself)
    AccessPath {
        access: LocalAccess,
        parameters: Vec<SExp>,
    },
    // accessing constructor of the inductive type, accessing field of record type
    AssociatedAccess {
        base: Box<SExp>,
        field: Identifier,
    },

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
    // Elim(ind_type_name, eliminated_exp, return_type){cases[0], ..., cases[m]}
    IndElim {
        path: LocalAccess,
        elim: Box<SExp>,
        return_type: Box<SExp>,
        cases: Vec<(Identifier, SExp)>,
    },
    // primitive elimination for inductive type
    IndElimPrim {
        path: LocalAccess,
        parameters: Vec<SExp>,
        sort: kernel::exp::Sort,
    },

    // --- record type
    // nominal style
    RecordTypeCtor {
        access: LocalAccess,
        parameters: Vec<SExp>,
        fields: Vec<(Identifier, SExp)>,
    },

    // --- set theory
    // \Proof (term) ... "prove this later"
    ProveLater {
        prop: Box<SExp>,
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
    ProofTermRaw(SProveCommandBy),
    // --- block of statements
    Block(Block),
}

#[derive(Debug, Clone)]
pub enum SProveCommandBy {
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
    pub proofby: SProveCommandBy,     // proof term to fill in
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

#[derive(Debug, Clone)]
pub struct ModItemDefinition {
    pub name: Identifier,
    pub body: Rc<DefinedConstant>,
}

#[derive(Debug, Clone)]
pub struct ModItemInductive {
    pub type_name: Identifier,
    pub ctor_names: Vec<Identifier>,
    pub ind_defs: Rc<InductiveTypeSpecs>,
}

#[derive(Debug, Clone)]
pub struct ModItemRecord {
    pub type_name: Identifier,
    pub rc_spec_as_indtype: Rc<InductiveTypeSpecs>,
}

impl ModItemRecord {
    // get projection expression for field_name, returns None if field_name not found
    // (e: Record {}) => elim e \in Record return { mk: <primitive_recursion>}
    // where primitive_recursion = (x1: T1) => ... => xi
    pub fn field_projection(
        &self,
        e: &Exp,
        field_name: &Identifier,
        parameters: &Vec<Exp>,
    ) -> Option<Exp> {
        // this should always have only one constructor
        let ctor = &self.rc_spec_as_indtype.constructors[0];
        let telescope = ctor
            .telescope
            .iter()
            .map(|bind| {
                let CtorBinder::Simple((id, ty)) = bind else {
                    unreachable!("record type constructor should only have simple binders");
                };
                (id.clone(), ty.clone())
            })
            .collect::<Vec<_>>();

        let (field_var, field_ty) = telescope
            .iter()
            .find(|(id, _)| id.as_str() == field_name.as_str())?
            .clone();

        let prec = utils::assoc_lam(telescope, Exp::Var(field_var));

        let elim = Exp::IndElim {
            indspec: self.rc_spec_as_indtype.clone(),
            elim: e.clone().into(),
            return_type: Exp::Prod {
                var: Var::new("record"),
                ty: Exp::IndType {
                    indspec: self.rc_spec_as_indtype.clone(),
                    parameters: parameters.clone(),
                }
                .into(),
                body: Box::new(field_ty),
            }
            .into(),
            cases: vec![prec],
        };

        Some(elim)
    }
}

#[derive(Debug, Clone)]
pub enum ModuleItemAccessible {
    Definition(ModItemDefinition),
    Inductive(ModItemInductive),
    // we use inductive type to represent record type
    Record(ModItemRecord),
}
