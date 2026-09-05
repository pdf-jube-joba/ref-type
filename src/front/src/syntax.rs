// this file describes the surface syntax tree
use kernel::exp::{Exp, Node};
use kernel::ids::{DefId, InductiveId, ModuleId};
use kernel::inductive::CtorBinder;
use kernel::sort::Sort;
use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct SourceSpan {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SurfaceMeta {
    /// `_`: solve by constraints, but report ambiguity rather than a goal.
    Implicit,
    /// Bare `?`: a fresh proof-search goal at every occurrence.
    Goal,
    /// `?N`: occurrences with the same number share one metavariable within
    /// the current elaboration unit.
    Named(u32),
}

// identifier for any naming
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Identifier(pub String);

impl Identifier {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

// token for macros
//   which is (not identifier) /\ (not keyword)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct MacroToken(pub String);

// module definition
#[derive(Debug, Clone, Serialize)]
pub struct Module {
    pub name: Identifier,
    pub parameters: Vec<RightBind>, // given parameters for module
    pub body: ModuleBody,
}

#[derive(Debug, Clone, Serialize)]
pub enum ModuleBody {
    Inline(Vec<ModuleItem>), // sensitive to order
    External,
}

#[derive(Debug, Clone, Serialize)]
pub enum MacroSeqAtom {
    Capture(Identifier),
    Tok(MacroToken),
    Quoted(String),
    Seq(Vec<MacroSeqAtom>),
}

#[derive(Debug, Clone, Serialize)]
pub enum ModuleItem {
    Definition {
        owner: Option<AssociatedOwner>,
        name: Identifier,
        binders: Vec<RightBind>,
        ty: SExp,
        body: SExp,
        proof: Option<ProofBlock>,
    },
    Inductive {
        type_name: Identifier,
        parameters: Vec<RightBind>,
        indices: Vec<RightBind>,
        kind: InductiveKind,
        constructors: Vec<(Identifier, Vec<RightBind>, SExp)>,
    },
    Record {
        type_name: Identifier,
        parameters: Vec<RightBind>,
        kind: StructureKind,
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
        name: Identifier,
        before: Vec<MacroSeqAtom>,
        after: SExp,
    },
    UserMacro {
        name: Identifier,
        before: Vec<MacroSeqAtom>,
        after: SExp,
    },
    UseMacro {
        import_name: Identifier,
        macro_name: Identifier,
    },
    Eval {
        exp: SExp,
        proof: Option<ProofBlock>,
    },
    Normalize {
        exp: SExp,
        proof: Option<ProofBlock>,
    },
    Check {
        exp: SExp,
        ty: SExp,
        proof: Option<ProofBlock>,
    },
    Infer {
        exp: SExp,
        proof: Option<ProofBlock>,
    },
}

#[derive(Debug, Clone, Serialize)]
pub struct ProofBlock {
    pub entries: Vec<ProofEntry>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ProofEntry {
    pub binders: Vec<RightBind>,
    pub proposition: SExp,
    pub witness: SExp,
}

#[derive(Debug, Clone, Serialize)]
pub struct AssociatedOwner {
    pub type_name: Identifier,
    pub parameters: Vec<RightBind>,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub enum StructureKind {
    Pts(Sort),
    Program,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub enum InductiveKind {
    Pts(Sort),
    Program,
}

#[derive(Debug, Clone, Serialize)]
pub enum ModuleInstantiatePath {
    FromCurrent {
        back_parent: usize,
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
    FromRoot {
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
}

#[derive(Debug, Clone, Serialize)]
pub enum MacroExp {
    Exp(SExp),
    Tok(MacroToken),
    Quoted(String),
    Seq(Vec<MacroExp>),
}

#[derive(Debug, Clone, Serialize)]
pub struct RightBind {
    pub vars: Vec<Identifier>,
    pub ty: Box<SExp>,
}

pub struct TelescopeRightbind(pub Vec<RightBind>);

#[derive(Debug, Clone, Serialize)]
// general binding syntax
// A = (_: A), (x: A), ((x: A) | P), ((x: A) | h: P),
pub enum Bind {
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

#[derive(Debug, Clone, Serialize)]
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
    /// An access resolved in a macro's definition environment.
    Resolved {
        module: ModuleId,
        access: Identifier,
    },
}

// this is internal representation
#[derive(Debug, Clone, Serialize)]
pub enum SExp {
    Meta {
        kind: SurfaceMeta,
        span: SourceSpan,
    },
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
        /// `None` for source calls; templates pin nested calls to their
        /// definition environment before they are registered.
        scope: Option<ModuleId>,
        /// For calls originating in a template, only declarations older than
        /// this order are visible.
        max_order: Option<u64>,
        depth: u16,
    },
    // macro specified by name
    NamedMacro {
        name: Identifier,
        tokens: Vec<MacroExp>,
        scope: Option<ModuleId>,
        max_order: Option<u64>,
        depth: u16,
    },
    /// A reference to a pattern capture. Only valid in macro templates.
    MacroParameter(Identifier),
    /// A core expression captured while resolving a macro template (currently
    /// used for module parameters). It is remapped when a module is instantiated.
    ResolvedExp(Exp),

    // --- expression with clauses
    // where clauses to define local variables
    Where {
        exp: Box<SExp>,
        clauses: Vec<(Identifier, SExp, SExp)>,
    },
    // --- lambda calculus
    // sort: Prop, Set(i), Univ, Type
    Sort(Sort),
    /// Surface-only marker accepted in module/type-parameter binders and as
    /// the result kind of a Program datatype declaration.
    ValueType,
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
    // subset introduction: `subset` is checked against `PowerSet(superset)`,
    // `element` against `superset`, and `proof` against their membership.
    SubsetIntro {
        superset: Box<SExp>,
        subset: Box<SExp>,
        element: Box<SExp>,
        proof: Box<SExp>,
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
        sort: Sort,
    },

    // --- CBPV Program ------------------------------------------------------
    ThunkType {
        computation_ty: Box<SExp>,
    },
    ReturnType {
        value_ty: Box<SExp>,
    },
    ComputationFunction {
        domain: Box<SExp>,
        codomain: Box<SExp>,
    },
    Thunk {
        computation: Box<SExp>,
    },
    Return {
        value: Box<SExp>,
    },
    Force {
        value: Box<SExp>,
    },
    ComputationLam {
        var: Identifier,
        value_ty: Box<SExp>,
        body: Box<SExp>,
    },
    ComputationApp {
        computation: Box<SExp>,
        value: Box<SExp>,
    },
    Sequence {
        computation: Box<SExp>,
        var: Identifier,
        value_ty: Box<SExp>,
        body: Box<SExp>,
    },
    ValueLet {
        var: Identifier,
        value: Box<SExp>,
        body: Box<SExp>,
    },
    ProgramCase {
        path: LocalAccess,
        scrutinee: Box<SExp>,
        branches: Vec<(Identifier, Vec<Identifier>, SExp)>,
    },

    // --- certified general recursion over Program values
    RunStep {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
    },
    Continue {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        next: Box<SExp>,
    },
    Finish {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        output: Box<SExp>,
    },
    Acc {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        step: Box<SExp>,
        state: Box<SExp>,
    },
    RfType {
        compute_ty: Box<SExp>,
    },
    RfTerm {
        compute_ty: Box<SExp>,
        term: Box<SExp>,
    },
    Run {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        step: Box<SExp>,
        initial: Box<SExp>,
    },
    RunCase {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        step: Box<SExp>,
        initial: Box<SExp>,
        transition: Box<SExp>,
    },
    RunStepRec {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        motive: Box<SExp>,
        on_continue: Box<SExp>,
        on_finish: Box<SExp>,
        scrutinee: Box<SExp>,
    },
    Proof {
        proposition: Box<SExp>,
    },
    BoxType {
        program_ty: Box<SExp>,
    },
    BoxProgram {
        program_ty: Box<SExp>,
        program: Box<SExp>,
    },
    ForceBox {
        program_ty: Box<SExp>,
        boxed: Box<SExp>,
    },
    BoxApp {
        function: Box<SExp>,
        argument: Box<SExp>,
    },
    AccIntro {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        step: Box<SExp>,
        state: Box<SExp>,
        predecessors: Box<SExp>,
    },
    AccDescent {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        step: Box<SExp>,
        from: Box<SExp>,
        to: Box<SExp>,
        accessibility: Box<SExp>,
        transition: Box<SExp>,
    },

    // --- record type
    // nominal style
    RecordTypeCtor {
        access: LocalAccess,
        parameters: Vec<SExp>,
        fields: Vec<(Identifier, SExp)>,
    },

    // --- set theory
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
    TakeSet {
        bind: Bind, // updated to use the new Bind structure
        body: Box<SExp>,
        existence: Box<SExp>,
        uniqueness: Box<SExp>,
    },
    TakeProp {
        bind: Bind,
        body: Box<SExp>,
        existence: Box<SExp>,
    },
    ExistsIntro {
        element: Box<SExp>,
        set: Box<SExp>,
    },
    SubsetElim {
        element: Box<SExp>,
        subset: Box<SExp>,
        superset: Box<SExp>,
    },
    IdRefl {
        element: Box<SExp>,
    },
    IdElim {
        left: Box<SExp>,
        right: Box<SExp>,
        var: Identifier,
        ty: Box<SExp>,
        predicate: Box<SExp>,
        base: Box<SExp>,
        equality: Box<SExp>,
    },
    AxiomSetExt {
        left: Box<SExp>,
        right: Box<SExp>,
        left_to_right: Box<SExp>,
        right_to_left: Box<SExp>,
    },
    AxiomFunExt {
        left: Box<SExp>,
        right: Box<SExp>,
        pointwise: Box<SExp>,
    },
    AxiomClassicalIndefiniteChoice {
        domain: Box<SExp>,
        family: Box<SExp>,
        inhabited: Box<SExp>,
    },
    TakeEq {
        func: Box<SExp>,
        domain: Box<SExp>,
        codomain: Box<SExp>,
        element: Box<SExp>,
        existence: Box<SExp>,
        uniqueness: Box<SExp>,
    },
    // --- block of statements
    Block(Block),
}

#[derive(Debug, Clone, Serialize)]
pub struct Block {
    pub statements: Vec<Statement>, // sensitive to order
    pub result: Box<SExp>,          // returning term of the block
}

#[derive(Debug, Clone, Serialize)]
pub enum Statement {
    Fix(Vec<RightBind>), // fix x: A; y: B;
    Let {
        var: Identifier,
        ty: SExp,
        body: SExp,
    }, // have x: A := t;
    TakeSet {
        bind: Bind,
        existence: SExp,
        uniqueness: SExp,
    },
    TakeProp {
        bind: Bind,
        existence: SExp,
    },
    Sufficient {
        map: SExp,
        map_ty: SExp,
    }, // suffices A by (h: A -> B);
}

#[derive(Debug, Clone)]
pub struct ModItemDefinition {
    pub def_name: Identifier,
    pub definition: DefId,
}

#[derive(Debug, Clone)]
pub struct ModItemInductive {
    pub type_name: Identifier,
    pub ctor_names: Vec<Identifier>,
    pub inductive: InductiveId,
    pub associated_definitions: Vec<(Identifier, DefId)>,
}

#[derive(Debug, Clone)]
pub struct ModItemProgramInductive {
    pub type_name: Identifier,
    pub ctor_names: Vec<Identifier>,
    pub inductive: kernel::ids::ProgramInductiveId,
    pub reflected: InductiveId,
    pub associated_definitions: Vec<(Identifier, DefId)>,
}

#[derive(Debug, Clone)]
pub struct ModItemRecord {
    pub type_name: Identifier,
    pub inductive: InductiveId,
    pub associated_definitions: Vec<(Identifier, DefId)>,
}

impl ModItemRecord {
    // get projection expression for field_name, returns None if field_name not found
    // (e: Record {}) => elim e \in Record return { mk: <primitive_recursion>}
    // where primitive_recursion = (x1: T1) => ... => xi
    pub fn field_projection(
        &self,
        env: &kernel::environment::CrateEnv,
        e: Exp,
        field_name: &Identifier,
        parameters: &[Exp],
    ) -> Option<Exp> {
        let arena = env.arena();
        let spec = env.inductive(self.inductive);
        // this should always have only one constructor
        let ctor = &spec.constructors()[0];
        let telescope = ctor
            .telescope
            .iter()
            .map(|bind| {
                let CtorBinder::Simple((id, ty)) = bind else {
                    unreachable!("record type constructor should only have simple binders");
                };
                (*id, *ty)
            })
            .collect::<Vec<_>>();

        let (field_index, _) = telescope
            .iter()
            .enumerate()
            .find(|(_, (id, _))| env.symbol(*id) == field_name.as_str())?;
        Some(arena.alloc(Node::IndProjection {
            indspec: self.inductive,
            parameters: parameters.to_vec(),
            value: e,
            field: field_index,
        }))
    }
}

#[derive(Debug, Clone)]
pub enum ModuleItemAccessible {
    Definition(ModItemDefinition),
    Inductive(ModItemInductive),
    // we use inductive type to represent record type
    Record(ModItemRecord),
    ProgramInductive(ModItemProgramInductive),
}
