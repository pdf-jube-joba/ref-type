//! Source syntax, without resolution or elaboration state.

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Set(usize),     // predicative SET(i):
    SetKind(usize), // SET(i): SETKind(i)
    Prop,           // proposition
    PropKind,       // Prop: PropKind
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceSpan {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaKind {
    /// `_`: solve by constraints, but report ambiguity rather than a goal.
    Implicit,
    /// Bare `?`: a fresh proof-search goal at every occurrence.
    Goal,
    /// `?N`: occurrences with the same number share one metavariable within
    /// the current elaboration unit.
    Named(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SurfaceMeta {
    pub kind: MetaKind,
}

impl SurfaceMeta {
    pub fn implicit() -> Self {
        Self::source(MetaKind::Implicit)
    }
    pub fn goal() -> Self {
        Self::source(MetaKind::Goal)
    }
    pub fn named(number: u32) -> Self {
        Self::source(MetaKind::Named(number))
    }
    fn source(kind: MetaKind) -> Self {
        Self { kind }
    }
}

/// A source file identity, retained together with the original text.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SourceId(pub std::path::PathBuf);

#[derive(Debug)]
pub struct SourceFile {
    pub id: SourceId,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct SourceLocation {
    pub source: std::sync::Arc<SourceFile>,
    pub span: SourceSpan,
}

impl SourceLocation {
    pub fn render(&self) -> String {
        let text = &self.source.text;
        let mut start = self.span.start.min(text.len());
        while !text.is_char_boundary(start) {
            start -= 1;
        }
        let line_start = text[..start].rfind('\n').map_or(0, |at| at + 1);
        let line_end = text[start..].find('\n').map_or(text.len(), |at| start + at);
        let line = text[..start].bytes().filter(|byte| *byte == b'\n').count() + 1;
        let column = text[line_start..start].chars().count() + 1;
        let mut end = self.span.end.min(line_end).max(start);
        while !text.is_char_boundary(end) {
            end -= 1;
        }
        let width = text[start..end].chars().count().max(1);
        format!(
            "{}:{line}:{column}\n  |\n{line:>2} | {}\n  | {}{}",
            self.source.id.0.display(),
            &text[line_start..line_end],
            " ".repeat(column - 1),
            "^".repeat(width)
        )
    }
}

// identifier for any naming
#[derive(Clone)]
pub struct Identifier<S = AstSource>(pub String, pub Option<S>);

impl<S> std::fmt::Debug for Identifier<S> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_tuple("Identifier").field(&self.0).finish()
    }
}

impl<S> PartialEq for Identifier<S> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<S> Eq for Identifier<S> {}
impl<S> PartialOrd for Identifier<S> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<S> Ord for Identifier<S> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}
impl<S> std::hash::Hash for Identifier<S> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.0, state);
    }
}

impl<S> Identifier<S> {
    pub fn new(name: String) -> Self {
        Self(name, None)
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Identifier {
    pub fn with_span(mut self, span: SourceSpan) -> Self {
        self.1 = Some(AstSource::new(span));
        self
    }
    pub fn span(&self) -> Option<SourceSpan> {
        self.1.map(|source| source.span)
    }
}

impl Identifier<AstId> {
    pub fn origin(&self) -> Option<AstId> {
        self.1
    }
}

impl From<Identifier> for Identifier<AstId> {
    fn from(value: Identifier) -> Self {
        Self(value.0, value.1.map(|source| source.id))
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
    pub parameters: Vec<RightBind>, // given parameters for module
    pub body: ModuleBody,
    pub span: SourceSpan,
    pub declaration_spans: Vec<SourceSpan>,
    pub source: Option<std::sync::Arc<SourceFile>>,
    pub header_source: Option<std::sync::Arc<SourceFile>>,
}

#[derive(Debug, Clone)]
pub enum ModuleBody {
    Inline(Vec<ModuleItem>), // sensitive to order
    External,
}

#[derive(Debug, Clone)]
pub enum MacroSeqAtom<S = AstSource> {
    Capture(Identifier<S>),
    TokenCapture(Identifier<S>),
    Rest(Identifier<S>),
    Tok(MacroToken),
    Quoted(String),
    Seq(Vec<MacroSeqAtom<S>>),
}

#[derive(Debug, Clone)]
pub enum TokenMatchPattern<S = AstSource> {
    Token(MacroSeqAtom<S>),
    Sequence(Vec<MacroSeqAtom<S>>),
    Default,
}

impl From<MacroSeqAtom> for MacroSeqAtom<AstId> {
    fn from(value: MacroSeqAtom) -> Self {
        match value {
            MacroSeqAtom::Capture(name) => Self::Capture(name.into()),
            MacroSeqAtom::TokenCapture(name) => Self::TokenCapture(name.into()),
            MacroSeqAtom::Rest(name) => Self::Rest(name.into()),
            MacroSeqAtom::Tok(token) => Self::Tok(token),
            MacroSeqAtom::Quoted(text) => Self::Quoted(text),
            MacroSeqAtom::Seq(tokens) => Self::Seq(tokens.into_iter().map(Into::into).collect()),
        }
    }
}

impl From<TokenMatchPattern> for TokenMatchPattern<AstId> {
    fn from(value: TokenMatchPattern) -> Self {
        match value {
            TokenMatchPattern::Token(token) => Self::Token(token.into()),
            TokenMatchPattern::Sequence(tokens) => {
                Self::Sequence(tokens.into_iter().map(Into::into).collect())
            }
            TokenMatchPattern::Default => Self::Default,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ModuleItem {
    /// A recovered declaration remains in the outline and still shadows its name.
    Error {
        name: Option<Identifier>,
        message: String,
    },
    Definition {
        owner: Option<AssociatedOwner>,
        name: Identifier,
        binders: Vec<RightBind>,
        ty: SExp,
        body: SExp,
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
        kind: InductiveKind,
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
    },
    Normalize {
        exp: SExp,
    },
    ComputationEval {
        exp: ComputationTermExp,
    },
    ComputationNormalize {
        exp: ComputationTermExp,
    },
    ValueCheck {
        exp: ValueTermExp,
        ty: ValueTypeExp,
    },
    ComputationCheck {
        exp: ComputationTermExp,
        ty: ComputationTypeExp,
    },
    ValueInfer {
        exp: ValueTermExp,
    },
    ComputationInfer {
        exp: ComputationTermExp,
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
pub struct AssociatedOwner {
    pub type_name: Identifier,
    pub parameters: Vec<RightBind>,
}

#[derive(Debug, Clone, Copy)]
pub enum InductiveKind {
    Pts(Sort),
    Program,
}

#[derive(Debug, Clone)]
pub enum ModuleInstantiatePath {
    FromPackage {
        package: Identifier,
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
    FromCurrent {
        back_parent: usize,
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
    FromRoot {
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
    FromImport {
        import_name: Identifier,
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
}

#[derive(Debug, Clone)]
pub enum MacroExp {
    RawExp(SExp),
    /// A bare template-sequence name, resolved during template preparation.
    /// Keeping it separate preserves the expression boundary of `{ ... }`.
    TemplateName(Identifier),
    TokenParameter(Identifier),
    Splice(Identifier),
    Tok(MacroToken),
    Quoted(String),
    Seq(Vec<MacroExp>),
}

#[derive(Debug, Clone)]
pub struct RightBind {
    pub vars: Vec<Identifier>,
    pub ty: Box<SExp>,
}

/// Surface Program syntax is split into the same four categories as the
/// kernel.  Parsing a category-specific declaration performs this
/// classification before elaboration.
pub type ValueTypeExp = Expr<ValueTypeExpKind>;

#[derive(Debug, Clone)]
pub enum ValueTypeExpKind {
    Meta {
        kind: SurfaceMeta,
        token: AstSource,
    },
    Access {
        access: LocalAccess,
        parameters: Vec<ValueTypeExp>,
    },
    Thunk(Box<ComputationTypeExp>),
    RunStep {
        state_ty: Box<ValueTypeExp>,
        result_ty: Box<ValueTypeExp>,
    },
}

pub type ComputationTypeExp = Expr<ComputationTypeExpKind>;

#[derive(Debug, Clone)]
pub enum ComputationTypeExpKind {
    Meta {
        kind: SurfaceMeta,
        token: AstSource,
    },
    Return(Box<ValueTypeExp>),
    Function {
        domain: Box<ValueTypeExp>,
        codomain: Box<ComputationTypeExp>,
    },
}

pub type ValueTermExp = Expr<ValueTermExpKind>;

#[derive(Debug, Clone)]
pub enum ValueTermExpKind {
    Meta {
        kind: SurfaceMeta,
        token: AstSource,
    },
    Access(LocalAccess),
    Record {
        datatype: LocalAccess,
        parameters: Vec<ValueTypeExp>,
        fields: Vec<(Identifier, ValueTermExp)>,
    },
    Constructor {
        datatype: LocalAccess,
        constructor: Identifier,
        parameters: Vec<ValueTypeExp>,
        fields: Vec<ValueTermExp>,
    },
    Thunk(Box<ComputationTermExp>),
    Continue {
        state_ty: Box<ValueTypeExp>,
        result_ty: Box<ValueTypeExp>,
        next: Box<ValueTermExp>,
    },
    Finish {
        state_ty: Box<ValueTypeExp>,
        result_ty: Box<ValueTypeExp>,
        output: Box<ValueTermExp>,
    },
}

pub type ComputationTermExp = Expr<ComputationTermExpKind>;

#[derive(Debug, Clone)]
pub enum ComputationTermExpKind {
    Meta {
        kind: SurfaceMeta,
        token: AstSource,
    },
    Access(LocalAccess),
    Associated {
        datatype: LocalAccess,
        item: Identifier,
        parameters: Vec<ValueTypeExp>,
    },
    InferredProjection {
        value: Box<ValueTermExp>,
        field: Identifier,
    },
    Return(Box<ValueTermExp>),
    Force(Box<ValueTermExp>),
    Lambda {
        var: Identifier,
        value_ty: Box<ValueTypeExp>,
        body: Box<ComputationTermExp>,
    },
    Application {
        function: ProgramFunctionExp,
        arguments: Vec<ValueTermExp>,
    },
    Sequence {
        computation: Box<ComputationTermExp>,
        var: Identifier,
        value_ty: Box<ValueTypeExp>,
        body: Box<ComputationTermExp>,
    },
    ValueLet {
        var: Identifier,
        value_ty: Box<ValueTypeExp>,
        value: Box<ValueTermExp>,
        body: Box<ComputationTermExp>,
    },
    Case {
        datatype: LocalAccess,
        scrutinee: Box<ValueTermExp>,
        branches: Vec<(Identifier, Vec<Identifier>, ComputationTermExp)>,
    },
    Run {
        state_ty: Box<ValueTypeExp>,
        result_ty: Box<ValueTypeExp>,
        step: Box<ValueTermExp>,
        initial: Box<ValueTermExp>,
        accessibility: Box<SExp>,
    },
    RunCase {
        state_ty: Box<ValueTypeExp>,
        result_ty: Box<ValueTypeExp>,
        step: Box<ValueTermExp>,
        initial: Box<ValueTermExp>,
        transition: Box<ComputationTermExp>,
        accessibility: Box<SExp>,
        transition_equality: Box<SExp>,
    },
}

/// The head of an ordinary Program application. An access is deliberately
/// left unclassified until elaboration, where name resolution can distinguish
/// local values from global value and computation definitions.
pub type ProgramFunctionExp = Expr<ProgramFunctionExpKind>;

#[derive(Debug, Clone)]
pub enum ProgramFunctionExpKind {
    Access(LocalAccess),
    Associated {
        datatype: LocalAccess,
        item: Identifier,
        parameters: Vec<ValueTypeExp>,
    },
    Value(Box<ValueTermExp>),
    Computation(Box<ComputationTermExp>),
}

#[derive(Debug, Clone)]
// general binding syntax
// (x: A), (x: A \where P), (x: A \where P \as h).
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

impl std::fmt::Display for LocalAccess {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Current { access } => formatter.write_str(access.as_str()),
            Self::Named { access, child } => {
                write!(formatter, "{}.{}", access.as_str(), child.as_str())
            }
        }
    }
}

/// Identity of a parsed expression occurrence; clones retain the same identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AstId(u64);

impl AstId {
    pub fn fresh() -> Self {
        static NEXT_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        Self(NEXT_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AstSource {
    pub id: AstId,
    pub span: SourceSpan,
}

impl AstSource {
    pub fn new(span: SourceSpan) -> Self {
        Self {
            id: AstId::fresh(),
            span,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Expr<K> {
    pub kind: K,
    pub source: Option<AstSource>,
}

pub type SExp = Expr<SExpKind>;

impl<K> From<K> for Expr<K> {
    fn from(kind: K) -> Self {
        Self { kind, source: None }
    }
}

impl<K> Expr<K> {
    pub fn with_span(mut self, span: SourceSpan) -> Self {
        if self.source.is_some_and(|source| source.span == span) {
            return self;
        }
        self.source = Some(AstSource::new(span));
        self
    }
}

#[derive(Debug, Clone)]
pub enum SExpKind {
    Meta {
        kind: SurfaceMeta,
        token: AstSource,
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
    InferredProjection {
        value: Box<SExp>,
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
    /// A reference to a pattern capture. Only valid in macro templates.
    MacroParameter(Identifier),
    /// Expansion-time matching, available only in named macro templates.
    TokenMatch {
        target: Identifier,
        branches: Vec<(TokenMatchPattern, SExp)>,
    },

    // --- expression with clauses
    // where clauses to define local variables
    Where {
        exp: Box<SExp>,
        clauses: Vec<(Identifier, SExp, SExp)>,
    },
    // --- lambda calculus
    // sort: Prop, PropKind, Set(i), SetKind(i)
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
    IndCase {
        path: LocalAccess,
        scrutinee: Box<SExp>,
        return_type: Box<SExp>,
        branches: Vec<(Identifier, SExp)>,
    },
    Induction {
        binder: RightBind,
        return_type: Box<SExp>,
        cases: Vec<(Identifier, SExp)>,
    },
    // primitive elimination for inductive type
    IndElimPrim {
        path: LocalAccess,
        parameters: Vec<SExp>,
        motive: Box<SExp>,
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
    Sequence {
        computation: Box<SExp>,
        var: Identifier,
        value_ty: Box<SExp>,
        body: Box<SExp>,
    },
    ValueLet {
        var: Identifier,
        value_ty: Box<SExp>,
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
    Run {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        step: Box<SExp>,
        initial: Box<SExp>,
        accessibility: Box<SExp>,
    },
    RunCase {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        step: Box<SExp>,
        initial: Box<SExp>,
        transition: Box<SExp>,
        accessibility: Box<SExp>,
        transition_equality: Box<SExp>,
    },
    RunStepRec {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        motive: Box<SExp>,
        on_continue: Box<SExp>,
        on_finish: Box<SExp>,
        scrutinee: Box<SExp>,
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
    // Shared, unclassified record construction; classification belongs to elaboration.
    RecordTypeCtor {
        access: LocalAccess,
        parameters: Vec<SExp>,
        fields: Vec<(Identifier, SExp)>,
    },

    // --- set theory
    // \Pow power
    PowerSet {
        set: Box<SExp>,
    },
    // \SubSet (var, set, predicate)
    SubSet {
        var: Identifier,
        set: Box<SExp>,
        predicate: Box<SExp>,
    },
    // \In[superset] subset elem
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
    Program(Block),
}

impl TryFrom<SExp> for ValueTypeExp {
    type Error = String;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        let source = value.source;
        let result = match value.kind {
            SExpKind::Meta { kind, token } => Ok(ValueTypeExpKind::Meta { kind, token }),
            SExpKind::AccessPath { access, parameters } => Ok(ValueTypeExpKind::Access {
                access,
                parameters: parameters
                    .into_iter()
                    .map(TryInto::try_into)
                    .collect::<Result<_, _>>()?,
            }),
            SExpKind::ThunkType { computation_ty } => Ok(ValueTypeExpKind::Thunk(Box::new(
                (*computation_ty).try_into()?,
            ))),
            SExpKind::Prod {
                bind: Bind::Named(RightBind { vars, ty }),
                body,
            } if vars.is_empty() => Ok(ValueTypeExpKind::Thunk(Box::new(
                cbv_arrow_as_computation_type(*ty, *body)?,
            ))),
            SExpKind::RunStep {
                state_ty,
                result_ty,
            } => Ok(ValueTypeExpKind::RunStep {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
            }),
            _ => Err("expected Program value-type syntax".into()),
        };
        result.map(|kind| Self { kind, source })
    }
}

impl TryFrom<SExp> for ComputationTypeExp {
    type Error = String;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        let source = value.source;
        let result = match value.kind {
            SExpKind::Meta { kind, token } => Ok(ComputationTypeExpKind::Meta { kind, token }),
            SExpKind::ReturnType { value_ty } => Ok(ComputationTypeExpKind::Return(Box::new(
                (*value_ty).try_into()?,
            ))),
            SExpKind::ComputationFunction { domain, codomain } => {
                Ok(ComputationTypeExpKind::Function {
                    domain: Box::new((*domain).try_into()?),
                    codomain: Box::new((*codomain).try_into()?),
                })
            }
            SExpKind::Prod {
                bind: Bind::Named(RightBind { vars, ty }),
                body,
            } if vars.is_empty() => cbv_arrow_as_computation_type(*ty, *body).map(|exp| exp.kind),
            _ => Err("expected Program computation-type syntax".into()),
        };
        result.map(|kind| Self { kind, source })
    }
}

impl TryFrom<SExp> for ValueTermExp {
    type Error = String;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        let source = value.source;
        let (value, arguments) = decompose_surface_application(value);
        let result = match value {
            SExp {
                kind:
                    SExpKind::RecordTypeCtor {
                        access,
                        parameters,
                        fields,
                    },
                ..
            } if arguments.is_empty() => Ok(ValueTermExpKind::Record {
                datatype: access,
                parameters: parameters
                    .into_iter()
                    .map(TryInto::try_into)
                    .collect::<Result<_, _>>()?,
                fields: fields
                    .into_iter()
                    .map(|(name, value)| Ok((name, value.try_into()?)))
                    .collect::<Result<_, String>>()?,
            }),
            SExp {
                kind: SExpKind::Meta { kind, token },
                ..
            } if arguments.is_empty() => Ok(ValueTermExpKind::Meta { kind, token }),
            SExp {
                kind: SExpKind::AccessPath { access, parameters },
                ..
            } if parameters.is_empty() => {
                if arguments.is_empty() {
                    Ok(ValueTermExpKind::Access(access))
                } else {
                    Err(
                        "Program values are not applied; only constructors take field arguments"
                            .into(),
                    )
                }
            }
            SExp {
                kind: SExpKind::AssociatedAccess { base, field },
                ..
            } => {
                let SExp {
                    kind: SExpKind::AccessPath { access, parameters },
                    ..
                } = *base
                else {
                    return Err("expected a Program datatype before constructor access".into());
                };
                Ok(ValueTermExpKind::Constructor {
                    datatype: access,
                    constructor: field,
                    parameters: parameters
                        .into_iter()
                        .map(TryInto::try_into)
                        .collect::<Result<_, _>>()?,
                    fields: arguments
                        .into_iter()
                        .map(TryInto::try_into)
                        .collect::<Result<_, _>>()?,
                })
            }
            SExp {
                kind: SExpKind::Thunk { computation },
                ..
            } if arguments.is_empty() => Ok(ValueTermExpKind::Thunk(Box::new(
                (*computation).try_into()?,
            ))),
            expression @ SExp {
                kind: SExpKind::Lam { .. },
                ..
            } if arguments.is_empty() => Ok(ValueTermExpKind::Thunk(Box::new(
                cbv_lambda_as_computation(expression)?,
            ))),
            SExp {
                kind:
                    SExpKind::Continue {
                        state_ty,
                        result_ty,
                        next,
                    },
                ..
            } if arguments.is_empty() => Ok(ValueTermExpKind::Continue {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                next: Box::new((*next).try_into()?),
            }),
            SExp {
                kind:
                    SExpKind::Finish {
                        state_ty,
                        result_ty,
                        output,
                    },
                ..
            } if arguments.is_empty() => Ok(ValueTermExpKind::Finish {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                output: Box::new((*output).try_into()?),
            }),
            _ => Err("expected Program value syntax".into()),
        };
        result.map(|kind| Self { kind, source })
    }
}

impl TryFrom<SExp> for ComputationTermExp {
    type Error = String;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        let source = value.source;
        let result = match value {
            SExp {
                kind: SExpKind::InferredProjection { value, field },
                ..
            } => Ok(ComputationTermExpKind::InferredProjection {
                value: Box::new((*value).try_into()?),
                field,
            }),
            SExp {
                kind: SExpKind::AssociatedAccess { base, field },
                ..
            } => {
                let SExp {
                    kind: SExpKind::AccessPath { access, parameters },
                    ..
                } = *base
                else {
                    return Err("expected a Program datatype before associated access".into());
                };
                Ok(ComputationTermExpKind::Associated {
                    datatype: access,
                    item: field,
                    parameters: parameters
                        .into_iter()
                        .map(TryInto::try_into)
                        .collect::<Result<_, _>>()?,
                })
            }
            SExp {
                kind: SExpKind::Meta { kind, token },
                ..
            } => Ok(ComputationTermExpKind::Meta { kind, token }),
            SExp {
                kind: SExpKind::AccessPath { access, parameters },
                ..
            } if parameters.is_empty() => Ok(ComputationTermExpKind::Access(access)),
            SExp {
                kind: SExpKind::Return { value },
                ..
            } => Ok(ComputationTermExpKind::Return(Box::new(
                (*value).try_into()?,
            ))),
            SExp {
                kind: SExpKind::Force { value },
                ..
            } => Ok(ComputationTermExpKind::Force(Box::new(
                (*value).try_into()?,
            ))),
            SExp {
                kind:
                    SExpKind::ComputationLam {
                        var,
                        value_ty,
                        body,
                    },
                ..
            } => Ok(ComputationTermExpKind::Lambda {
                var,
                value_ty: Box::new((*value_ty).try_into()?),
                body: Box::new((*body).try_into()?),
            }),
            expression @ SExp {
                kind: SExpKind::App { .. },
                ..
            } => {
                let (head, arguments) = decompose_surface_application(expression);
                let head_source = head.source;
                let mut function: ProgramFunctionExp = match head {
                    SExp {
                        kind: SExpKind::AccessPath { access, parameters },
                        ..
                    } if parameters.is_empty() => ProgramFunctionExpKind::Access(access).into(),
                    SExp {
                        kind: SExpKind::AssociatedAccess { base, field },
                        ..
                    } => {
                        let SExp {
                            kind: SExpKind::AccessPath { access, parameters },
                            ..
                        } = *base
                        else {
                            return Err(
                                "expected a Program datatype before associated access".into()
                            );
                        };
                        ProgramFunctionExpKind::Associated {
                            datatype: access,
                            item: field,
                            parameters: parameters
                                .into_iter()
                                .map(TryInto::try_into)
                                .collect::<Result<_, _>>()?,
                        }
                        .into()
                    }
                    expression @ SExp {
                        kind: SExpKind::Thunk { .. },
                        ..
                    } => ProgramFunctionExpKind::Value(Box::new(expression.try_into()?)).into(),
                    expression => {
                        ProgramFunctionExpKind::Computation(Box::new(expression.try_into()?)).into()
                    }
                };
                function.source = head_source;
                Ok(ComputationTermExpKind::Application {
                    function,
                    arguments: arguments
                        .into_iter()
                        .map(TryInto::try_into)
                        .collect::<Result<_, _>>()?,
                })
            }
            expression @ SExp {
                kind: SExpKind::Lam { .. },
                ..
            } => cbv_lambda_as_computation(expression).map(|exp| exp.kind),
            SExp {
                kind:
                    SExpKind::Sequence {
                        computation,
                        var,
                        value_ty,
                        body,
                    },
                ..
            } => Ok(ComputationTermExpKind::Sequence {
                computation: Box::new((*computation).try_into()?),
                var,
                value_ty: Box::new((*value_ty).try_into()?),
                body: Box::new((*body).try_into()?),
            }),
            SExp {
                kind:
                    SExpKind::ValueLet {
                        var,
                        value_ty,
                        value,
                        body,
                    },
                ..
            } => Ok(ComputationTermExpKind::ValueLet {
                var,
                value_ty: Box::new((*value_ty).try_into()?),
                value: Box::new((*value).try_into()?),
                body: Box::new((*body).try_into()?),
            }),
            SExp {
                kind: SExpKind::Program(Block { statements, result }),
                ..
            } => {
                let mut body = ComputationTermExpKind::Return(Box::new((*result).try_into()?));
                for statement in statements.into_iter().rev() {
                    body = match statement {
                        Statement::Let {
                            var,
                            ty,
                            body: value,
                        } => ComputationTermExpKind::ValueLet {
                            var,
                            value_ty: Box::new(ty.try_into()?),
                            value: Box::new(value.try_into()?),
                            body: Box::new(body.into()),
                        },
                        Statement::Bind {
                            var,
                            ty,
                            computation,
                        } => ComputationTermExpKind::Sequence {
                            computation: Box::new(computation.try_into()?),
                            var,
                            value_ty: Box::new(ty.try_into()?),
                            body: Box::new(body.into()),
                        },
                        _ => {
                            return Err(
                                "Program blocks only support \\let and \\bind statements".into()
                            );
                        }
                    };
                }
                Ok(body)
            }
            SExp {
                kind:
                    SExpKind::ProgramCase {
                        path,
                        scrutinee,
                        branches,
                    },
                ..
            } => Ok(ComputationTermExpKind::Case {
                datatype: path,
                scrutinee: Box::new((*scrutinee).try_into()?),
                branches: branches
                    .into_iter()
                    .map(|(constructor, binders, body)| {
                        Ok((constructor, binders, body.try_into()?))
                    })
                    .collect::<Result<_, String>>()?,
            }),
            SExp {
                kind:
                    SExpKind::Run {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                        accessibility,
                    },
                ..
            } => Ok(ComputationTermExpKind::Run {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                step: Box::new((*step).try_into()?),
                initial: Box::new((*initial).try_into()?),
                accessibility,
            }),
            SExp {
                kind:
                    SExpKind::RunCase {
                        state_ty,
                        result_ty,
                        step,
                        initial,
                        transition,
                        accessibility,
                        transition_equality,
                    },
                ..
            } => Ok(ComputationTermExpKind::RunCase {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                step: Box::new((*step).try_into()?),
                initial: Box::new((*initial).try_into()?),
                transition: Box::new((*transition).try_into()?),
                accessibility,
                transition_equality,
            }),
            _ => Err("expected Program computation syntax".into()),
        };
        result.map(|kind| Self { kind, source })
    }
}

fn cbv_arrow_as_computation_type(
    domain: SExp,
    codomain: SExp,
) -> Result<ComputationTypeExp, String> {
    Ok(ComputationTypeExpKind::Function {
        domain: Box::new(domain.try_into()?),
        codomain: Box::new(ComputationTypeExpKind::Return(Box::new(codomain.try_into()?)).into()),
    }
    .into())
}

fn cbv_lambda_as_computation(expression: SExp) -> Result<ComputationTermExp, String> {
    let mut expression = expression;
    let mut binders = Vec::new();
    while let SExp {
        kind: SExpKind::Lam { bind, body },
        ..
    } = expression
    {
        let Bind::Named(RightBind { vars, ty }) = bind else {
            return Err("Program lambda requires a plain value binder".into());
        };
        if vars.is_empty() {
            return Err("Program lambda requires at least one value binder".into());
        }
        binders.extend(vars.into_iter().map(|var| (var, (*ty).clone())));
        expression = *body;
    }
    let mut body: ComputationTermExp = expression.try_into()?;
    let (var, ty) = binders
        .pop()
        .ok_or_else(|| "Program lambda requires at least one value binder".to_string())?;
    body = ComputationTermExpKind::Lambda {
        var,
        value_ty: Box::new(ty.try_into()?),
        body: Box::new(body),
    }
    .into();
    for (var, ty) in binders.into_iter().rev() {
        body = ComputationTermExpKind::Lambda {
            var,
            value_ty: Box::new(ty.try_into()?),
            body: Box::new(
                ComputationTermExpKind::Return(Box::new(
                    ValueTermExpKind::Thunk(Box::new(body)).into(),
                ))
                .into(),
            ),
        }
        .into();
    }
    Ok(body)
}

fn decompose_surface_application(mut expression: SExp) -> (SExp, Vec<SExp>) {
    let mut arguments = Vec::new();
    while let SExp {
        kind: SExpKind::App { func, arg, .. },
        ..
    } = expression
    {
        arguments.push(*arg);
        expression = *func;
    }
    arguments.reverse();
    (expression, arguments)
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
    Bind {
        var: Identifier,
        ty: SExp,
        computation: SExp,
    }, // bind x: A <- computation;
    Sufficient {
        map: SExp,
        map_ty: SExp,
    }, // enough A by t;
    TakeFrom {
        var: Identifier,
        ty: SExp,
        existence: SExp,
    }, // takefrom x: A by existence;
}
