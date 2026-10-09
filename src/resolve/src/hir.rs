//! Names resolved to bindings, before type inference.
use syntax::sort::Sort;
pub use syntax::syntax::{
    MacroToken, SourceFile, SourceId, SourceLocation, SourceSpan, SurfaceMeta,
};

#[derive(
    serde::Serialize, serde::Deserialize, Debug, Clone, Copy, Default, PartialEq, Eq, Hash,
)]
pub struct ModuleId(pub u32);
#[derive(
    serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash,
)]
pub struct BindingId(pub u64);

/// Spelling for diagnostics and the resolved binding, where the name denotes one.
/// Field labels and other type-directed members retain their spelling.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub String, pub Option<BindingId>);
pub type Identifier = Name;
#[allow(non_snake_case)]
pub fn Identifier(text: String) -> Name {
    Name(text, None)
}
impl Name {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

// module definition
#[derive(Debug, Clone)]
pub struct Module {
    pub id: ModuleId,
    pub name: Identifier,
    pub parameters: Vec<RightBind>, // given parameters for module
    pub parameter_checks: Vec<(SExp, SExp)>,
    /// Source declarations represented by parameters in a generated module.
    pub parameter_sources: std::collections::HashMap<String, ParameterSource>,
    pub body: ModuleBody,
    pub span: SourceSpan,
    pub declaration_spans: Vec<SourceSpan>,
    pub source: Option<std::sync::Arc<SourceFile>>,
    pub header_source: Option<std::sync::Arc<SourceFile>>,
}

#[derive(Debug, Clone)]
pub struct ParameterSource {
    pub subject: ParameterSubject,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub enum ModuleBody {
    Inline(Vec<ModuleItem>), // sensitive to order
    External,
}

#[derive(Debug, Clone)]
pub enum MacroSeqAtom {
    Capture(Identifier),
    TokenCapture(Identifier),
    Rest(Identifier),
    Tok(MacroToken),
    Quoted(String),
    Seq(Vec<MacroSeqAtom>),
}

#[derive(Debug, Clone)]
pub enum TokenMatchPattern {
    Token(MacroSeqAtom),
    Sequence(Vec<MacroSeqAtom>),
    Default,
}

#[derive(Debug, Clone)]
pub enum ModuleItem {
    Scoped {
        exports: Vec<Identifier>,
        items: Vec<ModuleItem>,
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
    Structure {
        name: Identifier,
        kind: Option<InductiveKind>,
        parameters: Vec<RightBind>,
        fields: Vec<(Identifier, SExp, Option<SExp>)>,
        field_spans: Vec<SourceSpan>,
    },
    Record {
        type_name: Identifier,
        parameters: Vec<RightBind>,
        kind: InductiveKind,
        fields: Vec<(Identifier, SExp)>,
    },
    SetStructure {
        name: Identifier,
        parameters: Vec<RightBind>,
        sort: syntax::sort::Sort,
        fields: Vec<(Identifier, SExp)>,
    },
    ChildModule {
        module: Box<Module>,
    },
    Import {
        path: ModuleInstantiatePath,
        import_name: Identifier,
        checks: Vec<(SExp, SExp)>,
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
    MemberCheck {
        value: SExp,
        ty: SExp,
    },
    ValueTypeCheck {
        ty: ValueTypeExp,
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

pub type ModuleCall = (Identifier, Vec<(Identifier, SExp)>);

#[derive(Debug, Clone)]
pub enum ModuleInstantiatePath {
    FromModule {
        module: ModuleId,
        calls: Vec<ModuleCall>,
    },
    FromCurrent {
        back_parent: usize,
        calls: Vec<ModuleCall>,
    },
    FromRoot {
        calls: Vec<ModuleCall>,
    },
    FromImport {
        import_name: Identifier,
        calls: Vec<ModuleCall>,
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

/// Program expression views mirror the kernel's four syntactic categories.
/// Shared queries retain `SExp` until elaboration selects a judgement.
#[derive(Debug, Clone)]
pub enum ValueTypeExp {
    Deferred {
        expression: Box<SExp>,
    },
    Checked {
        checks: Vec<(SExp, SExp)>,
        body: Box<ValueTypeExp>,
    },
    Meta {
        kind: SurfaceMeta,
        span: SourceSpan,
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

#[derive(Debug, Clone)]
pub enum ComputationTypeExp {
    Deferred {
        expression: Box<SExp>,
    },
    Checked {
        checks: Vec<(SExp, SExp)>,
        body: Box<ComputationTypeExp>,
    },
    Meta {
        kind: SurfaceMeta,
        span: SourceSpan,
    },
    Return(Box<ValueTypeExp>),
    Function {
        domain: Box<ValueTypeExp>,
        codomain: Box<ComputationTypeExp>,
    },
}

#[derive(Debug, Clone)]
pub enum ValueTermExp {
    Reference {
        access: LocalAccess,
    },
    Deferred {
        expression: Box<SExp>,
    },
    Checked {
        checks: Vec<(SExp, SExp)>,
        body: Box<ValueTermExp>,
    },
    Ascribe {
        term: Box<ValueTermExp>,
        ty: Box<ValueTypeExp>,
    },
    Meta {
        kind: SurfaceMeta,
        span: SourceSpan,
    },
    Access(LocalAccess),
    Record {
        datatype: LocalAccess,
        parameters: Vec<ValueTypeExp>,
        fields: Vec<(Identifier, ValueTermExp)>,
    },
    Constructor {
        span: SourceSpan,
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

#[derive(Debug, Clone)]
pub enum ComputationTermExp {
    Deferred {
        expression: Box<SExp>,
    },
    Checked {
        checks: Vec<(SExp, SExp)>,
        body: Box<ComputationTermExp>,
    },
    Ascribe {
        term: Box<ComputationTermExp>,
        ty: Box<ComputationTypeExp>,
    },
    Meta {
        kind: SurfaceMeta,
        span: SourceSpan,
    },
    Access(LocalAccess),
    Associated {
        span: SourceSpan,
        datatype: LocalAccess,
        item: Identifier,
        parameters: Vec<ValueTypeExp>,
    },
    InferredProjection {
        value: Box<ValueTermExp>,
        field: Identifier,
        span: SourceSpan,
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
    StepMatch {
        state_ty: Box<ValueTypeExp>,
        result_ty: Box<ValueTypeExp>,
        computation_ty: Box<ComputationTypeExp>,
        on_continue: Box<ComputationTermExp>,
        on_finish: Box<ComputationTermExp>,
        scrutinee: Box<ValueTermExp>,
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
/// left unclassified until elaboration can inspect the type of the resolved
/// local value or global value/computation definition.
#[derive(Debug, Clone)]
pub enum ProgramFunctionExp {
    Access(LocalAccess),
    Associated {
        span: SourceSpan,
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
    Instantiated {
        span: SourceSpan,
        path: Box<ModuleInstantiatePath>,
        child: Identifier,
    },
    // accessing inductive type or defined constant
    Current {
        span: SourceSpan,
        access: Identifier,
    },
    Named {
        span: SourceSpan,
        access: Identifier,
        child: Identifier,
    },
    /// An access resolved in a macro's definition environment.
    Resolved {
        span: SourceSpan,
        module: ModuleId,
        access: Identifier,
        display: String,
    },
}

impl std::fmt::Display for LocalAccess {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Instantiated { child, .. } => write!(formatter, "<module>.{}", child.as_str()),
            Self::Resolved { display, .. } => formatter.write_str(display),
            Self::Current { access, .. } => formatter.write_str(access.as_str()),
            Self::Named { access, child, .. } => {
                write!(formatter, "{}.{}", access.as_str(), child.as_str())
            }
        }
    }
}

// this is internal representation
#[derive(Debug, Clone)]
pub enum SExp {
    ModuleInstance {
        path: Box<ModuleInstantiatePath>,
        import_name: Identifier,
    },
    ConversionTarget {
        expression: Box<SExp>,
    },
    ProgramValueReference {
        access: LocalAccess,
    },
    MemberAccess {
        base: Box<SExp>,
        field: Identifier,
        parameters: Vec<SExp>,
        span: SourceSpan,
    },
    MemberLiteral {
        ty: Box<SExp>,
        fields: Vec<(Identifier, SExp)>,
    },

    Checked {
        checks: Vec<(SExp, SExp)>,
        body: Box<SExp>,
    },
    Ascribe {
        term: Box<SExp>,
        ty: Box<SExp>,
    },
    ReflectTerm {
        expression: Box<SExp>,
    },
    /// Reflection of a substituted Program module argument.
    Reflect {
        parameter: BindingId,
        expression: Box<SExp>,
    },
    Assign {
        value: Box<SExp>,
        number: u32,
        span: SourceSpan,
    },
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
        span: SourceSpan,
        base: Box<SExp>,
        field: Identifier,
    },
    InferredProjection {
        value: Box<SExp>,
        field: Identifier,
        span: SourceSpan,
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
        /// Template calls can see declarations up to and including their own
        /// definition, allowing self recursion without forward references.
        max_order: Option<u64>,
        depth: u16,
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
        span: Option<SourceSpan>,
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
        branches: Vec<(Identifier, Vec<Identifier>, SExp)>,
    },
    Induction {
        binders: Vec<RightBind>,
        return_type: Box<SExp>,
        cases: Vec<(Identifier, SExp)>,
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
    ProgramStepMatch {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        computation_ty: Box<SExp>,
        on_continue: Box<SExp>,
        on_finish: Box<SExp>,
        scrutinee: Box<SExp>,
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
    SetStepMatch {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        motive: Box<SExp>,
        on_continue: Box<SExp>,
        on_finish: Box<SExp>,
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
    // Unique choice from a set.
    Choice {
        set: Box<SExp>,
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
    ChoiceEq {
        set: Box<SExp>,
        element: Box<SExp>,
        existence: Box<SExp>,
        uniqueness: Box<SExp>,
    },
    // --- block of statements
    Block(Block),
    Program(Block),
}

impl TryFrom<SExp> for ValueTypeExp {
    type Error = syntax::error::ConversionError;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        match value {
            SExp::Checked { checks, body } => Ok(Self::Checked {
                checks,
                body: Box::new((*body).try_into()?),
            }),
            SExp::Meta { kind, span } => Ok(Self::Meta { kind, span }),
            SExp::AccessPath { access, parameters } => Ok(Self::Access {
                access,
                parameters: parameters
                    .into_iter()
                    .map(TryInto::try_into)
                    .collect::<Result<_, _>>()?,
            }),
            SExp::ThunkType { computation_ty } => {
                Ok(Self::Thunk(Box::new((*computation_ty).try_into()?)))
            }
            SExp::Prod {
                bind: Bind::Named(RightBind { vars, ty }),
                body,
            } if vars.is_empty() => Ok(Self::Thunk(Box::new(cbv_arrow_as_computation_type(
                *ty, *body,
            )?))),
            SExp::RunStep {
                state_ty,
                result_ty,
            } => Ok(Self::RunStep {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
            }),
            _ => Err(syntax::error::ConversionError::ExpectedProgramValueTypeSyntax),
        }
    }
}

impl TryFrom<SExp> for ComputationTypeExp {
    type Error = syntax::error::ConversionError;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        match value {
            SExp::Checked { checks, body } => Ok(Self::Checked {
                checks,
                body: Box::new((*body).try_into()?),
            }),
            SExp::Meta { kind, span } => Ok(Self::Meta { kind, span }),
            SExp::ReturnType { value_ty } => Ok(Self::Return(Box::new((*value_ty).try_into()?))),
            SExp::ComputationFunction { domain, codomain } => Ok(Self::Function {
                domain: Box::new((*domain).try_into()?),
                codomain: Box::new((*codomain).try_into()?),
            }),
            SExp::Prod {
                bind: Bind::Named(RightBind { vars, ty }),
                body,
            } if vars.is_empty() => cbv_arrow_as_computation_type(*ty, *body),
            _ => Err(syntax::error::ConversionError::ExpectedProgramComputationTypeSyntax),
        }
    }
}

impl TryFrom<SExp> for ValueTermExp {
    type Error = syntax::error::ConversionError;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        let (value, arguments) = decompose_surface_application(value);
        match value {
            SExp::ProgramValueReference { access } if arguments.is_empty() => {
                Ok(Self::Reference { access })
            }
            SExp::Checked { checks, body } => Ok(Self::Checked {
                checks,
                body: Box::new((*body).try_into()?),
            }),
            SExp::Ascribe { term, ty } if arguments.is_empty() => Ok(Self::Ascribe {
                term: Box::new((*term).try_into()?),
                ty: Box::new((*ty).try_into()?),
            }),
            SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } if arguments.is_empty() => Ok(Self::Record {
                datatype: access,
                parameters: parameters
                    .into_iter()
                    .map(TryInto::try_into)
                    .collect::<Result<_, _>>()?,
                fields: fields
                    .into_iter()
                    .map(|(name, value)| Ok((name, value.try_into()?)))
                    .collect::<Result<_, syntax::error::ConversionError>>()?,
            }),
            SExp::Meta { kind, span } if arguments.is_empty() => Ok(Self::Meta { kind, span }),
            SExp::AccessPath { access, parameters } if parameters.is_empty() => {
                if arguments.is_empty() {
                    Ok(Self::Access(access))
                } else {
                    Err(syntax::error::ConversionError::ProgramValuesAreNotAppliedOnlyConstructorsTakeFieldArguments)
                }
            }
            SExp::AssociatedAccess { base, field, span } => {
                let SExp::AccessPath { access, parameters } = *base else {
                    return Err(syntax::error::ConversionError::ExpectedAProgramDatatypeBeforeConstructorAccess);
                };
                Ok(Self::Constructor {
                    span,
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
            SExp::Thunk { computation } if arguments.is_empty() => {
                Ok(Self::Thunk(Box::new((*computation).try_into()?)))
            }
            expression @ SExp::Lam { .. } if arguments.is_empty() => Ok(Self::Thunk(Box::new(
                cbv_lambda_as_computation(expression)?,
            ))),
            SExp::Continue {
                state_ty,
                result_ty,
                next,
            } if arguments.is_empty() => Ok(Self::Continue {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                next: Box::new((*next).try_into()?),
            }),
            SExp::Finish {
                state_ty,
                result_ty,
                output,
            } if arguments.is_empty() => Ok(Self::Finish {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                output: Box::new((*output).try_into()?),
            }),
            _ => Err(syntax::error::ConversionError::ExpectedProgramValueSyntax),
        }
    }
}

impl TryFrom<SExp> for ComputationTermExp {
    type Error = syntax::error::ConversionError;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        match value {
            SExp::Checked { checks, body } => {
                let body = match Self::try_from((*body).clone()) {
                    Ok(body) => body,
                    Err(_) => Self::Force(Box::new((*body).try_into()?)),
                };
                Ok(Self::Checked {
                    checks,
                    body: Box::new(body),
                })
            }
            SExp::Ascribe { term, ty } => Ok(Self::Ascribe {
                term: Box::new((*term).try_into()?),
                ty: Box::new((*ty).try_into()?),
            }),
            SExp::InferredProjection { value, field, span } => Ok(Self::InferredProjection {
                value: Box::new((*value).try_into()?),
                field,
                span,
            }),
            SExp::AssociatedAccess { base, field, span } => {
                let SExp::AccessPath { access, parameters } = *base else {
                    return Err(syntax::error::ConversionError::ExpectedAProgramDatatypeBeforeAssociatedAccess);
                };
                Ok(Self::Associated {
                    span,
                    datatype: access,
                    item: field,
                    parameters: parameters
                        .into_iter()
                        .map(TryInto::try_into)
                        .collect::<Result<_, _>>()?,
                })
            }
            SExp::Meta { kind, span } => Ok(Self::Meta { kind, span }),
            SExp::AccessPath { access, parameters } if parameters.is_empty() => {
                Ok(Self::Access(access))
            }
            SExp::Return { value } => Ok(Self::Return(Box::new((*value).try_into()?))),
            SExp::Force { value } => Ok(Self::Force(Box::new((*value).try_into()?))),
            SExp::ComputationLam {
                var,
                value_ty,
                body,
            } => Ok(Self::Lambda {
                var,
                value_ty: Box::new((*value_ty).try_into()?),
                body: Box::new((*body).try_into()?),
            }),
            expression @ SExp::App { .. } => {
                let (head, arguments) = decompose_surface_application(expression);
                let function = match head {
                    SExp::AccessPath { access, parameters } if parameters.is_empty() => {
                        ProgramFunctionExp::Access(access)
                    }
                    SExp::AssociatedAccess { base, field, span } => {
                        let SExp::AccessPath { access, parameters } = *base else {
                            return Err(syntax::error::ConversionError::ExpectedAProgramDatatypeBeforeAssociatedAccess);
                        };
                        ProgramFunctionExp::Associated {
                            span,
                            datatype: access,
                            item: field,
                            parameters: parameters
                                .into_iter()
                                .map(TryInto::try_into)
                                .collect::<Result<_, _>>()?,
                        }
                    }
                    expression @ (SExp::Thunk { .. } | SExp::Checked { .. }) => {
                        match ValueTermExp::try_from(expression.clone()) {
                            Ok(value) => ProgramFunctionExp::Value(Box::new(value)),
                            Err(_) => {
                                ProgramFunctionExp::Computation(Box::new(expression.try_into()?))
                            }
                        }
                    }
                    expression => ProgramFunctionExp::Computation(Box::new(expression.try_into()?)),
                };
                Ok(Self::Application {
                    function,
                    arguments: arguments
                        .into_iter()
                        .map(TryInto::try_into)
                        .collect::<Result<_, _>>()?,
                })
            }
            expression @ SExp::Lam { .. } => cbv_lambda_as_computation(expression),
            SExp::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => Ok(Self::Sequence {
                computation: Box::new((*computation).try_into()?),
                var,
                value_ty: Box::new((*value_ty).try_into()?),
                body: Box::new((*body).try_into()?),
            }),
            SExp::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => Ok(Self::ValueLet {
                var,
                value_ty: Box::new((*value_ty).try_into()?),
                value: Box::new((*value).try_into()?),
                body: Box::new((*body).try_into()?),
            }),
            SExp::Program(Block { statements, result }) => {
                let mut body = Self::Return(Box::new((*result).try_into()?));
                for statement in statements.into_iter().rev() {
                    body = match statement {
                        Statement::Let {
                            var,
                            ty,
                            body: value,
                            ..
                        } => Self::ValueLet {
                            var,
                            value_ty: Box::new(ty.try_into()?),
                            value: Box::new(value.try_into()?),
                            body: Box::new(body),
                        },
                        Statement::Bind {
                            var,
                            ty,
                            computation,
                        } => Self::Sequence {
                            computation: Box::new(computation.try_into()?),
                            var,
                            value_ty: Box::new(ty.try_into()?),
                            body: Box::new(body),
                        },
                        _ => {
                            return Err(syntax::error::ConversionError::ProgramBlocksOnlySupportLetAndBindStatements);
                        }
                    };
                }
                Ok(body)
            }
            SExp::ProgramCase {
                path,
                scrutinee,
                branches,
            } => Ok(Self::Case {
                datatype: path,
                scrutinee: Box::new((*scrutinee).try_into()?),
                branches: branches
                    .into_iter()
                    .map(|(constructor, binders, body)| {
                        Ok((constructor, binders, body.try_into()?))
                    })
                    .collect::<Result<_, syntax::error::ConversionError>>()?,
            }),
            SExp::ProgramStepMatch {
                state_ty,
                result_ty,
                computation_ty,
                on_continue,
                on_finish,
                scrutinee,
            } => Ok(Self::StepMatch {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                computation_ty: Box::new((*computation_ty).try_into()?),
                on_continue: Box::new((*on_continue).try_into()?),
                on_finish: Box::new((*on_finish).try_into()?),
                scrutinee: Box::new((*scrutinee).try_into()?),
            }),
            SExp::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => Ok(Self::Run {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                step: Box::new((*step).try_into()?),
                initial: Box::new((*initial).try_into()?),
                accessibility,
            }),
            SExp::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => Ok(Self::RunCase {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                step: Box::new((*step).try_into()?),
                initial: Box::new((*initial).try_into()?),
                transition: Box::new((*transition).try_into()?),
                accessibility,
                transition_equality,
            }),
            _ => Err(syntax::error::ConversionError::ExpectedProgramComputationSyntax),
        }
    }
}

fn cbv_arrow_as_computation_type(
    domain: SExp,
    codomain: SExp,
) -> Result<ComputationTypeExp, syntax::error::ConversionError> {
    Ok(ComputationTypeExp::Function {
        domain: Box::new(domain.try_into()?),
        codomain: Box::new(ComputationTypeExp::Return(Box::new(codomain.try_into()?))),
    })
}

fn cbv_lambda_as_computation(
    expression: SExp,
) -> Result<ComputationTermExp, syntax::error::ConversionError> {
    let mut expression = expression;
    let mut binders = Vec::new();
    while let SExp::Lam { bind, body } = expression {
        let Bind::Named(RightBind { vars, ty }) = bind else {
            return Err(syntax::error::ConversionError::ProgramLambdaRequiresAPlainValueBinder);
        };
        if vars.is_empty() {
            return Err(syntax::error::ConversionError::ProgramLambdaRequiresAtLeastOneValueBinder);
        }
        binders.extend(vars.into_iter().map(|var| (var, (*ty).clone())));
        expression = *body;
    }
    let mut body: ComputationTermExp = expression.try_into()?;
    let (var, ty) = binders
        .pop()
        .ok_or(syntax::error::ConversionError::ProgramLambdaRequiresAtLeastOneValueBinder)?;
    body = ComputationTermExp::Lambda {
        var,
        value_ty: Box::new(ty.try_into()?),
        body: Box::new(body),
    };
    for (var, ty) in binders.into_iter().rev() {
        body = ComputationTermExp::Lambda {
            var,
            value_ty: Box::new(ty.try_into()?),
            body: Box::new(ComputationTermExp::Return(Box::new(ValueTermExp::Thunk(
                Box::new(body),
            )))),
        };
    }
    Ok(body)
}

fn decompose_surface_application(mut expression: SExp) -> (SExp, Vec<SExp>) {
    let mut arguments = Vec::new();
    while let SExp::App { func, arg, .. } = expression {
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

impl Block {
    pub fn as_term(&self) -> Result<SExp, syntax::error::ConversionError> {
        let Block {
            statements: declarations,
            result: term,
        } = self;
        let mut term = term.as_ref().clone();
        for decl in declarations.iter().rev() {
            match decl {
                Statement::Fun(items) => {
                    for bind in items.iter().rev() {
                        term = SExp::Lam {
                            bind: Bind::Named(bind.clone()),
                            body: Box::new(term),
                        };
                    }
                }
                Statement::Let {
                    span,
                    var,
                    ty,
                    body,
                } => {
                    term = SExp::Where {
                        exp: Box::new(term),
                        clauses: vec![(var.clone(), ty.clone(), body.clone())],
                        span: Some(*span),
                    };
                }
                Statement::Bind { .. } => {
                    return Err(syntax::error::ConversionError::BindStatementsAreOnlyAvailableInProgramBlocks);
                }
                Statement::TakeFrom { var, ty, existence } => {
                    term = SExp::TakeProp {
                        bind: Bind::Named(RightBind {
                            vars: vec![var.clone()],
                            ty: Box::new(ty.clone()),
                        }),
                        body: Box::new(term),
                        existence: Box::new(existence.clone()),
                    };
                }
                Statement::Sufficient { map, map_ty } => {
                    let argument = Identifier("enoughArgument".into());
                    term = SExp::App {
                        func: Box::new(map.clone()),
                        arg: Box::new(SExp::Where {
                            exp: Box::new(SExp::AccessPath {
                                access: LocalAccess::Current {
                                    span: Default::default(),
                                    access: argument.clone(),
                                },
                                parameters: Vec::new(),
                            }),
                            clauses: vec![(argument, map_ty.clone(), term)],
                            span: None,
                        }),
                    };
                }
            }
        }
        Ok(term)
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Fun(Vec<RightBind>), // \fun (x: A) (y: B) \then
    Let {
        span: SourceSpan,
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

impl LocalAccess {
    pub fn span(&self) -> SourceSpan {
        match self {
            Self::Instantiated { span, .. }
            | Self::Current { span, .. }
            | Self::Named { span, .. }
            | Self::Resolved { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParameterSubject {
    ModuleParameter,
    StructureParameter { structure: String, name: String },
    StructureField { structure: String, name: String },
    DefinitionParameter { definition: String, name: String },
}
impl std::fmt::Display for ParameterSubject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ModuleParameter => f.write_str("Module parameter"),
            Self::StructureParameter { structure, name } => {
                write!(f, "Structure parameter '{structure}.{name}'")
            }
            Self::StructureField { structure, name } => {
                write!(f, "Structure field '{structure}.{name}'")
            }
            Self::DefinitionParameter { definition, name } => {
                write!(f, "Definition parameter '{definition}.{name}'")
            }
        }
    }
}

impl ParameterSubject {
    pub fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        use diagnostics::DiagnosticData as Data;
        match self {
            Self::ModuleParameter => Data::new("resolve.ModuleParameter"),
            Self::StructureParameter { structure, name } => Data::new("resolve.StructureParameter")
                .with("structure", structure.clone())
                .with("name", name.clone()),
            Self::StructureField { structure, name } => Data::new("resolve.StructureField")
                .with("structure", structure.clone())
                .with("name", name.clone()),
            Self::DefinitionParameter { definition, name } => {
                Data::new("resolve.DefinitionParameter")
                    .with("definition", definition.clone())
                    .with("name", name.clone())
            }
        }
    }
}
