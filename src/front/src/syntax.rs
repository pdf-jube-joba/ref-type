// this file describes the surface syntax tree
use crate::raw::exp::{Exp, ExpNode};
use crate::raw::ids::{DefId, InductiveId, ModuleId};
use crate::raw::sort::Sort;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceSpan {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SurfaceMeta {
    /// `_`: solve by constraints, but report ambiguity rather than a goal.
    Implicit,
    /// Bare `?`: a fresh proof-search goal at every occurrence.
    Goal,
    /// `?N`: occurrences with the same number share one metavariable within
    /// the current elaboration unit.
    Named(u32),
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
    Definition {
        owner: Option<AssociatedOwner>,
        name: Identifier,
        binders: Vec<RightBind>,
        ty: SExp,
        body: SExp,
    },
    ValueDefinition {
        owner: Option<AssociatedOwner>,
        name: Identifier,
        ty: ValueTypeExp,
        body: ValueTermExp,
    },
    ComputationDefinition {
        owner: Option<AssociatedOwner>,
        name: Identifier,
        ty: ComputationTypeExp,
        body: ComputationTermExp,
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
#[derive(Debug, Clone)]
pub enum ValueTypeExp {
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
    Meta {
        kind: SurfaceMeta,
        span: SourceSpan,
    },
    Access(LocalAccess),
    Associated {
        datatype: LocalAccess,
        item: Identifier,
        parameters: Vec<ValueTypeExp>,
    },
    Return(Box<ValueTermExp>),
    Force(Box<ValueTermExp>),
    Lambda {
        var: Identifier,
        value_ty: Box<ValueTypeExp>,
        body: Box<ComputationTermExp>,
    },
    Application {
        computation: Box<ComputationTermExp>,
        value: Box<ValueTermExp>,
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
        accessibility: Option<Box<SExp>>,
    },
    RunCase {
        state_ty: Box<ValueTypeExp>,
        result_ty: Box<ValueTypeExp>,
        step: Box<ValueTermExp>,
        initial: Box<ValueTermExp>,
        transition: Box<ComputationTermExp>,
        accessibility: Option<Box<SExp>>,
        transition_equality: Option<Box<SExp>>,
    },
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
    /// An access resolved in a macro's definition environment.
    Resolved {
        module: ModuleId,
        access: Identifier,
    },
}

// this is internal representation
#[derive(Debug, Clone)]
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
    PRunStep {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
    },
    Continue {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        next: Box<SExp>,
    },
    PContinue {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        next: Box<SExp>,
    },
    Finish {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        output: Box<SExp>,
    },
    PFinish {
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
    PRun {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        step: Box<SExp>,
        initial: Box<SExp>,
        accessibility: Option<Box<SExp>>,
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
    PRunCase {
        state_ty: Box<SExp>,
        result_ty: Box<SExp>,
        step: Box<SExp>,
        initial: Box<SExp>,
        transition: Box<SExp>,
        accessibility: Option<Box<SExp>>,
        transition_equality: Option<Box<SExp>>,
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

impl TryFrom<SExp> for ValueTypeExp {
    type Error = String;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        match value {
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
            SExp::PRunStep {
                state_ty,
                result_ty,
            } => Ok(Self::RunStep {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
            }),
            _ => Err("expected Program value-type syntax".into()),
        }
    }
}

impl TryFrom<SExp> for ComputationTypeExp {
    type Error = String;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        match value {
            SExp::Meta { kind, span } => Ok(Self::Meta { kind, span }),
            SExp::ReturnType { value_ty } => Ok(Self::Return(Box::new((*value_ty).try_into()?))),
            SExp::ComputationFunction { domain, codomain } => Ok(Self::Function {
                domain: Box::new((*domain).try_into()?),
                codomain: Box::new((*codomain).try_into()?),
            }),
            _ => Err("expected Program computation-type syntax".into()),
        }
    }
}

impl TryFrom<SExp> for ValueTermExp {
    type Error = String;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        let (value, arguments) = decompose_surface_application(value);
        match value {
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
                    .collect::<Result<_, String>>()?,
            }),
            SExp::Meta { kind, span } if arguments.is_empty() => Ok(Self::Meta { kind, span }),
            SExp::AccessPath { access, parameters } if parameters.is_empty() => {
                if arguments.is_empty() {
                    Ok(Self::Access(access))
                } else {
                    Err(
                        "Program values are not applied; only constructors take field arguments"
                            .into(),
                    )
                }
            }
            SExp::AssociatedAccess { base, field } => {
                let SExp::AccessPath { access, parameters } = *base else {
                    return Err("expected a Program datatype before constructor access".into());
                };
                Ok(Self::Constructor {
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
            SExp::PContinue {
                state_ty,
                result_ty,
                next,
            } if arguments.is_empty() => Ok(Self::Continue {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                next: Box::new((*next).try_into()?),
            }),
            SExp::PFinish {
                state_ty,
                result_ty,
                output,
            } if arguments.is_empty() => Ok(Self::Finish {
                state_ty: Box::new((*state_ty).try_into()?),
                result_ty: Box::new((*result_ty).try_into()?),
                output: Box::new((*output).try_into()?),
            }),
            _ => Err("expected Program value syntax".into()),
        }
    }
}

impl TryFrom<SExp> for ComputationTermExp {
    type Error = String;
    fn try_from(value: SExp) -> Result<Self, Self::Error> {
        match value {
            SExp::AssociatedAccess { base, field } => {
                let SExp::AccessPath { access, parameters } = *base else {
                    return Err("expected a Program datatype before associated access".into());
                };
                Ok(Self::Associated {
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
            SExp::App { func, arg, .. } => Ok(Self::Application {
                computation: Box::new((*func).try_into()?),
                value: Box::new((*arg).try_into()?),
            }),
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
            SExp::Block(Block { statements, result }) => {
                let mut body = Self::Return(Box::new((*result).try_into()?));
                for statement in statements.into_iter().rev() {
                    body = match statement {
                        Statement::Let {
                            var,
                            ty,
                            body: value,
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
                            return Err(
                                "Program blocks only support \\let and \\bind statements".into()
                            );
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
                    .collect::<Result<_, String>>()?,
            }),
            SExp::PRun {
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
            SExp::PRunCase {
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
            _ => Err("expected Program computation syntax".into()),
        }
    }
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
    pub record_fields: Option<Vec<Identifier>>,
    pub type_name: Identifier,
    pub ctor_names: Vec<Identifier>,
    pub inductive: crate::raw::ids::ProgramInductiveId,
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
    // Apply the projection definition generated for a record field.
    pub fn field_projection(
        &self,
        env: &crate::raw::environment::CrateEnv,
        e: Exp,
        field_name: &Identifier,
        parameters: &[Exp],
    ) -> Option<Exp> {
        let arena = env.arena();
        let (_, definition) = self
            .associated_definitions
            .iter()
            .find(|(name, _)| name == field_name)?;
        let projection = arena.alloc(ExpNode::DefinedConstant(*definition));
        Some(crate::raw::utils::assoc_apply(
            arena,
            projection,
            parameters.iter().copied().chain([e]).collect(),
        ))
    }
}
