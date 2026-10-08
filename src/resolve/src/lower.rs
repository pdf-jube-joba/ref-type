//! Structural conversion before resolution.
use crate::hir;
use std::sync::Arc;
use syntax::{sort::Sort, syntax::*};

trait Extend {
    type Output;
    fn extend(self) -> Self::Output;
}

fn extend<T: Extend>(value: T) -> T::Output {
    value.extend()
}

macro_rules! identity {
    ($($ty:ty),* $(,)?) => {$(
        impl Extend for $ty {
            type Output = Self;
            fn extend(self) -> Self { self }
        }
    )*};
}
identity!(
    MacroToken,
    SourceSpan,
    SurfaceMeta,
    u32,
    Sort,
    Arc<SourceFile>,
    usize,
    u16,
    u64,
    String
);

impl<T: Extend> Extend for Vec<T> {
    type Output = Vec<T::Output>;
    fn extend(self) -> Self::Output {
        self.into_iter().map(extend).collect()
    }
}
impl<T: Extend> Extend for Option<T> {
    type Output = Option<T::Output>;
    fn extend(self) -> Self::Output {
        self.map(extend)
    }
}
impl<T: Extend> Extend for Box<T> {
    type Output = Box<T::Output>;
    fn extend(self) -> Self::Output {
        Box::new(extend(*self))
    }
}
macro_rules! tuple {
    ($($ty:ident : $value:ident),+) => {
        impl<$($ty: Extend),+> Extend for ($($ty,)+) {
            type Output = ($($ty::Output,)+);
            fn extend(self) -> Self::Output {
                let ($($value,)+) = self;
                ($(extend($value),)+)
            }
        }
    };
}
tuple!(A: a, B: b);
tuple!(A: a, B: b, C: c);

macro_rules! extend_struct {
    ($name:ident { $($field:ident),* $(,)? }) => {
        impl Extend for $name {
            type Output = hir::$name;
            fn extend(self) -> Self::Output {
                hir::$name { $($field: extend(self.$field)),* }
            }
        }
    };
}
macro_rules! extend_field {
    ($extension:ident, $field:ident) => {
        extend($field)
    };
    ($extension:ident, $field:ident => $value:expr) => {
        $value
    };
}
macro_rules! extend_enum {
    ($name:ident {
        $($variant:ident $( ( $($argument:ident),* ) )?
            $( { $($field:ident $(=> $value:expr)?),* $(,)? } )?),* $(,)?
    } $(special { $($pattern:pat => $body:expr),* $(,)? })?) => {
        impl Extend for $name {
            type Output = hir::$name;
            fn extend(self) -> Self::Output {
                match self {
                    $(Self::$variant $( ($($argument),*) )? $( { $($field),* } )? =>
                        hir::$name::$variant $( ($(extend($argument)),*) )?
                        $( { $($field: extend_field!(Unused, $field $(=> $value)?)),* } )?,)*
                    $($($pattern => $body,)*)?
                }
            }
        }
    };
}

impl Extend for Module {
    type Output = hir::Module;
    fn extend(self) -> Self::Output {
        hir::Module {
            id: hir::ModuleId::default(),
            name: extend(self.name),
            parameters: extend(self.parameters),
            parameter_checks: Vec::new(),
            parameter_sources: Default::default(),
            body: extend(self.body),
            span: self.span,
            declaration_spans: self.declaration_spans,
            source: self.source,
            header_source: self.header_source,
        }
    }
}
pub(crate) fn module(module: Module) -> hir::Module {
    extend(module)
}
impl Extend for Identifier {
    type Output = hir::Identifier;
    fn extend(self) -> Self::Output {
        hir::Identifier(self.0)
    }
}
extend_enum!(InductiveKind { Pts(sort), Program });
extend_enum!(MacroSeqAtom { Capture(name), TokenCapture(name), Rest(name), Tok(token), Quoted(text), Seq(items) });
extend_enum!(TokenMatchPattern { Token(atom), Sequence(items), Default });

extend_enum!(ModuleBody {
    Inline(value0),
    External,
});

extend_enum!(ModuleItem {
    Scoped { exports, items },
    Definition { owner, name, binders, ty, body },
    Inductive { type_name, parameters, indices, kind, constructors },
    Structure { name, kind, parameters, fields, field_spans },
    Record { type_name, parameters, kind, fields },
    ChildModule { module },
    MathMacro { name, before, after },
    UserMacro { name, before, after },
    UseMacro { import_name, macro_name },
    Eval { exp },
    Normalize { exp },
    ValueTypeCheck { ty },
    Check { exp, ty },
    Infer { exp },
} special {
    ModuleItem::Import { path, import_name } => hir::ModuleItem::Import {
        path: extend(path), import_name: extend(import_name), checks: Vec::new(),
    }
});

extend_struct!(AssociatedOwner {
    type_name,
    parameters
});

extend_enum!(ModuleInstantiatePath {
    FromCurrent { back_parent, calls },
    FromRoot { calls },
    FromImport { import_name, calls },
});

extend_enum!(MacroExp {
    RawExp(value0),
    TemplateName(value0),
    TokenParameter(value0),
    Splice(value0),
    Tok(value0),
    Quoted(value0),
    Seq(value0),
});

extend_struct!(RightBind { vars, ty });

extend_enum!(ValueTypeExp {
    Deferred { expression },
    Meta { kind, span },
    Access { access, parameters },
    Thunk(value0),
    RunStep { state_ty, result_ty },
});

extend_enum!(ComputationTypeExp {
    Deferred { expression },
    Meta { kind, span },
    Return(value0),
    Function { domain, codomain },
});

extend_enum!(ValueTermExp {
    Deferred { expression },
    Ascribe { term, ty },
    Meta { kind, span },
    Access(value0),
    Record { datatype, parameters, fields },
    Constructor { span, datatype, constructor, parameters, fields },
    Thunk(value0),
    Continue { state_ty, result_ty, next },
    Finish { state_ty, result_ty, output },
});

extend_enum!(ComputationTermExp {
    Deferred { expression },
    Ascribe { term, ty },
    Meta { kind, span },
    Access(value0),
    Associated { span, datatype, item, parameters },
    InferredProjection { value, field, span },
    Return(value0),
    Force(value0),
    Lambda { var, value_ty, body },
    Application { function, arguments },
    Sequence { computation, var, value_ty, body },
    ValueLet { var, value_ty, value, body },
    Case { datatype, scrutinee, branches },
    Run { state_ty, result_ty, step, initial, accessibility },
    RunCase { state_ty, result_ty, step, initial, transition, accessibility, transition_equality },
});

extend_enum!(ProgramFunctionExp {
    Access(value0),
    Associated { span, datatype, item, parameters },
    Value(value0),
    Computation(value0),
});

extend_enum!(Bind {
    Named(value0),
    Subset { var, ty, predicate },
    SubsetWithProof { var, ty, predicate, proof_var },
});

extend_enum!(LocalAccess {
    Current { span, access },
    Named { span, access, child },
    Instantiated { span, path, child },
});

extend_enum!(SExp {
    MemberAccess { base, field, parameters, span },
    MemberLiteral { ty, fields },
    Ascribe { term, ty },
    Assign { value, number, span },
    Meta { kind, span },
    AccessPath { access, parameters },
    AssociatedAccess { span, base, field },
    InferredProjection { value, field, span },
    MacroParameter(value0),
    TokenMatch { target, branches },
    Where { exp, clauses, span },
    Sort(value0),
    ValueType,
    Prod { bind, body },
    Lam { bind, body },
    App { func, arg },
    SubsetIntro { superset, subset, element, proof },
    IndCase { path, scrutinee, return_type, branches },
    Induction { binders, return_type, cases },
    ThunkType { computation_ty },
    ReturnType { value_ty },
    ComputationFunction { domain, codomain },
    Thunk { computation },
    Return { value },
    Force { value },
    ComputationLam { var, value_ty, body },
    Sequence { computation, var, value_ty, body },
    ValueLet { var, value_ty, value, body },
    ProgramCase { path, scrutinee, branches },
    ProgramStepMatch { state_ty, result_ty, computation_ty, on_continue, on_finish, scrutinee },
    RunStep { state_ty, result_ty },
    Continue { state_ty, result_ty, next },
    Finish { state_ty, result_ty, output },
    Run { state_ty, result_ty, step, initial, accessibility },
    RunCase { state_ty, result_ty, step, initial, transition, accessibility, transition_equality },
    SetStepMatch { state_ty, result_ty, motive, on_continue, on_finish },
    BoxType { program_ty },
    BoxProgram { program_ty, program },
    ForceBox { program_ty, boxed },
    BoxApp { function, argument },
    RecordTypeCtor { access, parameters, fields },
    PowerSet { set },
    SubSet { var, set, predicate },
    Pred { superset, subset, element },
    TypeLift { superset, subset },
    Equal { left, right },
    Exists { bind },
    Choice { set, existence, uniqueness },
    TakeProp { bind, body, existence },
    ExistsIntro { element, set },
    SubsetElim { element, subset, superset },
    IdRefl { element },
    IdElim { left, right, var, ty, predicate, base, equality },
    AxiomSetExt { left, right, left_to_right, right_to_left },
    AxiomFunExt { left, right, pointwise },
    AxiomClassicalIndefiniteChoice { domain, family, inhabited },
    ChoiceEq { set, element, existence, uniqueness },
    Block(value0),
    Program(value0),
} special {
    Self::MathMacro { tokens } => hir::SExp::MathMacro { tokens: extend(tokens), scope: None, max_order: None, depth: 0 },
    Self::NamedMacro { name, tokens } => hir::SExp::NamedMacro { name: extend(name), tokens: extend(tokens), scope: None, max_order: None, depth: 0 }
});

extend_struct!(Block { statements, result });

extend_enum!(Statement {
    Fun(value0),
    Let { span, var, ty, body },
    Bind { var, ty, computation },
    Sufficient { map, map_ty },
    TakeFrom { var, ty, existence },
});
