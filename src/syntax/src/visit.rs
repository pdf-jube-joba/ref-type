//! Traverse module paths wherever they occur, including expression arguments.
use crate::{sort::Sort, syntax::*};
use std::sync::Arc;

pub trait ModulePaths {
    fn visit_module_paths(&mut self, action: &mut impl FnMut(&mut ModuleInstantiatePath));
}

macro_rules! leaf {
    ($($ty:ty),* $(,)?) => {$(
        impl ModulePaths for $ty {
            fn visit_module_paths(&mut self, _: &mut impl FnMut(&mut ModuleInstantiatePath)) {}
        }
    )*};
}
leaf!(
    Identifier,
    SourceSpan,
    SurfaceMeta,
    Sort,
    InductiveKind,
    MacroToken,
    MacroSeqAtom,
    TokenMatchPattern,
    SourceFile,
    u32,
    usize,
    String
);
impl<T: ModulePaths> ModulePaths for Vec<T> {
    fn visit_module_paths(&mut self, action: &mut impl FnMut(&mut ModuleInstantiatePath)) {
        for item in self {
            item.visit_module_paths(action);
        }
    }
}
impl<T: ModulePaths> ModulePaths for Option<T> {
    fn visit_module_paths(&mut self, action: &mut impl FnMut(&mut ModuleInstantiatePath)) {
        if let Some(item) = self {
            item.visit_module_paths(action);
        }
    }
}
impl<T: ModulePaths> ModulePaths for Box<T> {
    fn visit_module_paths(&mut self, action: &mut impl FnMut(&mut ModuleInstantiatePath)) {
        self.as_mut().visit_module_paths(action);
    }
}
impl ModulePaths for Arc<SourceFile> {
    fn visit_module_paths(&mut self, _: &mut impl FnMut(&mut ModuleInstantiatePath)) {}
}
macro_rules! tuple {
    ($($ty:ident : $value:ident),+) => {
        impl<$($ty: ModulePaths),+> ModulePaths for ($($ty,)+) {
            fn visit_module_paths(&mut self, action: &mut impl FnMut(&mut ModuleInstantiatePath)) {
                let ($($value,)+) = self;
                $($value.visit_module_paths(action);)+
            }
        }
    };
}
tuple!(A: a, B: b);
tuple!(A: a, B: b, C: c);
macro_rules! visit_struct {
    ($name:ident { $($field:ident),* $(,)? }) => {
        impl ModulePaths for $name {
            fn visit_module_paths(&mut self, action: &mut impl FnMut(&mut ModuleInstantiatePath)) {
                $(self.$field.visit_module_paths(action);)*
            }
        }
    };
}
macro_rules! visit_enum {
    ($name:ident {
        $($variant:ident $( ( $($argument:ident),* ) )?
            $( { $($field:ident),* $(,)? } )?),* $(,)?
    }) => {
        impl ModulePaths for $name {
            fn visit_module_paths(&mut self, action: &mut impl FnMut(&mut ModuleInstantiatePath)) {
                match self {
                    $(Self::$variant $( ($($argument),*) )? $( { $($field),* } )? => {
                        $($($argument.visit_module_paths(action);)*)?
                        $($($field.visit_module_paths(action);)*)?
                    },)*
                }
            }
        }
    };
}
impl ModulePaths for ModuleInstantiatePath {
    fn visit_module_paths(&mut self, action: &mut impl FnMut(&mut ModuleInstantiatePath)) {
        action(self);
        let calls = match self {
            Self::FromCurrent { calls, .. }
            | Self::FromRoot { calls }
            | Self::FromImport { calls, .. } => calls,
        };
        calls.visit_module_paths(action);
    }
}
visit_struct!(Module {
    name,
    parameters,
    body,
    span,
    declaration_spans,
    source,
    header_source
});
visit_enum!(ModuleBody {
    Inline(value0),
    External,
});

visit_enum!(ModuleItem {
    Scoped { exports, items },
    Definition { owner, name, binders, ty, body },
    Inductive { type_name, parameters, indices, kind, constructors },
    Structure { name, kind, parameters, fields, field_spans },
    Record { type_name, parameters, kind, fields },
    ChildModule { module },
    MathMacro { name, before, after },
    UserMacro { name, before, after },
    UseMacro { path, macro_name, name },
    Eval { exp },
    Normalize { exp },
    ValueTypeCheck { ty },
    Check { exp, ty },
    Infer { exp },
    Import { path, import_name },
});

visit_struct!(AssociatedOwner {
    type_name,
    parameters
});

visit_enum!(MacroExp {
    RawExp(value0),
    TemplateName(value0),
    TokenParameter(value0),
    Splice(value0),
    Tok(value0),
    Quoted(value0),
    Seq(value0),
});

visit_struct!(RightBind { vars, ty });

visit_enum!(ValueTypeExp {
    Deferred { expression },
    Meta { kind, span },
    Access { access, parameters },
    Thunk(value0),
    RunStep { state_ty, result_ty },
});

visit_enum!(ComputationTypeExp {
    Deferred { expression },
    Meta { kind, span },
    Return(value0),
    Function { domain, codomain },
});

visit_enum!(ValueTermExp {
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

visit_enum!(ComputationTermExp {
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

visit_enum!(ProgramFunctionExp {
    Access(value0),
    Associated { span, datatype, item, parameters },
    Value(value0),
    Computation(value0),
});

visit_enum!(Bind {
    Named(value0),
    Subset { var, ty, predicate },
    SubsetWithProof { var, ty, predicate, proof_var },
});

visit_enum!(LocalAccess {
    Current { span, access },
    Named { span, access, child },
    Instantiated { span, path, child },
});

visit_enum!(SExp {
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
    IdElim { left, right, var, ty, family, base, equality },
    TransportEq { var, ty, index, family, base },
    AxiomSetExt { left, right, left_to_right, right_to_left },
    AxiomFunExt { left, right, pointwise },
    AxiomClassicalIndefiniteChoice { domain, family, inhabited },
    ChoiceEq { set, element, existence, uniqueness },
    Block(value0),
    Program(value0),
    MathMacro { tokens },
    NamedMacro { name, tokens },
});

visit_struct!(Block { statements, result });

visit_enum!(Statement {
    Fun(value0),
    Let { span, var, ty, body },
    Bind { var, ty, computation },
    Sufficient { map, map_ty },
    TakeFrom { var, ty, existence },
});
