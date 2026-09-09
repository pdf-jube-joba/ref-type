//! Sort-indexed syntax with separate Set, Prop, Value, and Computation families.
//! Each family has Term, Type, and Kind handles. Only level-indexed families
//! carry a level; Prop's sort is fixed by its handle.
//!
//! Proofs cannot be used where a Set term is required:
//! ```compile_fail
//! use kernel::syntax::{PropTerm, SetTerm};
//! fn as_set_term(proof: PropTerm) -> SetTerm { proof }
//! ```
//! Likewise, propositions cannot be used as Set types:
//! ```compile_fail
//! use kernel::syntax::{PropType, SetType};
//! fn as_set_type(proposition: PropType) -> SetType { proposition }
//! ```
use super::sort::*;
use crate::ids::*;
use std::cell::RefCell;
// Keep every family in Set/Prop/Value/Computation order, then Term/Type/Kind.
// One table defines handles, family tags, conversions, and arena partitions.
macro_rules! syntax_families {
    ($($handle:ident => $storage:ident, $sort:pat, $stage:ident;)+) => {
        $(
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub struct $handle(u32);
            impl $handle {
                pub fn index(self) -> usize { self.0 as usize }
            }
            impl From<$handle> for Expression {
                fn from(h: $handle) -> Self { Self::$handle(h) }
            }
            impl TryFrom<Expression> for $handle {
                type Error = String;
                fn try_from(e: Expression) -> Result<Self, String> {
                    match e {
                        Expression::$handle(h) => Ok(h),
                        _ => Err(concat!("expected ", stringify!($handle)).into()),
                    }
                }
            }
        )+
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Expression { $($handle($handle),)+ }
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Family { $($handle,)+ }
        impl Expression {
            pub fn family(self) -> Family {
                match self { $(Self::$handle(..) => Family::$handle,)+ }
            }
        }
        impl Family {
            pub fn stage(self) -> Stage {
                match self { $(Self::$handle => Stage::$stage,)+ }
            }
            pub fn at(sort: BaseSort, stage: Stage) -> Self {
                match (sort, stage) { $(($sort, Stage::$stage) => Self::$handle,)+ }
            }
        }
        #[derive(Debug, Default)]
        pub struct Arena {
            interner: RefCell<std::collections::HashMap<(Family, Data), Expression>>,
            loose_bound_cache: RefCell<std::collections::HashMap<Expression, Option<usize>>>,
            $($storage: RefCell<Vec<Data>>,)+
        }
        impl Arena {
            pub fn sort(&self, e: impl Into<Expression>) -> BaseSort {
                match e.into() { $(Expression::$handle(h) => self.$storage.borrow()[h.index()].sort,)+ }
            }
            pub(crate) fn data(&self, e: Expression) -> Data {
                match e { $(Expression::$handle(h) => self.$storage.borrow()[h.index()].clone(),)+ }
            }
            pub(crate) fn store(&self, family: Family, data: Data) -> Expression {
                let key = (family, data.clone());
                if let Some(&e) = self.interner.borrow().get(&key) { return e; }
                let result = match family {
                    $(Family::$handle => {
                        let mut v = self.$storage.borrow_mut();
                        let h = $handle(u32::try_from(v.len()).expect("arena exhausted"));
                        v.push(data);
                        h.into()
                    },)+
                };
                self.interner.borrow_mut().insert(key, result);
                result
            }
        }
    };
}

// A classified subset of Expression with checked conversions in both directions.
macro_rules! expression_subset {
    ($name:ident, $error:literal; $($handle:ident),+ $(,)?) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum $name { $($handle($handle),)+ }
        $(impl From<$handle> for $name {
            fn from(h: $handle) -> Self { Self::$handle(h) }
        })+
        impl From<$name> for Expression {
            fn from(e: $name) -> Self {
                match e { $($name::$handle(h) => h.into(),)+ }
            }
        }
        impl TryFrom<Expression> for $name {
            type Error = String;
            fn try_from(e: Expression) -> Result<Self, String> {
                match e {
                    $(Expression::$handle(h) => Ok(Self::$handle(h)),)+
                    _ => Err($error.into()),
                }
            }
        }
    };
}

// Each singleton field records how many binders its child crosses.
macro_rules! child_fields {
    ($($child:ident => $depth:expr),* $(,)?) => {
        vec![$(vec![Child { depth: $depth, expression: $child.into() }]),*]
    };
}

syntax_families! {
    SetTerm => setterm, BaseSort::Set(_), Term;
    SetType => settype, BaseSort::Set(_), Type;
    SetKind => setkind, BaseSort::Set(_), Kind;
    PropTerm => propterm, BaseSort::Prop, Term;
    PropType => proptype, BaseSort::Prop, Type;
    PropKind => propkind, BaseSort::Prop, Kind;
    ValueTerm => valueterm, BaseSort::Value(_), Term;
    ValueType => valuetype, BaseSort::Value(_), Type;
    ValueKind => valuekind, BaseSort::Value(_), Kind;
    ComputationTerm => computationterm, BaseSort::Computation(_), Term;
    ComputationType => computationtype, BaseSort::Computation(_), Type;
    ComputationKind => computationkind, BaseSort::Computation(_), Kind;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Stage {
    Term,
    Type,
    Kind,
}

expression_subset!(SetExpression, "expected Set expression"; SetTerm, SetType, SetKind);
expression_subset!(PropExpression, "expected Prop expression"; PropTerm, PropType, PropKind);
expression_subset!(SetArgument, "expected Set argument"; SetTerm, SetType);
expression_subset!(PropArgument, "expected Prop argument"; PropTerm, PropType);
expression_subset!(LogicalTerm, "expected Set/Prop term"; SetTerm, PropTerm);
expression_subset!(LogicalType, "expected Set/Prop type"; SetType, PropType);
expression_subset!(LogicalKind, "expected Set/Prop kind"; SetKind, PropKind);
expression_subset!(ProgramTerm, "wrong syntax family"; ValueTerm, ComputationTerm);
expression_subset!(ProgramType, "wrong syntax family"; ValueType, ComputationType);
expression_subset!(ProgramKind, "wrong syntax family"; ValueKind, ComputationKind);

/// Set/Prop expressions used by mixed binders and inductive elimination.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicalExpression {
    Set(SetExpression),
    Prop(PropExpression),
}
impl From<SetExpression> for LogicalExpression {
    fn from(e: SetExpression) -> Self {
        Self::Set(e)
    }
}
impl From<SetTerm> for LogicalExpression {
    fn from(h: SetTerm) -> Self {
        Self::Set(h.into())
    }
}
impl From<SetType> for LogicalExpression {
    fn from(h: SetType) -> Self {
        Self::Set(h.into())
    }
}
impl From<SetKind> for LogicalExpression {
    fn from(h: SetKind) -> Self {
        Self::Set(h.into())
    }
}
impl From<PropExpression> for LogicalExpression {
    fn from(e: PropExpression) -> Self {
        Self::Prop(e)
    }
}
impl From<PropTerm> for LogicalExpression {
    fn from(h: PropTerm) -> Self {
        Self::Prop(h.into())
    }
}
impl From<PropType> for LogicalExpression {
    fn from(h: PropType) -> Self {
        Self::Prop(h.into())
    }
}
impl From<PropKind> for LogicalExpression {
    fn from(h: PropKind) -> Self {
        Self::Prop(h.into())
    }
}
impl From<LogicalExpression> for Expression {
    fn from(e: LogicalExpression) -> Self {
        match e {
            LogicalExpression::Set(e) => e.into(),
            LogicalExpression::Prop(e) => e.into(),
        }
    }
}
impl TryFrom<Expression> for LogicalExpression {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        if let Ok(e) = SetExpression::try_from(e) {
            Ok(Self::Set(e))
        } else {
            PropExpression::try_from(e).map(Self::Prop)
        }
    }
}

/// Set/Prop arguments used by mixed binders and inductive elimination.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicalArgument {
    Set(SetArgument),
    Prop(PropArgument),
}
impl From<SetArgument> for LogicalArgument {
    fn from(e: SetArgument) -> Self {
        Self::Set(e)
    }
}
impl From<SetTerm> for LogicalArgument {
    fn from(h: SetTerm) -> Self {
        Self::Set(h.into())
    }
}
impl From<SetType> for LogicalArgument {
    fn from(h: SetType) -> Self {
        Self::Set(h.into())
    }
}
impl From<PropArgument> for LogicalArgument {
    fn from(e: PropArgument) -> Self {
        Self::Prop(e)
    }
}
impl From<PropTerm> for LogicalArgument {
    fn from(h: PropTerm) -> Self {
        Self::Prop(h.into())
    }
}
impl From<PropType> for LogicalArgument {
    fn from(h: PropType) -> Self {
        Self::Prop(h.into())
    }
}
impl From<LogicalArgument> for Expression {
    fn from(e: LogicalArgument) -> Self {
        match e {
            LogicalArgument::Set(e) => e.into(),
            LogicalArgument::Prop(e) => e.into(),
        }
    }
}
impl TryFrom<Expression> for LogicalArgument {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        if let Ok(e) = SetArgument::try_from(e) {
            Ok(Self::Set(e))
        } else {
            PropArgument::try_from(e).map(Self::Prop)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SetTermForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
    ReflectedProgramParam {
        parameter: ModuleParamId,
    },
    LambdaTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: SetType,
        body: SetTerm,
    },
    LambdaType {
        rule: ProductRule,
        var: SymbolId,
        domain: SetKind,
        body: SetTerm,
    },
    AppTerm {
        rule: ProductRule,
        function: SetTerm,
        argument: SetTerm,
    },
    AppType {
        rule: ProductRule,
        function: SetTerm,
        argument: SetType,
    },
    Subset {
        var: SymbolId,
        set: SetType,
        predicate: PropType,
    },
    SubsetIntro {
        superset: SetType,
        subset: SetTerm,
        element: SetTerm,
        proof: PropTerm,
    },
    Continue {
        state_ty: SetType,
        result_ty: SetType,
        next: SetTerm,
    },
    Finish {
        state_ty: SetType,
        result_ty: SetType,
        output: SetTerm,
    },
    SetRun {
        state_ty: SetType,
        result_ty: SetType,
        step: SetTerm,
        initial: SetTerm,
        accessibility: PropTerm,
    },
    SetRunCase {
        state_ty: SetType,
        result_ty: SetType,
        step: SetTerm,
        initial: SetTerm,
        transition: SetTerm,
        accessibility: PropTerm,
        transition_equality: PropTerm,
    },
    Recursor {
        rule: ProductRule,
        var: SymbolId,
        state_ty: SetType,
        result_ty: SetType,
        motive: SetType,
        on_continue: SetTerm,
        on_finish: SetTerm,
        scrutinee: SetTerm,
    },
    BoxProgram {
        program_ty: ProgramType,
        program: ProgramTerm,
        certified_reflection: SetTerm,
    },
    ForceBox {
        program_ty: ProgramType,
        boxed: SetTerm,
    },
    BoxApp {
        rule: ProductRule,
        domain: ValueType,
        codomain: ComputationType,
        function: SetTerm,
        argument: SetTerm,
    },
    BoxTypeApp {
        rule: ProductRule,
        var: SymbolId,
        domain: ProgramKind,
        codomain: ComputationType,
        function: SetTerm,
        argument: ProgramType,
    },
    TakeSet {
        domain: SetType,
        codomain: SetType,
        map: SetTerm,
        existence: PropTerm,
        uniqueness: PropTerm,
    },
    IndCtor {
        inductive: InductiveId,
        constructor: usize,
        parameters: Vec<LogicalArgument>,
    },
    IndElim {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: LogicalArgument,
        motive_domains: Vec<LogicalExpression>,
        motive_body: LogicalExpression,
        cases: Vec<LogicalArgument>,
    },
    SetCase {
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
        result_ty: SetType,
        scrutinee: SetTerm,
        branches: Vec<SetTerm>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetTermNode {
    pub level: usize,
    pub form: SetTermForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SetTypeForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
    ReflectedProgramParam {
        parameter: ModuleParamId,
    },
    ProdTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: SetType,
        body: SetType,
    },
    ProdType {
        rule: ProductRule,
        var: SymbolId,
        domain: SetKind,
        body: SetType,
    },
    LambdaTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: SetType,
        body: SetType,
    },
    LambdaType {
        rule: ProductRule,
        var: SymbolId,
        domain: SetKind,
        body: SetType,
    },
    AppTerm {
        rule: ProductRule,
        function: SetType,
        argument: SetTerm,
    },
    AppType {
        rule: ProductRule,
        function: SetType,
        argument: SetType,
    },
    PowerSet {
        set: SetType,
    },
    TypeLift {
        superset: SetType,
        subset: SetTerm,
    },
    RunStep {
        state_ty: SetType,
        result_ty: SetType,
    },
    BoxType {
        program_ty: ProgramType,
    },
    Recursor {
        rule: ProductRule,
        var: SymbolId,
        state_ty: SetType,
        result_ty: SetType,
        motive: SetKind,
        on_continue: SetType,
        on_finish: SetType,
        scrutinee: SetTerm,
    },
    IndType {
        inductive: InductiveId,
        parameters: Vec<LogicalArgument>,
    },
    IndCtor {
        inductive: InductiveId,
        constructor: usize,
        parameters: Vec<LogicalArgument>,
    },
    IndElim {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: LogicalArgument,
        motive_domains: Vec<LogicalExpression>,
        motive_body: LogicalExpression,
        cases: Vec<LogicalArgument>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetTypeNode {
    pub level: usize,
    pub form: SetTypeForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SetKindForm {
    Base,
    ProdTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: SetType,
        body: SetKind,
    },
    ProdType {
        rule: ProductRule,
        var: SymbolId,
        domain: SetKind,
        body: SetKind,
    },
    IndType {
        inductive: InductiveId,
        parameters: Vec<LogicalArgument>,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetKindNode {
    pub level: usize,
    pub form: SetKindForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropTermForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
    LambdaTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: LogicalType,
        body: PropTerm,
    },
    LambdaType {
        rule: ProductRule,
        var: SymbolId,
        domain: LogicalKind,
        body: PropTerm,
    },
    AppTerm {
        rule: ProductRule,
        function: PropTerm,
        argument: LogicalTerm,
    },
    AppType {
        rule: ProductRule,
        function: PropTerm,
        argument: LogicalType,
    },
    Recursor {
        rule: ProductRule,
        var: SymbolId,
        state_ty: SetType,
        result_ty: SetType,
        motive: PropType,
        on_continue: PropTerm,
        on_finish: PropTerm,
        scrutinee: SetTerm,
    },
    IdRefl {
        element: SetTerm,
    },
    ExistsIntro {
        element: SetTerm,
        set: SetType,
    },
    SubsetElim {
        element: SetTerm,
        subset: SetTerm,
        superset: SetType,
    },
    IdElim {
        var: SymbolId,
        left: SetTerm,
        right: SetTerm,
        ty: SetType,
        predicate: PropType,
        base: PropTerm,
        equality: PropTerm,
    },
    TakeProp {
        domain: SetType,
        proposition: PropType,
        map: PropTerm,
        existence: PropTerm,
    },
    TakeEq {
        func: SetTerm,
        domain: SetType,
        codomain: SetType,
        element: SetTerm,
        existence: PropTerm,
        uniqueness: PropTerm,
    },
    SetExt {
        left: SetTerm,
        right: SetTerm,
        left_to_right: PropTerm,
        right_to_left: PropTerm,
    },
    FunExt {
        left: SetTerm,
        right: SetTerm,
        pointwise: PropTerm,
    },
    ClassicalIndefiniteChoice {
        domain: SetType,
        family: SetType,
        inhabited: PropTerm,
    },
    AccIntro {
        state_ty: SetType,
        result_ty: SetType,
        step: SetTerm,
        state: SetTerm,
        predecessors: PropTerm,
    },
    AccDescent {
        state_ty: SetType,
        result_ty: SetType,
        step: SetTerm,
        from: SetTerm,
        to: SetTerm,
        accessibility: PropTerm,
        transition: PropTerm,
    },
    IndCtor {
        inductive: InductiveId,
        constructor: usize,
        parameters: Vec<LogicalArgument>,
    },
    IndElim {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: LogicalArgument,
        motive_domains: Vec<LogicalExpression>,
        motive_body: LogicalExpression,
        cases: Vec<LogicalArgument>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropTermNode {
    pub form: PropTermForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropTypeForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
    ProdTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: LogicalType,
        body: PropType,
    },
    ProdType {
        rule: ProductRule,
        var: SymbolId,
        domain: LogicalKind,
        body: PropType,
    },
    LambdaTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: LogicalType,
        body: PropType,
    },
    LambdaType {
        rule: ProductRule,
        var: SymbolId,
        domain: LogicalKind,
        body: PropType,
    },
    AppTerm {
        rule: ProductRule,
        function: PropType,
        argument: LogicalTerm,
    },
    AppType {
        rule: ProductRule,
        function: PropType,
        argument: LogicalType,
    },
    Pred {
        superset: SetType,
        subset: SetTerm,
        element: SetTerm,
    },
    Equal {
        left: SetTerm,
        right: SetTerm,
    },
    Exists {
        set: SetType,
    },
    Acc {
        state_ty: SetType,
        result_ty: SetType,
        step: SetTerm,
        state: SetTerm,
    },
    Recursor {
        rule: ProductRule,
        var: SymbolId,
        state_ty: SetType,
        result_ty: SetType,
        motive: PropKind,
        on_continue: PropType,
        on_finish: PropType,
        scrutinee: SetTerm,
    },
    IndType {
        inductive: InductiveId,
        parameters: Vec<LogicalArgument>,
    },
    IndCtor {
        inductive: InductiveId,
        constructor: usize,
        parameters: Vec<LogicalArgument>,
    },
    IndElim {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: LogicalArgument,
        motive_domains: Vec<LogicalExpression>,
        motive_body: LogicalExpression,
        cases: Vec<LogicalArgument>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropTypeNode {
    pub form: PropTypeForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropKindForm {
    Base,
    ProdTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: LogicalType,
        body: PropKind,
    },
    ProdType {
        rule: ProductRule,
        var: SymbolId,
        domain: LogicalKind,
        body: PropKind,
    },
    IndType {
        inductive: InductiveId,
        parameters: Vec<LogicalArgument>,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropKindNode {
    pub form: PropKindForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueTermForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
    ThunkValue {
        computation: ComputationTerm,
    },
    Continue {
        state_ty: ValueType,
        result_ty: ValueType,
        next: ValueTerm,
    },
    Finish {
        state_ty: ValueType,
        result_ty: ValueType,
        output: ValueTerm,
    },
    InductiveConstructor {
        inductive: ProgramInductiveId,
        constructor: usize,
        parameters: Vec<ProgramType>,
        fields: Vec<ValueTerm>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueTermNode {
    pub level: usize,
    pub form: ValueTermForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueTypeForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
    Thunk {
        computation_ty: ComputationType,
    },
    RunStep {
        state_ty: ValueType,
        result_ty: ValueType,
    },
    Inductive {
        inductive: ProgramInductiveId,
        parameters: Vec<ProgramType>,
    },
    LambdaType {
        rule: ProductRule,
        var: SymbolId,
        domain: ProgramKind,
        body: ValueType,
    },
    AppType {
        rule: ProductRule,
        function: ValueType,
        argument: ProgramType,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueTypeNode {
    pub level: usize,
    pub form: ValueTypeForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueKindForm {
    Base,
    ProdType {
        rule: ProductRule,
        var: SymbolId,
        domain: ProgramKind,
        body: ValueKind,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueKindNode {
    pub level: usize,
    pub form: ValueKindForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComputationTermForm {
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
    Return {
        value: ValueTerm,
    },
    Force {
        value: ValueTerm,
    },
    LambdaTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: ValueType,
        body: ComputationTerm,
    },
    LambdaType {
        rule: ProductRule,
        var: SymbolId,
        domain: ProgramKind,
        body: ComputationTerm,
    },
    AppTerm {
        rule: ProductRule,
        function: ComputationTerm,
        argument: ValueTerm,
    },
    AppType {
        rule: ProductRule,
        function: ComputationTerm,
        argument: ProgramType,
    },
    Sequence {
        var: SymbolId,
        value_ty: ValueType,
        computation: ComputationTerm,
        body: ComputationTerm,
    },
    ValueLet {
        var: SymbolId,
        value_ty: ValueType,
        value: ValueTerm,
        body: ComputationTerm,
    },
    Case {
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
        result_ty: ComputationType,
        scrutinee: ValueTerm,
        branches: Vec<ComputationTerm>,
    },
    Run {
        state_ty: ValueType,
        result_ty: ValueType,
        step: ValueTerm,
        initial: ValueTerm,
    },
    RunCase {
        state_ty: ValueType,
        result_ty: ValueType,
        step: ValueTerm,
        initial: ValueTerm,
        transition: ComputationTerm,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputationTermNode {
    pub level: usize,
    pub form: ComputationTermForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComputationTypeForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
    ReturnType {
        value_ty: ValueType,
    },
    ProdTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: ValueType,
        body: ComputationType,
    },
    ProdType {
        rule: ProductRule,
        var: SymbolId,
        domain: ProgramKind,
        body: ComputationType,
    },
    LambdaType {
        rule: ProductRule,
        var: SymbolId,
        domain: ProgramKind,
        body: ComputationType,
    },
    AppType {
        rule: ProductRule,
        function: ComputationType,
        argument: ProgramType,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputationTypeNode {
    pub level: usize,
    pub form: ComputationTypeForm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComputationKindForm {
    Base,
    ProdType {
        rule: ProductRule,
        var: SymbolId,
        domain: ProgramKind,
        body: ComputationKind,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputationKindNode {
    pub level: usize,
    pub form: ComputationKindForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Op {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
    ReflectedProgramParam {
        parameter: ModuleParamId,
    },
    LambdaTerm {
        rule: ProductRule,
        var: SymbolId,
    },
    LambdaType {
        rule: ProductRule,
        var: SymbolId,
    },
    AppTerm {
        rule: ProductRule,
    },
    AppType {
        rule: ProductRule,
    },
    Subset {
        var: SymbolId,
    },
    SubsetIntro,
    Continue,
    Finish,
    SetRun,
    SetRunCase,
    Recursor {
        rule: ProductRule,
        var: SymbolId,
    },
    BoxProgram,
    ForceBox,
    BoxApp {
        rule: ProductRule,
    },
    BoxTypeApp {
        rule: ProductRule,
        var: SymbolId,
    },
    IdRefl,
    ExistsIntro,
    SubsetElim,
    IdElim {
        var: SymbolId,
    },
    TakeSet,
    TakeProp,
    TakeEq,
    SetExt,
    FunExt,
    ClassicalIndefiniteChoice,
    AccIntro,
    AccDescent,
    IndCtor {
        inductive: InductiveId,
        constructor: usize,
    },
    IndElim {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
    },
    SetCase {
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
    },
    ProdTerm {
        rule: ProductRule,
        var: SymbolId,
    },
    ProdType {
        rule: ProductRule,
        var: SymbolId,
    },
    PowerSet,
    TypeLift,
    Pred,
    Equal,
    Exists,
    RunStep,
    Acc,
    BoxType,
    IndType {
        inductive: InductiveId,
    },
    Base,
    Thunk,
    Inductive {
        inductive: ProgramInductiveId,
    },
    ReturnType,
    ThunkValue,
    InductiveConstructor {
        inductive: ProgramInductiveId,
        constructor: usize,
    },
    Return,
    Force,
    Sequence {
        var: SymbolId,
    },
    ValueLet {
        var: SymbolId,
    },
    Case {
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
    },
    Run,
    RunCase,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Child {
    pub depth: usize,
    pub expression: Expression,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Data {
    pub sort: BaseSort,
    pub op: Op,
    pub fields: Vec<Vec<Child>>,
}

impl Data {
    pub fn child(&self, i: usize) -> Expression {
        self.fields[i][0].expression
    }

    pub fn children(&self, i: usize) -> Vec<Expression> {
        self.fields[i].iter().map(|x| x.expression).collect()
    }
}

pub trait ArenaNode {
    type Handle;
    fn allocate(self, arena: &Arena) -> Self::Handle;
}

pub trait ArenaHandle: Copy {
    type Node;
    fn get(self, arena: &Arena) -> Self::Node;
}

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc<N: ArenaNode>(&self, node: N) -> N::Handle {
        node.allocate(self)
    }

    pub fn get<H: ArenaHandle>(&self, h: H) -> H::Node {
        h.get(self)
    }

    /// Largest index that escapes the expression's own binders. Arena nodes
    /// are immutable, so this summary also applies to every later traversal.
    pub(crate) fn max_loose_bound(&self, e: Expression) -> Option<usize> {
        if let Some(&cached) = self.loose_bound_cache.borrow().get(&e) {
            return cached;
        }
        let data = self.data(e);
        let result = if let Op::Bound { index } = data.op {
            Some(index)
        } else {
            data.fields
                .iter()
                .flatten()
                .filter_map(|child| {
                    self.max_loose_bound(child.expression)?
                        .checked_sub(child.depth)
                })
                .max()
        };
        self.loose_bound_cache.borrow_mut().insert(e, result);
        result
    }
}

impl ArenaNode for SetTermNode {
    type Handle = SetTerm;
    fn allocate(self, arena: &Arena) -> SetTerm {
        let sort = BaseSort::Set(self.level);
        let (op, fields) = match self.form {
            SetTermForm::Bound { index } => {
                let fields = vec![];
                (Op::Bound { index }, fields)
            }
            SetTermForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            SetTermForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
            SetTermForm::ReflectedProgramParam { parameter } => {
                let fields = vec![];
                (Op::ReflectedProgramParam { parameter }, fields)
            }
            SetTermForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaTerm { rule, var }, fields)
            }
            SetTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaType { rule, var }, fields)
            }
            SetTermForm::AppTerm {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppTerm { rule }, fields)
            }
            SetTermForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppType { rule }, fields)
            }
            SetTermForm::Subset {
                var,
                set,
                predicate,
            } => {
                let fields = child_fields![set => 0, predicate => 1];
                (Op::Subset { var }, fields)
            }
            SetTermForm::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => {
                let fields = child_fields![superset => 0, subset => 0, element => 0, proof => 0];
                (Op::SubsetIntro, fields)
            }
            SetTermForm::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, next => 0];
                (Op::Continue, fields)
            }
            SetTermForm::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, output => 0];
                (Op::Finish, fields)
            }
            SetTermForm::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, step => 0, initial => 0, accessibility => 0];
                (Op::SetRun, fields)
            }
            SetTermForm::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, step => 0, initial => 0, transition => 0, accessibility => 0, transition_equality => 0];
                (Op::SetRunCase, fields)
            }
            SetTermForm::Recursor {
                rule,
                var,
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, motive => 1, on_continue => 0, on_finish => 0, scrutinee => 0];
                (Op::Recursor { rule, var }, fields)
            }
            SetTermForm::BoxProgram {
                program_ty,
                program,
                certified_reflection,
            } => {
                let fields =
                    child_fields![program_ty => 0, program => 0, certified_reflection => 0];
                (Op::BoxProgram, fields)
            }
            SetTermForm::ForceBox { program_ty, boxed } => {
                let fields = child_fields![program_ty => 0, boxed => 0];
                (Op::ForceBox, fields)
            }
            SetTermForm::BoxApp {
                rule,
                domain,
                codomain,
                function,
                argument,
            } => {
                let fields =
                    child_fields![domain => 0, codomain => 0, function => 0, argument => 0];
                (Op::BoxApp { rule }, fields)
            }
            SetTermForm::BoxTypeApp {
                rule,
                var,
                domain,
                codomain,
                function,
                argument,
            } => {
                let fields =
                    child_fields![domain => 0, codomain => 1, function => 0, argument => 0];
                (Op::BoxTypeApp { rule, var }, fields)
            }
            SetTermForm::TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
            } => {
                let fields = child_fields![domain => 0, codomain => 0, map => 0, existence => 0, uniqueness => 0];
                (Op::TakeSet, fields)
            }
            SetTermForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (
                    Op::IndCtor {
                        inductive,
                        constructor,
                    },
                    fields,
                )
            }
            SetTermForm::IndElim {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                cases,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: scrutinee.into(),
                    }],
                    motive_domains
                        .into_iter()
                        .enumerate()
                        .map(|(_i, x)| Child {
                            depth: _i,
                            expression: x.into(),
                        })
                        .collect(),
                    vec![Child {
                        depth: motive_vars.len(),
                        expression: motive_body.into(),
                    }],
                    cases
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (
                    Op::IndElim {
                        inductive,
                        motive_vars,
                    },
                    fields,
                )
            }
            SetTermForm::SetCase {
                inductive,
                binders,
                result_ty,
                scrutinee,
                branches,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: scrutinee.into(),
                    }],
                    branches
                        .into_iter()
                        .enumerate()
                        .map(|(_i, x)| Child {
                            depth: binders[_i].len(),
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (Op::SetCase { inductive, binders }, fields)
            }
        };
        arena
            .store(Family::SetTerm, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for SetTerm {
    type Node = SetTermNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Bound { index } => SetTermForm::Bound { index },
            Op::ModuleParam { parameter } => SetTermForm::ModuleParam { parameter },
            Op::Constant { definition } => SetTermForm::Constant { definition },
            Op::ReflectedProgramParam { parameter } => {
                SetTermForm::ReflectedProgramParam { parameter }
            }
            Op::LambdaTerm { rule, var } => SetTermForm::LambdaTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::LambdaType { rule, var } => SetTermForm::LambdaType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::AppTerm { rule } => SetTermForm::AppTerm {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::AppType { rule } => SetTermForm::AppType {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::Subset { var } => SetTermForm::Subset {
                var,
                set: data.child(0).try_into().expect("family"),
                predicate: data.child(1).try_into().expect("family"),
            },
            Op::SubsetIntro => SetTermForm::SubsetIntro {
                superset: data.child(0).try_into().expect("family"),
                subset: data.child(1).try_into().expect("family"),
                element: data.child(2).try_into().expect("family"),
                proof: data.child(3).try_into().expect("family"),
            },
            Op::Continue => SetTermForm::Continue {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                next: data.child(2).try_into().expect("family"),
            },
            Op::Finish => SetTermForm::Finish {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                output: data.child(2).try_into().expect("family"),
            },
            Op::SetRun => SetTermForm::SetRun {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                initial: data.child(3).try_into().expect("family"),
                accessibility: data.child(4).try_into().expect("family"),
            },
            Op::SetRunCase => SetTermForm::SetRunCase {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                initial: data.child(3).try_into().expect("family"),
                transition: data.child(4).try_into().expect("family"),
                accessibility: data.child(5).try_into().expect("family"),
                transition_equality: data.child(6).try_into().expect("family"),
            },
            Op::Recursor { rule, var } => SetTermForm::Recursor {
                rule,
                var,
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                motive: data.child(2).try_into().expect("family"),
                on_continue: data.child(3).try_into().expect("family"),
                on_finish: data.child(4).try_into().expect("family"),
                scrutinee: data.child(5).try_into().expect("family"),
            },
            Op::BoxProgram => SetTermForm::BoxProgram {
                program_ty: data.child(0).try_into().expect("family"),
                program: data.child(1).try_into().expect("family"),
                certified_reflection: data.child(2).try_into().expect("family"),
            },
            Op::ForceBox => SetTermForm::ForceBox {
                program_ty: data.child(0).try_into().expect("family"),
                boxed: data.child(1).try_into().expect("family"),
            },
            Op::BoxApp { rule } => SetTermForm::BoxApp {
                rule,
                domain: data.child(0).try_into().expect("family"),
                codomain: data.child(1).try_into().expect("family"),
                function: data.child(2).try_into().expect("family"),
                argument: data.child(3).try_into().expect("family"),
            },
            Op::BoxTypeApp { rule, var } => SetTermForm::BoxTypeApp {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                codomain: data.child(1).try_into().expect("family"),
                function: data.child(2).try_into().expect("family"),
                argument: data.child(3).try_into().expect("family"),
            },
            Op::TakeSet => SetTermForm::TakeSet {
                domain: data.child(0).try_into().expect("family"),
                codomain: data.child(1).try_into().expect("family"),
                map: data.child(2).try_into().expect("family"),
                existence: data.child(3).try_into().expect("family"),
                uniqueness: data.child(4).try_into().expect("family"),
            },
            Op::IndCtor {
                inductive,
                constructor,
            } => SetTermForm::IndCtor {
                inductive,
                constructor,
                parameters: data
                    .children(0)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::IndElim {
                inductive,
                motive_vars,
            } => SetTermForm::IndElim {
                inductive,
                motive_vars,
                scrutinee: data.child(0).try_into().expect("family"),
                motive_domains: data
                    .children(1)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
                motive_body: data.child(2).try_into().expect("family"),
                cases: data
                    .children(3)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::SetCase { inductive, binders } => SetTermForm::SetCase {
                inductive,
                binders,
                result_ty: data.child(0).try_into().expect("family"),
                scrutinee: data.child(1).try_into().expect("family"),
                branches: data
                    .children(2)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            _ => unreachable!("invalid arena partition"),
        };
        SetTermNode {
            level: data.sort.level().expect("Set level"),
            form,
        }
    }
}

impl ArenaNode for SetTypeNode {
    type Handle = SetType;
    fn allocate(self, arena: &Arena) -> SetType {
        let sort = BaseSort::Set(self.level);
        let (op, fields) = match self.form {
            SetTypeForm::Bound { index } => {
                let fields = vec![];
                (Op::Bound { index }, fields)
            }
            SetTypeForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            SetTypeForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
            SetTypeForm::ReflectedProgramParam { parameter } => {
                let fields = vec![];
                (Op::ReflectedProgramParam { parameter }, fields)
            }
            SetTypeForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdTerm { rule, var }, fields)
            }
            SetTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdType { rule, var }, fields)
            }
            SetTypeForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaTerm { rule, var }, fields)
            }
            SetTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaType { rule, var }, fields)
            }
            SetTypeForm::AppTerm {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppTerm { rule }, fields)
            }
            SetTypeForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppType { rule }, fields)
            }
            SetTypeForm::PowerSet { set } => {
                let fields = child_fields![set => 0];
                (Op::PowerSet, fields)
            }
            SetTypeForm::TypeLift { superset, subset } => {
                let fields = child_fields![superset => 0, subset => 0];
                (Op::TypeLift, fields)
            }
            SetTypeForm::RunStep {
                state_ty,
                result_ty,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0];
                (Op::RunStep, fields)
            }
            SetTypeForm::BoxType { program_ty } => {
                let fields = child_fields![program_ty => 0];
                (Op::BoxType, fields)
            }
            SetTypeForm::Recursor {
                rule,
                var,
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, motive => 1, on_continue => 0, on_finish => 0, scrutinee => 0];
                (Op::Recursor { rule, var }, fields)
            }
            SetTypeForm::IndType {
                inductive,
                parameters,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (Op::IndType { inductive }, fields)
            }
            SetTypeForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (
                    Op::IndCtor {
                        inductive,
                        constructor,
                    },
                    fields,
                )
            }
            SetTypeForm::IndElim {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                cases,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: scrutinee.into(),
                    }],
                    motive_domains
                        .into_iter()
                        .enumerate()
                        .map(|(_i, x)| Child {
                            depth: _i,
                            expression: x.into(),
                        })
                        .collect(),
                    vec![Child {
                        depth: motive_vars.len(),
                        expression: motive_body.into(),
                    }],
                    cases
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (
                    Op::IndElim {
                        inductive,
                        motive_vars,
                    },
                    fields,
                )
            }
        };
        arena
            .store(Family::SetType, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for SetType {
    type Node = SetTypeNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Bound { index } => SetTypeForm::Bound { index },
            Op::ModuleParam { parameter } => SetTypeForm::ModuleParam { parameter },
            Op::Constant { definition } => SetTypeForm::Constant { definition },
            Op::ReflectedProgramParam { parameter } => {
                SetTypeForm::ReflectedProgramParam { parameter }
            }
            Op::ProdTerm { rule, var } => SetTypeForm::ProdTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::ProdType { rule, var } => SetTypeForm::ProdType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::LambdaTerm { rule, var } => SetTypeForm::LambdaTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::LambdaType { rule, var } => SetTypeForm::LambdaType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::AppTerm { rule } => SetTypeForm::AppTerm {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::AppType { rule } => SetTypeForm::AppType {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::PowerSet => SetTypeForm::PowerSet {
                set: data.child(0).try_into().expect("family"),
            },
            Op::TypeLift => SetTypeForm::TypeLift {
                superset: data.child(0).try_into().expect("family"),
                subset: data.child(1).try_into().expect("family"),
            },
            Op::RunStep => SetTypeForm::RunStep {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
            },
            Op::BoxType => SetTypeForm::BoxType {
                program_ty: data.child(0).try_into().expect("family"),
            },
            Op::Recursor { rule, var } => SetTypeForm::Recursor {
                rule,
                var,
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                motive: data.child(2).try_into().expect("family"),
                on_continue: data.child(3).try_into().expect("family"),
                on_finish: data.child(4).try_into().expect("family"),
                scrutinee: data.child(5).try_into().expect("family"),
            },
            Op::IndType { inductive } => SetTypeForm::IndType {
                inductive,
                parameters: data
                    .children(0)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::IndCtor {
                inductive,
                constructor,
            } => SetTypeForm::IndCtor {
                inductive,
                constructor,
                parameters: data
                    .children(0)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::IndElim {
                inductive,
                motive_vars,
            } => SetTypeForm::IndElim {
                inductive,
                motive_vars,
                scrutinee: data.child(0).try_into().expect("family"),
                motive_domains: data
                    .children(1)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
                motive_body: data.child(2).try_into().expect("family"),
                cases: data
                    .children(3)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            _ => unreachable!("invalid arena partition"),
        };
        SetTypeNode {
            level: data.sort.level().expect("Set level"),
            form,
        }
    }
}

impl ArenaNode for SetKindNode {
    type Handle = SetKind;
    fn allocate(self, arena: &Arena) -> SetKind {
        let sort = BaseSort::Set(self.level);
        let (op, fields) = match self.form {
            SetKindForm::Base => {
                let fields = vec![];
                (Op::Base, fields)
            }
            SetKindForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdTerm { rule, var }, fields)
            }
            SetKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdType { rule, var }, fields)
            }
            SetKindForm::IndType {
                inductive,
                parameters,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (Op::IndType { inductive }, fields)
            }
            SetKindForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            SetKindForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
        };
        arena
            .store(Family::SetKind, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for SetKind {
    type Node = SetKindNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Base => SetKindForm::Base,
            Op::ProdTerm { rule, var } => SetKindForm::ProdTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::ProdType { rule, var } => SetKindForm::ProdType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::IndType { inductive } => SetKindForm::IndType {
                inductive,
                parameters: data
                    .children(0)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::ModuleParam { parameter } => SetKindForm::ModuleParam { parameter },
            Op::Constant { definition } => SetKindForm::Constant { definition },
            _ => unreachable!("invalid arena partition"),
        };
        SetKindNode {
            level: data.sort.level().expect("Set level"),
            form,
        }
    }
}

impl ArenaNode for PropTermNode {
    type Handle = PropTerm;
    fn allocate(self, arena: &Arena) -> PropTerm {
        let sort = BaseSort::Prop;
        let (op, fields) = match self.form {
            PropTermForm::Bound { index } => {
                let fields = vec![];
                (Op::Bound { index }, fields)
            }
            PropTermForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            PropTermForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
            PropTermForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaTerm { rule, var }, fields)
            }
            PropTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaType { rule, var }, fields)
            }
            PropTermForm::AppTerm {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppTerm { rule }, fields)
            }
            PropTermForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppType { rule }, fields)
            }
            PropTermForm::Recursor {
                rule,
                var,
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, motive => 1, on_continue => 0, on_finish => 0, scrutinee => 0];
                (Op::Recursor { rule, var }, fields)
            }
            PropTermForm::IdRefl { element } => {
                let fields = child_fields![element => 0];
                (Op::IdRefl, fields)
            }
            PropTermForm::ExistsIntro { element, set } => {
                let fields = child_fields![element => 0, set => 0];
                (Op::ExistsIntro, fields)
            }
            PropTermForm::SubsetElim {
                element,
                subset,
                superset,
            } => {
                let fields = child_fields![element => 0, subset => 0, superset => 0];
                (Op::SubsetElim, fields)
            }
            PropTermForm::IdElim {
                var,
                left,
                right,
                ty,
                predicate,
                base,
                equality,
            } => {
                let fields = child_fields![left => 0, right => 0, ty => 0, predicate => 1, base => 0, equality => 0];
                (Op::IdElim { var }, fields)
            }
            PropTermForm::TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => {
                let fields = child_fields![domain => 0, proposition => 0, map => 0, existence => 0];
                (Op::TakeProp, fields)
            }
            PropTermForm::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
            } => {
                let fields = child_fields![func => 0, domain => 0, codomain => 0, element => 0, existence => 0, uniqueness => 0];
                (Op::TakeEq, fields)
            }
            PropTermForm::SetExt {
                left,
                right,
                left_to_right,
                right_to_left,
            } => {
                let fields =
                    child_fields![left => 0, right => 0, left_to_right => 0, right_to_left => 0];
                (Op::SetExt, fields)
            }
            PropTermForm::FunExt {
                left,
                right,
                pointwise,
            } => {
                let fields = child_fields![left => 0, right => 0, pointwise => 0];
                (Op::FunExt, fields)
            }
            PropTermForm::ClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            } => {
                let fields = child_fields![domain => 0, family => 0, inhabited => 0];
                (Op::ClassicalIndefiniteChoice, fields)
            }
            PropTermForm::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, step => 0, state => 0, predecessors => 0];
                (Op::AccIntro, fields)
            }
            PropTermForm::AccDescent {
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, step => 0, from => 0, to => 0, accessibility => 0, transition => 0];
                (Op::AccDescent, fields)
            }
            PropTermForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (
                    Op::IndCtor {
                        inductive,
                        constructor,
                    },
                    fields,
                )
            }
            PropTermForm::IndElim {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                cases,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: scrutinee.into(),
                    }],
                    motive_domains
                        .into_iter()
                        .enumerate()
                        .map(|(_i, x)| Child {
                            depth: _i,
                            expression: x.into(),
                        })
                        .collect(),
                    vec![Child {
                        depth: motive_vars.len(),
                        expression: motive_body.into(),
                    }],
                    cases
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (
                    Op::IndElim {
                        inductive,
                        motive_vars,
                    },
                    fields,
                )
            }
        };
        arena
            .store(Family::PropTerm, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for PropTerm {
    type Node = PropTermNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Bound { index } => PropTermForm::Bound { index },
            Op::ModuleParam { parameter } => PropTermForm::ModuleParam { parameter },
            Op::Constant { definition } => PropTermForm::Constant { definition },
            Op::LambdaTerm { rule, var } => PropTermForm::LambdaTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::LambdaType { rule, var } => PropTermForm::LambdaType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::AppTerm { rule } => PropTermForm::AppTerm {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::AppType { rule } => PropTermForm::AppType {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::Recursor { rule, var } => PropTermForm::Recursor {
                rule,
                var,
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                motive: data.child(2).try_into().expect("family"),
                on_continue: data.child(3).try_into().expect("family"),
                on_finish: data.child(4).try_into().expect("family"),
                scrutinee: data.child(5).try_into().expect("family"),
            },
            Op::IdRefl => PropTermForm::IdRefl {
                element: data.child(0).try_into().expect("family"),
            },
            Op::ExistsIntro => PropTermForm::ExistsIntro {
                element: data.child(0).try_into().expect("family"),
                set: data.child(1).try_into().expect("family"),
            },
            Op::SubsetElim => PropTermForm::SubsetElim {
                element: data.child(0).try_into().expect("family"),
                subset: data.child(1).try_into().expect("family"),
                superset: data.child(2).try_into().expect("family"),
            },
            Op::IdElim { var } => PropTermForm::IdElim {
                var,
                left: data.child(0).try_into().expect("family"),
                right: data.child(1).try_into().expect("family"),
                ty: data.child(2).try_into().expect("family"),
                predicate: data.child(3).try_into().expect("family"),
                base: data.child(4).try_into().expect("family"),
                equality: data.child(5).try_into().expect("family"),
            },
            Op::TakeProp => PropTermForm::TakeProp {
                domain: data.child(0).try_into().expect("family"),
                proposition: data.child(1).try_into().expect("family"),
                map: data.child(2).try_into().expect("family"),
                existence: data.child(3).try_into().expect("family"),
            },
            Op::TakeEq => PropTermForm::TakeEq {
                func: data.child(0).try_into().expect("family"),
                domain: data.child(1).try_into().expect("family"),
                codomain: data.child(2).try_into().expect("family"),
                element: data.child(3).try_into().expect("family"),
                existence: data.child(4).try_into().expect("family"),
                uniqueness: data.child(5).try_into().expect("family"),
            },
            Op::SetExt => PropTermForm::SetExt {
                left: data.child(0).try_into().expect("family"),
                right: data.child(1).try_into().expect("family"),
                left_to_right: data.child(2).try_into().expect("family"),
                right_to_left: data.child(3).try_into().expect("family"),
            },
            Op::FunExt => PropTermForm::FunExt {
                left: data.child(0).try_into().expect("family"),
                right: data.child(1).try_into().expect("family"),
                pointwise: data.child(2).try_into().expect("family"),
            },
            Op::ClassicalIndefiniteChoice => PropTermForm::ClassicalIndefiniteChoice {
                domain: data.child(0).try_into().expect("family"),
                family: data.child(1).try_into().expect("family"),
                inhabited: data.child(2).try_into().expect("family"),
            },
            Op::AccIntro => PropTermForm::AccIntro {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                state: data.child(3).try_into().expect("family"),
                predecessors: data.child(4).try_into().expect("family"),
            },
            Op::AccDescent => PropTermForm::AccDescent {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                from: data.child(3).try_into().expect("family"),
                to: data.child(4).try_into().expect("family"),
                accessibility: data.child(5).try_into().expect("family"),
                transition: data.child(6).try_into().expect("family"),
            },
            Op::IndCtor {
                inductive,
                constructor,
            } => PropTermForm::IndCtor {
                inductive,
                constructor,
                parameters: data
                    .children(0)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::IndElim {
                inductive,
                motive_vars,
            } => PropTermForm::IndElim {
                inductive,
                motive_vars,
                scrutinee: data.child(0).try_into().expect("family"),
                motive_domains: data
                    .children(1)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
                motive_body: data.child(2).try_into().expect("family"),
                cases: data
                    .children(3)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            _ => unreachable!("invalid arena partition"),
        };
        PropTermNode { form }
    }
}

impl ArenaNode for PropTypeNode {
    type Handle = PropType;
    fn allocate(self, arena: &Arena) -> PropType {
        let sort = BaseSort::Prop;
        let (op, fields) = match self.form {
            PropTypeForm::Bound { index } => {
                let fields = vec![];
                (Op::Bound { index }, fields)
            }
            PropTypeForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            PropTypeForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
            PropTypeForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdTerm { rule, var }, fields)
            }
            PropTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdType { rule, var }, fields)
            }
            PropTypeForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaTerm { rule, var }, fields)
            }
            PropTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaType { rule, var }, fields)
            }
            PropTypeForm::AppTerm {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppTerm { rule }, fields)
            }
            PropTypeForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppType { rule }, fields)
            }
            PropTypeForm::Pred {
                superset,
                subset,
                element,
            } => {
                let fields = child_fields![superset => 0, subset => 0, element => 0];
                (Op::Pred, fields)
            }
            PropTypeForm::Equal { left, right } => {
                let fields = child_fields![left => 0, right => 0];
                (Op::Equal, fields)
            }
            PropTypeForm::Exists { set } => {
                let fields = child_fields![set => 0];
                (Op::Exists, fields)
            }
            PropTypeForm::Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, step => 0, state => 0];
                (Op::Acc, fields)
            }
            PropTypeForm::Recursor {
                rule,
                var,
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, motive => 1, on_continue => 0, on_finish => 0, scrutinee => 0];
                (Op::Recursor { rule, var }, fields)
            }
            PropTypeForm::IndType {
                inductive,
                parameters,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (Op::IndType { inductive }, fields)
            }
            PropTypeForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (
                    Op::IndCtor {
                        inductive,
                        constructor,
                    },
                    fields,
                )
            }
            PropTypeForm::IndElim {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                cases,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: scrutinee.into(),
                    }],
                    motive_domains
                        .into_iter()
                        .enumerate()
                        .map(|(_i, x)| Child {
                            depth: _i,
                            expression: x.into(),
                        })
                        .collect(),
                    vec![Child {
                        depth: motive_vars.len(),
                        expression: motive_body.into(),
                    }],
                    cases
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (
                    Op::IndElim {
                        inductive,
                        motive_vars,
                    },
                    fields,
                )
            }
        };
        arena
            .store(Family::PropType, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for PropType {
    type Node = PropTypeNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Bound { index } => PropTypeForm::Bound { index },
            Op::ModuleParam { parameter } => PropTypeForm::ModuleParam { parameter },
            Op::Constant { definition } => PropTypeForm::Constant { definition },
            Op::ProdTerm { rule, var } => PropTypeForm::ProdTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::ProdType { rule, var } => PropTypeForm::ProdType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::LambdaTerm { rule, var } => PropTypeForm::LambdaTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::LambdaType { rule, var } => PropTypeForm::LambdaType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::AppTerm { rule } => PropTypeForm::AppTerm {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::AppType { rule } => PropTypeForm::AppType {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::Pred => PropTypeForm::Pred {
                superset: data.child(0).try_into().expect("family"),
                subset: data.child(1).try_into().expect("family"),
                element: data.child(2).try_into().expect("family"),
            },
            Op::Equal => PropTypeForm::Equal {
                left: data.child(0).try_into().expect("family"),
                right: data.child(1).try_into().expect("family"),
            },
            Op::Exists => PropTypeForm::Exists {
                set: data.child(0).try_into().expect("family"),
            },
            Op::Acc => PropTypeForm::Acc {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                state: data.child(3).try_into().expect("family"),
            },
            Op::Recursor { rule, var } => PropTypeForm::Recursor {
                rule,
                var,
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                motive: data.child(2).try_into().expect("family"),
                on_continue: data.child(3).try_into().expect("family"),
                on_finish: data.child(4).try_into().expect("family"),
                scrutinee: data.child(5).try_into().expect("family"),
            },
            Op::IndType { inductive } => PropTypeForm::IndType {
                inductive,
                parameters: data
                    .children(0)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::IndCtor {
                inductive,
                constructor,
            } => PropTypeForm::IndCtor {
                inductive,
                constructor,
                parameters: data
                    .children(0)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::IndElim {
                inductive,
                motive_vars,
            } => PropTypeForm::IndElim {
                inductive,
                motive_vars,
                scrutinee: data.child(0).try_into().expect("family"),
                motive_domains: data
                    .children(1)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
                motive_body: data.child(2).try_into().expect("family"),
                cases: data
                    .children(3)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            _ => unreachable!("invalid arena partition"),
        };
        PropTypeNode { form }
    }
}

impl ArenaNode for PropKindNode {
    type Handle = PropKind;
    fn allocate(self, arena: &Arena) -> PropKind {
        let sort = BaseSort::Prop;
        let (op, fields) = match self.form {
            PropKindForm::Base => {
                let fields = vec![];
                (Op::Base, fields)
            }
            PropKindForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdTerm { rule, var }, fields)
            }
            PropKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdType { rule, var }, fields)
            }
            PropKindForm::IndType {
                inductive,
                parameters,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (Op::IndType { inductive }, fields)
            }
            PropKindForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            PropKindForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
        };
        arena
            .store(Family::PropKind, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for PropKind {
    type Node = PropKindNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Base => PropKindForm::Base,
            Op::ProdTerm { rule, var } => PropKindForm::ProdTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::ProdType { rule, var } => PropKindForm::ProdType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::IndType { inductive } => PropKindForm::IndType {
                inductive,
                parameters: data
                    .children(0)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::ModuleParam { parameter } => PropKindForm::ModuleParam { parameter },
            Op::Constant { definition } => PropKindForm::Constant { definition },
            _ => unreachable!("invalid arena partition"),
        };
        PropKindNode { form }
    }
}

impl ArenaNode for ValueTermNode {
    type Handle = ValueTerm;
    fn allocate(self, arena: &Arena) -> ValueTerm {
        let sort = BaseSort::Value(self.level);
        let (op, fields) = match self.form {
            ValueTermForm::Bound { index } => {
                let fields = vec![];
                (Op::Bound { index }, fields)
            }
            ValueTermForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            ValueTermForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
            ValueTermForm::ThunkValue { computation } => {
                let fields = child_fields![computation => 0];
                (Op::ThunkValue, fields)
            }
            ValueTermForm::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, next => 0];
                (Op::Continue, fields)
            }
            ValueTermForm::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, output => 0];
                (Op::Finish, fields)
            }
            ValueTermForm::InductiveConstructor {
                inductive,
                constructor,
                parameters,
                fields,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                    fields
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (
                    Op::InductiveConstructor {
                        inductive,
                        constructor,
                    },
                    fields,
                )
            }
        };
        arena
            .store(Family::ValueTerm, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for ValueTerm {
    type Node = ValueTermNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Bound { index } => ValueTermForm::Bound { index },
            Op::ModuleParam { parameter } => ValueTermForm::ModuleParam { parameter },
            Op::Constant { definition } => ValueTermForm::Constant { definition },
            Op::ThunkValue => ValueTermForm::ThunkValue {
                computation: data.child(0).try_into().expect("family"),
            },
            Op::Continue => ValueTermForm::Continue {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                next: data.child(2).try_into().expect("family"),
            },
            Op::Finish => ValueTermForm::Finish {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                output: data.child(2).try_into().expect("family"),
            },
            Op::InductiveConstructor {
                inductive,
                constructor,
            } => ValueTermForm::InductiveConstructor {
                inductive,
                constructor,
                parameters: data
                    .children(0)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
                fields: data
                    .children(1)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            _ => unreachable!("invalid arena partition"),
        };
        ValueTermNode {
            level: data.sort.level().expect("Program level"),
            form,
        }
    }
}

impl ArenaNode for ValueTypeNode {
    type Handle = ValueType;
    fn allocate(self, arena: &Arena) -> ValueType {
        let sort = BaseSort::Value(self.level);
        let (op, fields) = match self.form {
            ValueTypeForm::Bound { index } => {
                let fields = vec![];
                (Op::Bound { index }, fields)
            }
            ValueTypeForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            ValueTypeForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
            ValueTypeForm::Thunk { computation_ty } => {
                let fields = child_fields![computation_ty => 0];
                (Op::Thunk, fields)
            }
            ValueTypeForm::RunStep {
                state_ty,
                result_ty,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0];
                (Op::RunStep, fields)
            }
            ValueTypeForm::Inductive {
                inductive,
                parameters,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .map(|x| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (Op::Inductive { inductive }, fields)
            }
            ValueTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaType { rule, var }, fields)
            }
            ValueTypeForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppType { rule }, fields)
            }
        };
        arena
            .store(Family::ValueType, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for ValueType {
    type Node = ValueTypeNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Bound { index } => ValueTypeForm::Bound { index },
            Op::ModuleParam { parameter } => ValueTypeForm::ModuleParam { parameter },
            Op::Constant { definition } => ValueTypeForm::Constant { definition },
            Op::Thunk => ValueTypeForm::Thunk {
                computation_ty: data.child(0).try_into().expect("family"),
            },
            Op::RunStep => ValueTypeForm::RunStep {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
            },
            Op::Inductive { inductive } => ValueTypeForm::Inductive {
                inductive,
                parameters: data
                    .children(0)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::LambdaType { rule, var } => ValueTypeForm::LambdaType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::AppType { rule } => ValueTypeForm::AppType {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            _ => unreachable!("invalid arena partition"),
        };
        ValueTypeNode {
            level: data.sort.level().expect("Program level"),
            form,
        }
    }
}

impl ArenaNode for ValueKindNode {
    type Handle = ValueKind;
    fn allocate(self, arena: &Arena) -> ValueKind {
        let sort = BaseSort::Value(self.level);
        let (op, fields) = match self.form {
            ValueKindForm::Base => {
                let fields = vec![];
                (Op::Base, fields)
            }
            ValueKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdType { rule, var }, fields)
            }
        };
        arena
            .store(Family::ValueKind, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for ValueKind {
    type Node = ValueKindNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Base => ValueKindForm::Base,
            Op::ProdType { rule, var } => ValueKindForm::ProdType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            _ => unreachable!("invalid arena partition"),
        };
        ValueKindNode {
            level: data.sort.level().expect("Program level"),
            form,
        }
    }
}

impl ArenaNode for ComputationTermNode {
    type Handle = ComputationTerm;
    fn allocate(self, arena: &Arena) -> ComputationTerm {
        let sort = BaseSort::Computation(self.level);
        let (op, fields) = match self.form {
            ComputationTermForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            ComputationTermForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
            ComputationTermForm::Return { value } => {
                let fields = child_fields![value => 0];
                (Op::Return, fields)
            }
            ComputationTermForm::Force { value } => {
                let fields = child_fields![value => 0];
                (Op::Force, fields)
            }
            ComputationTermForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaTerm { rule, var }, fields)
            }
            ComputationTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaType { rule, var }, fields)
            }
            ComputationTermForm::AppTerm {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppTerm { rule }, fields)
            }
            ComputationTermForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppType { rule }, fields)
            }
            ComputationTermForm::Sequence {
                var,
                value_ty,
                computation,
                body,
            } => {
                let fields = child_fields![value_ty => 0, computation => 0, body => 1];
                (Op::Sequence { var }, fields)
            }
            ComputationTermForm::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                let fields = child_fields![value_ty => 0, value => 0, body => 1];
                (Op::ValueLet { var }, fields)
            }
            ComputationTermForm::Case {
                inductive,
                binders,
                result_ty,
                scrutinee,
                branches,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: scrutinee.into(),
                    }],
                    branches
                        .into_iter()
                        .enumerate()
                        .map(|(_i, x)| Child {
                            depth: binders[_i].len(),
                            expression: x.into(),
                        })
                        .collect(),
                ];
                (Op::Case { inductive, binders }, fields)
            }
            ComputationTermForm::Run {
                state_ty,
                result_ty,
                step,
                initial,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, step => 0, initial => 0];
                (Op::Run, fields)
            }
            ComputationTermForm::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => {
                let fields = child_fields![state_ty => 0, result_ty => 0, step => 0, initial => 0, transition => 0];
                (Op::RunCase, fields)
            }
        };
        arena
            .store(Family::ComputationTerm, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for ComputationTerm {
    type Node = ComputationTermNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::ModuleParam { parameter } => ComputationTermForm::ModuleParam { parameter },
            Op::Constant { definition } => ComputationTermForm::Constant { definition },
            Op::Return => ComputationTermForm::Return {
                value: data.child(0).try_into().expect("family"),
            },
            Op::Force => ComputationTermForm::Force {
                value: data.child(0).try_into().expect("family"),
            },
            Op::LambdaTerm { rule, var } => ComputationTermForm::LambdaTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::LambdaType { rule, var } => ComputationTermForm::LambdaType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::AppTerm { rule } => ComputationTermForm::AppTerm {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::AppType { rule } => ComputationTermForm::AppType {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::Sequence { var } => ComputationTermForm::Sequence {
                var,
                value_ty: data.child(0).try_into().expect("family"),
                computation: data.child(1).try_into().expect("family"),
                body: data.child(2).try_into().expect("family"),
            },
            Op::ValueLet { var } => ComputationTermForm::ValueLet {
                var,
                value_ty: data.child(0).try_into().expect("family"),
                value: data.child(1).try_into().expect("family"),
                body: data.child(2).try_into().expect("family"),
            },
            Op::Case { inductive, binders } => ComputationTermForm::Case {
                inductive,
                binders,
                result_ty: data.child(0).try_into().expect("family"),
                scrutinee: data.child(1).try_into().expect("family"),
                branches: data
                    .children(2)
                    .into_iter()
                    .map(|e| e.try_into().expect("family"))
                    .collect(),
            },
            Op::Run => ComputationTermForm::Run {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                initial: data.child(3).try_into().expect("family"),
            },
            Op::RunCase => ComputationTermForm::RunCase {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                initial: data.child(3).try_into().expect("family"),
                transition: data.child(4).try_into().expect("family"),
            },
            _ => unreachable!("invalid arena partition"),
        };
        ComputationTermNode {
            level: data.sort.level().expect("Program level"),
            form,
        }
    }
}

impl ArenaNode for ComputationTypeNode {
    type Handle = ComputationType;
    fn allocate(self, arena: &Arena) -> ComputationType {
        let sort = BaseSort::Computation(self.level);
        let (op, fields) = match self.form {
            ComputationTypeForm::Bound { index } => {
                let fields = vec![];
                (Op::Bound { index }, fields)
            }
            ComputationTypeForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            ComputationTypeForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
            ComputationTypeForm::ReturnType { value_ty } => {
                let fields = child_fields![value_ty => 0];
                (Op::ReturnType, fields)
            }
            ComputationTypeForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdTerm { rule, var }, fields)
            }
            ComputationTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdType { rule, var }, fields)
            }
            ComputationTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::LambdaType { rule, var }, fields)
            }
            ComputationTypeForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = child_fields![function => 0, argument => 0];
                (Op::AppType { rule }, fields)
            }
        };
        arena
            .store(Family::ComputationType, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for ComputationType {
    type Node = ComputationTypeNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Bound { index } => ComputationTypeForm::Bound { index },
            Op::ModuleParam { parameter } => ComputationTypeForm::ModuleParam { parameter },
            Op::Constant { definition } => ComputationTypeForm::Constant { definition },
            Op::ReturnType => ComputationTypeForm::ReturnType {
                value_ty: data.child(0).try_into().expect("family"),
            },
            Op::ProdTerm { rule, var } => ComputationTypeForm::ProdTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::ProdType { rule, var } => ComputationTypeForm::ProdType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::LambdaType { rule, var } => ComputationTypeForm::LambdaType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::AppType { rule } => ComputationTypeForm::AppType {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            _ => unreachable!("invalid arena partition"),
        };
        ComputationTypeNode {
            level: data.sort.level().expect("Program level"),
            form,
        }
    }
}

impl ArenaNode for ComputationKindNode {
    type Handle = ComputationKind;
    fn allocate(self, arena: &Arena) -> ComputationKind {
        let sort = BaseSort::Computation(self.level);
        let (op, fields) = match self.form {
            ComputationKindForm::Base => {
                let fields = vec![];
                (Op::Base, fields)
            }
            ComputationKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = child_fields![domain => 0, body => 1];
                (Op::ProdType { rule, var }, fields)
            }
        };
        arena
            .store(Family::ComputationKind, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}

impl ArenaHandle for ComputationKind {
    type Node = ComputationKindNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Base => ComputationKindForm::Base,
            Op::ProdType { rule, var } => ComputationKindForm::ProdType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            _ => unreachable!("invalid arena partition"),
        };
        ComputationKindNode {
            level: data.sort.level().expect("Program level"),
            form,
        }
    }
}
