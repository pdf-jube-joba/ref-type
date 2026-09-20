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
use hashconsing::{HConsed, HConsign, HashConsign};
use rustc_hash::FxBuildHasher;
use std::{
    cell::{Cell, RefCell},
    fmt,
    hash::{Hash, Hasher},
    ops::Deref,
};

struct Interned<N> {
    node: N,
    max_loose_bound: Cell<Option<Option<usize>>>,
}
impl<N: Clone> Clone for Interned<N> {
    fn clone(&self) -> Self {
        Self {
            node: self.node.clone(),
            max_loose_bound: Cell::new(self.max_loose_bound.get()),
        }
    }
}
impl<N: fmt::Debug> fmt::Debug for Interned<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.node.fmt(f)
    }
}
impl<N: PartialEq> PartialEq for Interned<N> {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}
impl<N: Eq> Eq for Interned<N> {}
impl<N: Hash> Hash for Interned<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.node.hash(state);
    }
}

/// Immutable, structurally interned nodes.
struct Partition<N: Clone + Eq + Hash> {
    consign: HConsign<Interned<N>, FxBuildHasher>,
}
impl<N: Clone + Eq + Hash> Default for Partition<N> {
    fn default() -> Self {
        Self {
            consign: HConsign::with_hasher(FxBuildHasher),
        }
    }
}
impl<N: Clone + Eq + Hash + fmt::Debug> fmt::Debug for Partition<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Partition").finish_non_exhaustive()
    }
}
impl<N: Clone + Eq + Hash> Partition<N> {
    fn insert(&mut self, node: N) -> HConsed<Interned<N>> {
        (&mut self.consign).mk(Interned {
            node,
            max_loose_bound: Cell::new(None),
        })
    }
}
// Keep every family in Set/Prop/Value/Computation order, then Term/Type/Kind.
// One table defines handles, family tags, conversions, and arena partitions.
macro_rules! syntax_families {
    ($($handle:ident => $storage:ident, $node:ident, $sort:pat, $stage:ident;)+) => {
        $(
            #[derive(Clone, PartialEq, Eq, Hash)]
            pub struct $handle(HConsed<Interned<$node>>);
            impl Deref for $handle {
                type Target = $node;
                fn deref(&self) -> &Self::Target { &self.0.node }
            }
            impl fmt::Debug for $handle {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    write!(f, "{}({})", stringify!($handle), self.0.uid())
                }
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
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub enum Expression { $($handle($handle),)+ }
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Family { $($handle,)+ }
        impl Expression {
            pub fn family(&self) -> Family {
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
            $($storage: RefCell<Partition<$node>>,)+
        }
        impl Arena {
            pub fn sort(&self, e: impl Into<Expression>) -> BaseSort {
                match e.into() { $(Expression::$handle(h) => h.sort(),)+ }
            }
            fn cached_max_loose_bound(&self, e: &Expression) -> Option<Option<usize>> {
                match e {
                    $(Expression::$handle(h) => h.0.max_loose_bound.get(),)+
                }
            }
            fn cache_max_loose_bound(&self, e: &Expression, value: Option<usize>) {
                match e {
                    $(Expression::$handle(h) => h.0.max_loose_bound.set(Some(value)),)+
                }
            }
            pub fn collect(&self) {
                $((&mut self.$storage.borrow_mut().consign).collect();)+
            }
        }
        $(impl ArenaNode for $node {
            type Handle = $handle;
            fn allocate(self, arena: &Arena) -> $handle {
                $handle(arena.$storage.borrow_mut().insert(self))
            }
        }
        impl ArenaHandle for $handle {
            type Node = $node;
            fn node(&self) -> &$node { self }
        })+

    };
}

// A classified subset of Expression with checked conversions in both directions.
macro_rules! expression_subset {
    ($name:ident, $error:literal; $($handle:ident),+ $(,)?) => {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

syntax_families! {
    SetTerm => setterm, SetTermNode, BaseSort::Set(_), Term;
    SetType => settype, SetTypeNode, BaseSort::Set(_), Type;
    SetKind => setkind, SetKindNode, BaseSort::Set(_), Kind;
    PropTerm => propterm, PropTermNode, BaseSort::Prop, Term;
    PropType => proptype, PropTypeNode, BaseSort::Prop, Type;
    PropKind => propkind, PropKindNode, BaseSort::Prop, Kind;
    ValueTerm => valueterm, ValueTermNode, BaseSort::Value(_), Term;
    ValueType => valuetype, ValueTypeNode, BaseSort::Value(_), Type;
    ValueKind => valuekind, ValueKindNode, BaseSort::Value(_), Kind;
    ComputationTerm => computationterm, ComputationTermNode, BaseSort::Computation(_), Term;
    ComputationType => computationtype, ComputationTypeNode, BaseSort::Computation(_), Type;
    ComputationKind => computationkind, ComputationKindNode, BaseSort::Computation(_), Kind;
}

impl<T> From<&T> for Expression
where
    T: Clone + Into<Expression>,
{
    fn from(value: &T) -> Self {
        value.clone().into()
    }
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
        if let Ok(e) = SetExpression::try_from(e.clone()) {
            Ok(Self::Set(e))
        } else {
            PropExpression::try_from(e).map(Self::Prop)
        }
    }
}

/// Set/Prop arguments used by mixed binders and inductive elimination.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
        if let Ok(e) = SetArgument::try_from(e.clone()) {
            Ok(Self::Set(e))
        } else {
            PropArgument::try_from(e).map(Self::Prop)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SetTermForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Annotated {
        body: SetTerm,
        classifier: super::environment::Classifier,
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
        program_ty: ComputationType,
        program: ComputationTerm,
    },
    ForceBox {
        program_ty: ComputationType,
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
    Case {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: LogicalArgument,
        motive_domains: Vec<LogicalExpression>,
        motive_body: LogicalExpression,
        branches: Vec<LogicalArgument>,
    },
    SetCase {
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
        result_ty: SetType,
        scrutinee: SetTerm,
        branches: Vec<SetTerm>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SetTermNode {
    pub level: usize,
    pub form: SetTermForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SetTypeForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Annotated {
        body: SetType,
        classifier: super::environment::Classifier,
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
        program_ty: ComputationType,
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
    Case {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: LogicalArgument,
        motive_domains: Vec<LogicalExpression>,
        motive_body: LogicalExpression,
        branches: Vec<LogicalArgument>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SetTypeNode {
    pub level: usize,
    pub form: SetTypeForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    Annotated {
        body: SetKind,
        classifier: super::environment::Classifier,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SetKindNode {
    pub level: usize,
    pub form: SetKindForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PropTermForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Annotated {
        body: PropTerm,
        classifier: super::environment::Classifier,
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
    Case {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: LogicalArgument,
        motive_domains: Vec<LogicalExpression>,
        motive_body: LogicalExpression,
        branches: Vec<LogicalArgument>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PropTermNode {
    pub form: PropTermForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PropTypeForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Annotated {
        body: PropType,
        classifier: super::environment::Classifier,
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
    Case {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: LogicalArgument,
        motive_domains: Vec<LogicalExpression>,
        motive_body: LogicalExpression,
        branches: Vec<LogicalArgument>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PropTypeNode {
    pub form: PropTypeForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    Annotated {
        body: PropKind,
        classifier: super::environment::Classifier,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PropKindNode {
    pub form: PropKindForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueTermForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Annotated {
        body: ValueTerm,
        classifier: super::environment::Classifier,
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValueTermNode {
    pub level: usize,
    pub form: ValueTermForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueTypeForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Annotated {
        body: ValueType,
        classifier: super::environment::Classifier,
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValueTypeNode {
    pub level: usize,
    pub form: ValueTypeForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueKindForm {
    Base,
    ProdType {
        rule: ProductRule,
        var: SymbolId,
        domain: ProgramKind,
        body: ValueKind,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ValueKindNode {
    pub level: usize,
    pub form: ValueKindForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ComputationTermForm {
    ModuleParam {
        parameter: ModuleParamId,
    },
    Annotated {
        body: ComputationTerm,
        classifier: super::environment::Classifier,
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
        accessibility: PropTerm,
    },
    RunCase {
        state_ty: ValueType,
        result_ty: ValueType,
        step: ValueTerm,
        initial: ValueTerm,
        transition: ComputationTerm,
        accessibility: PropTerm,
        transition_equality: PropTerm,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ComputationTermNode {
    pub level: usize,
    pub form: ComputationTermForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ComputationTypeForm {
    Bound {
        index: usize,
    },
    ModuleParam {
        parameter: ModuleParamId,
    },
    Annotated {
        body: ComputationType,
        classifier: super::environment::Classifier,
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ComputationTypeNode {
    pub level: usize,
    pub form: ComputationTypeForm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ComputationKindForm {
    Base,
    ProdType {
        rule: ProductRule,
        var: SymbolId,
        domain: ProgramKind,
        body: ComputationKind,
    },
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ComputationKindNode {
    pub level: usize,
    pub form: ComputationKindForm,
}

pub trait ArenaNode {
    type Handle;
    fn allocate(self, arena: &Arena) -> Self::Handle;
}
pub trait ArenaHandle: Clone {
    type Node: Clone;
    fn node(&self) -> &Self::Node;
}
impl Arena {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn alloc<N: ArenaNode>(&self, node: N) -> N::Handle {
        node.allocate(self)
    }
    pub fn get<H: ArenaHandle>(&self, handle: H) -> H::Node {
        handle.node().clone()
    }
    pub fn read<H: ArenaHandle>(&self, handle: H) -> H {
        handle
    }
    pub(crate) fn max_loose_bound(&self, e: Expression) -> Option<usize> {
        if let Some(cached) = self.cached_max_loose_bound(&e) {
            return cached;
        }
        let mut result = super::structure::bound_index(self, e.clone());
        super::structure::visit_children(self, e.clone(), |child, depth| {
            if let Some(index) = self
                .max_loose_bound(child)
                .and_then(|i| i.checked_sub(depth))
            {
                result = Some(result.map_or(index, |old| old.max(index)));
            }
        });
        self.cache_max_loose_bound(&e, result);
        result
    }
}
impl SetTermNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Set(self.level)
    }
}
impl SetTypeNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Set(self.level)
    }
}
impl SetKindNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Set(self.level)
    }
}
impl PropTermNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Prop
    }
}
impl PropTypeNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Prop
    }
}
impl PropKindNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Prop
    }
}
impl ValueTermNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Value(self.level)
    }
}
impl ValueTypeNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Value(self.level)
    }
}
impl ValueKindNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Value(self.level)
    }
}
impl ComputationTermNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Computation(self.level)
    }
}

impl Arena {
    /// A transparent body together with the classifier declared by its author.
    /// Allocation interns the whole annotation; no definition identity is involved.
    pub fn annotated(
        &self,
        body: Expression,
        classifier: super::environment::Classifier,
    ) -> Result<Expression, String> {
        Ok(match body {
            Expression::SetTerm(h) => self
                .alloc(SetTermNode {
                    level: self.read(h.clone()).level,
                    form: SetTermForm::Annotated {
                        body: h,
                        classifier,
                    },
                })
                .into(),
            Expression::SetType(h) => self
                .alloc(SetTypeNode {
                    level: self.read(h.clone()).level,
                    form: SetTypeForm::Annotated {
                        body: h,
                        classifier,
                    },
                })
                .into(),
            Expression::SetKind(h) => self
                .alloc(SetKindNode {
                    level: self.read(h.clone()).level,
                    form: SetKindForm::Annotated {
                        body: h,
                        classifier,
                    },
                })
                .into(),
            Expression::PropTerm(h) => self
                .alloc(PropTermNode {
                    form: PropTermForm::Annotated {
                        body: h,
                        classifier,
                    },
                })
                .into(),
            Expression::PropType(h) => self
                .alloc(PropTypeNode {
                    form: PropTypeForm::Annotated {
                        body: h,
                        classifier,
                    },
                })
                .into(),
            Expression::PropKind(h) => self
                .alloc(PropKindNode {
                    form: PropKindForm::Annotated {
                        body: h,
                        classifier,
                    },
                })
                .into(),
            Expression::ValueTerm(h) => self
                .alloc(ValueTermNode {
                    level: self.read(h.clone()).level,
                    form: ValueTermForm::Annotated {
                        body: h,
                        classifier,
                    },
                })
                .into(),
            Expression::ValueType(h) => self
                .alloc(ValueTypeNode {
                    level: self.read(h.clone()).level,
                    form: ValueTypeForm::Annotated {
                        body: h,
                        classifier,
                    },
                })
                .into(),
            Expression::ComputationTerm(h) => self
                .alloc(ComputationTermNode {
                    level: self.read(h.clone()).level,
                    form: ComputationTermForm::Annotated {
                        body: h,
                        classifier,
                    },
                })
                .into(),
            Expression::ComputationType(h) => self
                .alloc(ComputationTypeNode {
                    level: self.read(h.clone()).level,
                    form: ComputationTypeForm::Annotated {
                        body: h,
                        classifier,
                    },
                })
                .into(),
            _ => return Err("Program kinds cannot be annotated".into()),
        })
    }
}
impl ComputationTypeNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Computation(self.level)
    }
}
impl ComputationKindNode {
    pub fn sort(&self) -> BaseSort {
        BaseSort::Computation(self.level)
    }
}
