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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SetTerm(u32);
impl SetTerm {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SetType(u32);
impl SetType {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SetKind(u32);
impl SetKind {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ValueType(u32);
impl ValueType {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ComputationType(u32);
impl ComputationType {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ValueKind(u32);
impl ValueKind {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ComputationKind(u32);
impl ComputationKind {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ValueTerm(u32);
impl ValueTerm {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ComputationTerm(u32);
impl ComputationTerm {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SetExpression {
    SetTerm(SetTerm),
    SetType(SetType),
    SetKind(SetKind),
}
impl From<SetTerm> for SetExpression {
    fn from(h: SetTerm) -> Self {
        Self::SetTerm(h)
    }
}
impl From<SetType> for SetExpression {
    fn from(h: SetType) -> Self {
        Self::SetType(h)
    }
}
impl From<SetKind> for SetExpression {
    fn from(h: SetKind) -> Self {
        Self::SetKind(h)
    }
}
impl From<SetExpression> for Expression {
    fn from(e: SetExpression) -> Self {
        match e {
            SetExpression::SetTerm(h) => h.into(),
            SetExpression::SetType(h) => h.into(),
            SetExpression::SetKind(h) => h.into(),
        }
    }
}
impl TryFrom<Expression> for SetExpression {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        match e {
            Expression::SetTerm(h) => Ok(Self::SetTerm(h)),
            Expression::SetType(h) => Ok(Self::SetType(h)),
            Expression::SetKind(h) => Ok(Self::SetKind(h)),
            _ => Err("expected Set expression".into()),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PropExpression {
    PropTerm(PropTerm),
    PropType(PropType),
    PropKind(PropKind),
}
impl From<PropTerm> for PropExpression {
    fn from(h: PropTerm) -> Self {
        Self::PropTerm(h)
    }
}
impl From<PropType> for PropExpression {
    fn from(h: PropType) -> Self {
        Self::PropType(h)
    }
}
impl From<PropKind> for PropExpression {
    fn from(h: PropKind) -> Self {
        Self::PropKind(h)
    }
}
impl From<PropExpression> for Expression {
    fn from(e: PropExpression) -> Self {
        match e {
            PropExpression::PropTerm(h) => h.into(),
            PropExpression::PropType(h) => h.into(),
            PropExpression::PropKind(h) => h.into(),
        }
    }
}
impl TryFrom<Expression> for PropExpression {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        match e {
            Expression::PropTerm(h) => Ok(Self::PropTerm(h)),
            Expression::PropType(h) => Ok(Self::PropType(h)),
            Expression::PropKind(h) => Ok(Self::PropKind(h)),
            _ => Err("expected Prop expression".into()),
        }
    }
}
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SetArgument {
    SetTerm(SetTerm),
    SetType(SetType),
}
impl From<SetTerm> for SetArgument {
    fn from(h: SetTerm) -> Self {
        Self::SetTerm(h)
    }
}
impl From<SetType> for SetArgument {
    fn from(h: SetType) -> Self {
        Self::SetType(h)
    }
}
impl From<SetArgument> for Expression {
    fn from(e: SetArgument) -> Self {
        match e {
            SetArgument::SetTerm(h) => h.into(),
            SetArgument::SetType(h) => h.into(),
        }
    }
}
impl TryFrom<Expression> for SetArgument {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        match e {
            Expression::SetTerm(h) => Ok(Self::SetTerm(h)),
            Expression::SetType(h) => Ok(Self::SetType(h)),
            _ => Err("expected Set argument".into()),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PropArgument {
    PropTerm(PropTerm),
    PropType(PropType),
}
impl From<PropTerm> for PropArgument {
    fn from(h: PropTerm) -> Self {
        Self::PropTerm(h)
    }
}
impl From<PropType> for PropArgument {
    fn from(h: PropType) -> Self {
        Self::PropType(h)
    }
}
impl From<PropArgument> for Expression {
    fn from(e: PropArgument) -> Self {
        match e {
            PropArgument::PropTerm(h) => h.into(),
            PropArgument::PropType(h) => h.into(),
        }
    }
}
impl TryFrom<Expression> for PropArgument {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        match e {
            Expression::PropTerm(h) => Ok(Self::PropTerm(h)),
            Expression::PropType(h) => Ok(Self::PropType(h)),
            _ => Err("expected Prop argument".into()),
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProgramType {
    ValueType(ValueType),
    ComputationType(ComputationType),
}

impl From<ValueType> for ProgramType {
    fn from(x: ValueType) -> Self {
        Self::ValueType(x)
    }
}

impl From<ComputationType> for ProgramType {
    fn from(x: ComputationType) -> Self {
        Self::ComputationType(x)
    }
}

impl From<ProgramType> for Expression {
    fn from(x: ProgramType) -> Self {
        match x {
            ProgramType::ValueType(h) => Self::ValueType(h),
            ProgramType::ComputationType(h) => Self::ComputationType(h),
        }
    }
}

impl TryFrom<Expression> for ProgramType {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        match x {
            Expression::ValueType(h) => Ok(Self::ValueType(h)),
            Expression::ComputationType(h) => Ok(Self::ComputationType(h)),
            _ => Err("wrong syntax family".into()),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProgramKind {
    ValueKind(ValueKind),
    ComputationKind(ComputationKind),
}

impl From<ValueKind> for ProgramKind {
    fn from(x: ValueKind) -> Self {
        Self::ValueKind(x)
    }
}

impl From<ComputationKind> for ProgramKind {
    fn from(x: ComputationKind) -> Self {
        Self::ComputationKind(x)
    }
}

impl From<ProgramKind> for Expression {
    fn from(x: ProgramKind) -> Self {
        match x {
            ProgramKind::ValueKind(h) => Self::ValueKind(h),
            ProgramKind::ComputationKind(h) => Self::ComputationKind(h),
        }
    }
}

impl TryFrom<Expression> for ProgramKind {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        match x {
            Expression::ValueKind(h) => Ok(Self::ValueKind(h)),
            Expression::ComputationKind(h) => Ok(Self::ComputationKind(h)),
            _ => Err("wrong syntax family".into()),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProgramTerm {
    ValueTerm(ValueTerm),
    ComputationTerm(ComputationTerm),
}

impl From<ValueTerm> for ProgramTerm {
    fn from(x: ValueTerm) -> Self {
        Self::ValueTerm(x)
    }
}

impl From<ComputationTerm> for ProgramTerm {
    fn from(x: ComputationTerm) -> Self {
        Self::ComputationTerm(x)
    }
}

impl From<ProgramTerm> for Expression {
    fn from(x: ProgramTerm) -> Self {
        match x {
            ProgramTerm::ValueTerm(h) => Self::ValueTerm(h),
            ProgramTerm::ComputationTerm(h) => Self::ComputationTerm(h),
        }
    }
}

impl TryFrom<Expression> for ProgramTerm {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        match x {
            Expression::ValueTerm(h) => Ok(Self::ValueTerm(h)),
            Expression::ComputationTerm(h) => Ok(Self::ComputationTerm(h)),
            _ => Err("wrong syntax family".into()),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Expression {
    SetTerm(SetTerm),
    PropTerm(PropTerm),
    SetType(SetType),
    PropType(PropType),
    SetKind(SetKind),
    PropKind(PropKind),
    ValueType(ValueType),
    ComputationType(ComputationType),
    ValueKind(ValueKind),
    ComputationKind(ComputationKind),
    ValueTerm(ValueTerm),
    ComputationTerm(ComputationTerm),
}

impl From<SetTerm> for Expression {
    fn from(x: SetTerm) -> Self {
        Self::SetTerm(x)
    }
}
impl From<PropTerm> for Expression {
    fn from(x: PropTerm) -> Self {
        Self::PropTerm(x)
    }
}

impl From<SetType> for Expression {
    fn from(x: SetType) -> Self {
        Self::SetType(x)
    }
}
impl From<PropType> for Expression {
    fn from(x: PropType) -> Self {
        Self::PropType(x)
    }
}

impl From<SetKind> for Expression {
    fn from(x: SetKind) -> Self {
        Self::SetKind(x)
    }
}
impl From<PropKind> for Expression {
    fn from(x: PropKind) -> Self {
        Self::PropKind(x)
    }
}

impl From<ValueType> for Expression {
    fn from(x: ValueType) -> Self {
        Self::ValueType(x)
    }
}

impl From<ComputationType> for Expression {
    fn from(x: ComputationType) -> Self {
        Self::ComputationType(x)
    }
}

impl From<ValueKind> for Expression {
    fn from(x: ValueKind) -> Self {
        Self::ValueKind(x)
    }
}

impl From<ComputationKind> for Expression {
    fn from(x: ComputationKind) -> Self {
        Self::ComputationKind(x)
    }
}

impl From<ValueTerm> for Expression {
    fn from(x: ValueTerm) -> Self {
        Self::ValueTerm(x)
    }
}

impl From<ComputationTerm> for Expression {
    fn from(x: ComputationTerm) -> Self {
        Self::ComputationTerm(x)
    }
}

impl TryFrom<Expression> for SetTerm {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::SetTerm(h) = x {
            Ok(h)
        } else {
            Err("expected SetTerm".into())
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PropTerm(u32);
impl PropTerm {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
impl TryFrom<Expression> for PropTerm {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        if let Expression::PropTerm(h) = e {
            Ok(h)
        } else {
            Err("expected PropTerm".into())
        }
    }
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

impl TryFrom<Expression> for SetType {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::SetType(h) = x {
            Ok(h)
        } else {
            Err("expected SetType".into())
        }
    }
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PropType(u32);
impl PropType {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
impl TryFrom<Expression> for PropType {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        if let Expression::PropType(h) = e {
            Ok(h)
        } else {
            Err("expected PropType".into())
        }
    }
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

impl TryFrom<Expression> for SetKind {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::SetKind(h) = x {
            Ok(h)
        } else {
            Err("expected SetKind".into())
        }
    }
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PropKind(u32);
impl PropKind {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
impl TryFrom<Expression> for PropKind {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        if let Expression::PropKind(h) = e {
            Ok(h)
        } else {
            Err("expected PropKind".into())
        }
    }
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

impl TryFrom<Expression> for ValueType {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::ValueType(h) = x {
            Ok(h)
        } else {
            Err("expected ValueType".into())
        }
    }
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

impl TryFrom<Expression> for ComputationType {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::ComputationType(h) = x {
            Ok(h)
        } else {
            Err("expected ComputationType".into())
        }
    }
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

impl TryFrom<Expression> for ValueKind {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::ValueKind(h) = x {
            Ok(h)
        } else {
            Err("expected ValueKind".into())
        }
    }
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

impl TryFrom<Expression> for ComputationKind {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::ComputationKind(h) = x {
            Ok(h)
        } else {
            Err("expected ComputationKind".into())
        }
    }
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

impl TryFrom<Expression> for ValueTerm {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::ValueTerm(h) = x {
            Ok(h)
        } else {
            Err("expected ValueTerm".into())
        }
    }
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

impl TryFrom<Expression> for ComputationTerm {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::ComputationTerm(h) = x {
            Ok(h)
        } else {
            Err("expected ComputationTerm".into())
        }
    }
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
#[derive(Debug, Default)]
pub struct Arena {
    interner: RefCell<std::collections::HashMap<(Family, Data), Expression>>,
    loose_bound_cache: RefCell<std::collections::HashMap<Expression, Option<usize>>>,
    setterm: RefCell<Vec<Data>>,
    propterm: RefCell<Vec<Data>>,
    settype: RefCell<Vec<Data>>,
    proptype: RefCell<Vec<Data>>,
    setkind: RefCell<Vec<Data>>,
    propkind: RefCell<Vec<Data>>,
    valuetype: RefCell<Vec<Data>>,
    computationtype: RefCell<Vec<Data>>,
    valuekind: RefCell<Vec<Data>>,
    computationkind: RefCell<Vec<Data>>,
    valueterm: RefCell<Vec<Data>>,
    computationterm: RefCell<Vec<Data>>,
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

    pub fn sort(&self, e: impl Into<Expression>) -> BaseSort {
        match e.into() {
            Expression::SetTerm(h) => self.setterm.borrow()[h.index()].sort,
            Expression::PropTerm(h) => self.propterm.borrow()[h.index()].sort,
            Expression::SetType(h) => self.settype.borrow()[h.index()].sort,
            Expression::PropType(h) => self.proptype.borrow()[h.index()].sort,
            Expression::SetKind(h) => self.setkind.borrow()[h.index()].sort,
            Expression::PropKind(h) => self.propkind.borrow()[h.index()].sort,
            Expression::ValueType(h) => self.valuetype.borrow()[h.index()].sort,
            Expression::ComputationType(h) => self.computationtype.borrow()[h.index()].sort,
            Expression::ValueKind(h) => self.valuekind.borrow()[h.index()].sort,
            Expression::ComputationKind(h) => self.computationkind.borrow()[h.index()].sort,
            Expression::ValueTerm(h) => self.valueterm.borrow()[h.index()].sort,
            Expression::ComputationTerm(h) => self.computationterm.borrow()[h.index()].sort,
        }
    }

    pub(crate) fn data(&self, e: Expression) -> Data {
        match e {
            Expression::SetTerm(h) => self.setterm.borrow()[h.index()].clone(),
            Expression::PropTerm(h) => self.propterm.borrow()[h.index()].clone(),
            Expression::SetType(h) => self.settype.borrow()[h.index()].clone(),
            Expression::PropType(h) => self.proptype.borrow()[h.index()].clone(),
            Expression::SetKind(h) => self.setkind.borrow()[h.index()].clone(),
            Expression::PropKind(h) => self.propkind.borrow()[h.index()].clone(),
            Expression::ValueType(h) => self.valuetype.borrow()[h.index()].clone(),
            Expression::ComputationType(h) => self.computationtype.borrow()[h.index()].clone(),
            Expression::ValueKind(h) => self.valuekind.borrow()[h.index()].clone(),
            Expression::ComputationKind(h) => self.computationkind.borrow()[h.index()].clone(),
            Expression::ValueTerm(h) => self.valueterm.borrow()[h.index()].clone(),
            Expression::ComputationTerm(h) => self.computationterm.borrow()[h.index()].clone(),
        }
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

    pub(crate) fn store(&self, family: Family, data: Data) -> Expression {
        let key = (family, data.clone());
        if let Some(&e) = self.interner.borrow().get(&key) {
            return e;
        }
        let result = match family {
            Family::SetTerm => {
                let mut v = self.setterm.borrow_mut();
                let h = SetTerm(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::PropTerm => {
                let mut v = self.propterm.borrow_mut();
                let h = PropTerm(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::SetType => {
                let mut v = self.settype.borrow_mut();
                let h = SetType(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::PropType => {
                let mut v = self.proptype.borrow_mut();
                let h = PropType(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::SetKind => {
                let mut v = self.setkind.borrow_mut();
                let h = SetKind(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::PropKind => {
                let mut v = self.propkind.borrow_mut();
                let h = PropKind(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::ValueType => {
                let mut v = self.valuetype.borrow_mut();
                let h = ValueType(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::ComputationType => {
                let mut v = self.computationtype.borrow_mut();
                let h = ComputationType(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::ValueKind => {
                let mut v = self.valuekind.borrow_mut();
                let h = ValueKind(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::ComputationKind => {
                let mut v = self.computationkind.borrow_mut();
                let h = ComputationKind(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::ValueTerm => {
                let mut v = self.valueterm.borrow_mut();
                let h = ValueTerm(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::ComputationTerm => {
                let mut v = self.computationterm.borrow_mut();
                let h = ComputationTerm(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
        };
        self.interner.borrow_mut().insert(key, result);
        result
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Family {
    SetTerm,
    PropTerm,
    SetType,
    PropType,
    SetKind,
    PropKind,
    ValueType,
    ComputationType,
    ValueKind,
    ComputationKind,
    ValueTerm,
    ComputationTerm,
}

impl Expression {
    pub fn family(self) -> Family {
        match self {
            Self::SetTerm(..) => Family::SetTerm,
            Self::PropTerm(..) => Family::PropTerm,
            Self::SetType(..) => Family::SetType,
            Self::PropType(..) => Family::PropType,
            Self::SetKind(..) => Family::SetKind,
            Self::PropKind(..) => Family::PropKind,
            Self::ValueType(..) => Family::ValueType,
            Self::ComputationType(..) => Family::ComputationType,
            Self::ValueKind(..) => Family::ValueKind,
            Self::ComputationKind(..) => Family::ComputationKind,
            Self::ValueTerm(..) => Family::ValueTerm,
            Self::ComputationTerm(..) => Family::ComputationTerm,
        }
    }
}

impl Family {
    pub fn stage(self) -> Stage {
        match self {
            Self::SetTerm => Stage::Term,
            Self::PropTerm => Stage::Term,
            Self::SetType => Stage::Type,
            Self::PropType => Stage::Type,
            Self::SetKind => Stage::Kind,
            Self::PropKind => Stage::Kind,
            Self::ValueType => Stage::Type,
            Self::ComputationType => Stage::Type,
            Self::ValueKind => Stage::Kind,
            Self::ComputationKind => Stage::Kind,
            Self::ValueTerm => Stage::Term,
            Self::ComputationTerm => Stage::Term,
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Stage {
    Term,
    Type,
    Kind,
}

impl Family {
    pub fn at(sort: BaseSort, stage: Stage) -> Self {
        match (sort, stage) {
            (BaseSort::Set(_), Stage::Term) => Self::SetTerm,
            (BaseSort::Prop, Stage::Term) => Self::PropTerm,
            (BaseSort::Set(_), Stage::Type) => Self::SetType,
            (BaseSort::Prop, Stage::Type) => Self::PropType,
            (BaseSort::Set(_), Stage::Kind) => Self::SetKind,
            (BaseSort::Prop, Stage::Kind) => Self::PropKind,
            (BaseSort::Value(_), Stage::Term) => Self::ValueTerm,
            (BaseSort::Value(_), Stage::Type) => Self::ValueType,
            (BaseSort::Value(_), Stage::Kind) => Self::ValueKind,
            (BaseSort::Computation(_), Stage::Term) => Self::ComputationTerm,
            (BaseSort::Computation(_), Stage::Type) => Self::ComputationType,
            (BaseSort::Computation(_), Stage::Kind) => Self::ComputationKind,
        }
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaTerm { rule, var }, fields)
            }
            SetTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaType { rule, var }, fields)
            }
            SetTermForm::AppTerm {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
                (Op::AppTerm { rule }, fields)
            }
            SetTermForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
                (Op::AppType { rule }, fields)
            }
            SetTermForm::Subset {
                var,
                set,
                predicate,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: set.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: predicate.into(),
                    }],
                ];
                (Op::Subset { var }, fields)
            }
            SetTermForm::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: superset.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: subset.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: element.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: proof.into(),
                    }],
                ];
                (Op::SubsetIntro, fields)
            }
            SetTermForm::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: next.into(),
                    }],
                ];
                (Op::Continue, fields)
            }
            SetTermForm::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: output.into(),
                    }],
                ];
                (Op::Finish, fields)
            }
            SetTermForm::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: step.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: initial.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: accessibility.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: step.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: initial.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: transition.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: accessibility.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: transition_equality.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: motive.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: on_continue.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: on_finish.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: scrutinee.into(),
                    }],
                ];
                (Op::Recursor { rule, var }, fields)
            }
            SetTermForm::BoxProgram {
                program_ty,
                program,
                certified_reflection,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: program_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: program.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: certified_reflection.into(),
                    }],
                ];
                (Op::BoxProgram, fields)
            }
            SetTermForm::ForceBox { program_ty, boxed } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: program_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: boxed.into(),
                    }],
                ];
                (Op::ForceBox, fields)
            }
            SetTermForm::BoxApp {
                rule,
                domain,
                codomain,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: codomain.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: codomain.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
                (Op::BoxTypeApp { rule, var }, fields)
            }
            SetTermForm::TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: codomain.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: map.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: existence.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: uniqueness.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaTerm { rule, var }, fields)
            }
            PropTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaType { rule, var }, fields)
            }
            PropTermForm::AppTerm {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
                (Op::AppTerm { rule }, fields)
            }
            PropTermForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: motive.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: on_continue.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: on_finish.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: scrutinee.into(),
                    }],
                ];
                (Op::Recursor { rule, var }, fields)
            }
            PropTermForm::IdRefl { element } => {
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: element.into(),
                }]];
                (Op::IdRefl, fields)
            }
            PropTermForm::ExistsIntro { element, set } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: element.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: set.into(),
                    }],
                ];
                (Op::ExistsIntro, fields)
            }
            PropTermForm::SubsetElim {
                element,
                subset,
                superset,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: element.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: subset.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: superset.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: left.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: right.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: ty.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: predicate.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: base.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: equality.into(),
                    }],
                ];
                (Op::IdElim { var }, fields)
            }
            PropTermForm::TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: proposition.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: map.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: existence.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: func.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: codomain.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: element.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: existence.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: uniqueness.into(),
                    }],
                ];
                (Op::TakeEq, fields)
            }
            PropTermForm::SetExt {
                left,
                right,
                left_to_right,
                right_to_left,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: left.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: right.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: left_to_right.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: right_to_left.into(),
                    }],
                ];
                (Op::SetExt, fields)
            }
            PropTermForm::FunExt {
                left,
                right,
                pointwise,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: left.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: right.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: pointwise.into(),
                    }],
                ];
                (Op::FunExt, fields)
            }
            PropTermForm::ClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: family.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: inhabited.into(),
                    }],
                ];
                (Op::ClassicalIndefiniteChoice, fields)
            }
            PropTermForm::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: step.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: state.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: predecessors.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: step.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: from.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: to.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: accessibility.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: transition.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::ProdTerm { rule, var }, fields)
            }
            SetTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::ProdType { rule, var }, fields)
            }
            SetTypeForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaTerm { rule, var }, fields)
            }
            SetTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaType { rule, var }, fields)
            }
            SetTypeForm::AppTerm {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
                (Op::AppTerm { rule }, fields)
            }
            SetTypeForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
                (Op::AppType { rule }, fields)
            }
            SetTypeForm::PowerSet { set } => {
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: set.into(),
                }]];
                (Op::PowerSet, fields)
            }
            SetTypeForm::TypeLift { superset, subset } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: superset.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: subset.into(),
                    }],
                ];
                (Op::TypeLift, fields)
            }
            SetTypeForm::RunStep {
                state_ty,
                result_ty,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                ];
                (Op::RunStep, fields)
            }
            SetTypeForm::BoxType { program_ty } => {
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: program_ty.into(),
                }]];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: motive.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: on_continue.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: on_finish.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: scrutinee.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::ProdTerm { rule, var }, fields)
            }
            PropTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::ProdType { rule, var }, fields)
            }
            PropTypeForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaTerm { rule, var }, fields)
            }
            PropTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaType { rule, var }, fields)
            }
            PropTypeForm::AppTerm {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
                (Op::AppTerm { rule }, fields)
            }
            PropTypeForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
                (Op::AppType { rule }, fields)
            }
            PropTypeForm::Pred {
                superset,
                subset,
                element,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: superset.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: subset.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: element.into(),
                    }],
                ];
                (Op::Pred, fields)
            }
            PropTypeForm::Equal { left, right } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: left.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: right.into(),
                    }],
                ];
                (Op::Equal, fields)
            }
            PropTypeForm::Exists { set } => {
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: set.into(),
                }]];
                (Op::Exists, fields)
            }
            PropTypeForm::Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: step.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: state.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: motive.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: on_continue.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: on_finish.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: scrutinee.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::ProdTerm { rule, var }, fields)
            }
            SetKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::ProdTerm { rule, var }, fields)
            }
            PropKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
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
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: computation_ty.into(),
                }]];
                (Op::Thunk, fields)
            }
            ValueTypeForm::RunStep {
                state_ty,
                result_ty,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaType { rule, var }, fields)
            }
            ValueTypeForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
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
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: value_ty.into(),
                }]];
                (Op::ReturnType, fields)
            }
            ComputationTypeForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::ProdTerm { rule, var }, fields)
            }
            ComputationTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::ProdType { rule, var }, fields)
            }
            ComputationTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaType { rule, var }, fields)
            }
            ComputationTypeForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
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
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: computation.into(),
                }]];
                (Op::ThunkValue, fields)
            }
            ValueTermForm::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: next.into(),
                    }],
                ];
                (Op::Continue, fields)
            }
            ValueTermForm::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: output.into(),
                    }],
                ];
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
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: value.into(),
                }]];
                (Op::Return, fields)
            }
            ComputationTermForm::Force { value } => {
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: value.into(),
                }]];
                (Op::Force, fields)
            }
            ComputationTermForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaTerm { rule, var }, fields)
            }
            ComputationTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: domain.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::LambdaType { rule, var }, fields)
            }
            ComputationTermForm::AppTerm {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
                (Op::AppTerm { rule }, fields)
            }
            ComputationTermForm::AppType {
                rule,
                function,
                argument,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: function.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: argument.into(),
                    }],
                ];
                (Op::AppType { rule }, fields)
            }
            ComputationTermForm::Sequence {
                var,
                value_ty,
                computation,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: value_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: computation.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
                (Op::Sequence { var }, fields)
            }
            ComputationTermForm::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: value_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: value.into(),
                    }],
                    vec![Child {
                        depth: 1,
                        expression: body.into(),
                    }],
                ];
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
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: step.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: initial.into(),
                    }],
                ];
                (Op::Run, fields)
            }
            ComputationTermForm::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
            } => {
                let fields = vec![
                    vec![Child {
                        depth: 0,
                        expression: state_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: result_ty.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: step.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: initial.into(),
                    }],
                    vec![Child {
                        depth: 0,
                        expression: transition.into(),
                    }],
                ];
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicalTerm {
    SetTerm(SetTerm),
    PropTerm(PropTerm),
}
impl From<SetTerm> for LogicalTerm {
    fn from(h: SetTerm) -> Self {
        Self::SetTerm(h)
    }
}
impl From<PropTerm> for LogicalTerm {
    fn from(h: PropTerm) -> Self {
        Self::PropTerm(h)
    }
}
impl From<LogicalTerm> for Expression {
    fn from(h: LogicalTerm) -> Self {
        match h {
            LogicalTerm::SetTerm(h) => h.into(),
            LogicalTerm::PropTerm(h) => h.into(),
        }
    }
}
impl TryFrom<Expression> for LogicalTerm {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        match e {
            Expression::SetTerm(h) => Ok(Self::SetTerm(h)),
            Expression::PropTerm(h) => Ok(Self::PropTerm(h)),
            _ => Err("expected Set/Prop term".into()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicalType {
    SetType(SetType),
    PropType(PropType),
}
impl From<SetType> for LogicalType {
    fn from(h: SetType) -> Self {
        Self::SetType(h)
    }
}
impl From<PropType> for LogicalType {
    fn from(h: PropType) -> Self {
        Self::PropType(h)
    }
}
impl From<LogicalType> for Expression {
    fn from(h: LogicalType) -> Self {
        match h {
            LogicalType::SetType(h) => h.into(),
            LogicalType::PropType(h) => h.into(),
        }
    }
}
impl TryFrom<Expression> for LogicalType {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        match e {
            Expression::SetType(h) => Ok(Self::SetType(h)),
            Expression::PropType(h) => Ok(Self::PropType(h)),
            _ => Err("expected Set/Prop type".into()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogicalKind {
    SetKind(SetKind),
    PropKind(PropKind),
}
impl From<SetKind> for LogicalKind {
    fn from(h: SetKind) -> Self {
        Self::SetKind(h)
    }
}
impl From<PropKind> for LogicalKind {
    fn from(h: PropKind) -> Self {
        Self::PropKind(h)
    }
}
impl From<LogicalKind> for Expression {
    fn from(h: LogicalKind) -> Self {
        match h {
            LogicalKind::SetKind(h) => h.into(),
            LogicalKind::PropKind(h) => h.into(),
        }
    }
}
impl TryFrom<Expression> for LogicalKind {
    type Error = String;
    fn try_from(e: Expression) -> Result<Self, String> {
        match e {
            Expression::SetKind(h) => Ok(Self::SetKind(h)),
            Expression::PropKind(h) => Ok(Self::PropKind(h)),
            _ => Err("expected Set/Prop kind".into()),
        }
    }
}
