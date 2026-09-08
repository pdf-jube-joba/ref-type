//! Sort-indexed syntax. A handle fixes the syntactic family; nodes carry its index.
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
pub struct Value(u32);
impl Value {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Computation(u32);
impl Computation {
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
    fn from(x: SetTerm) -> Self {
        Self::SetTerm(x)
    }
}
impl From<SetType> for SetExpression {
    fn from(x: SetType) -> Self {
        Self::SetType(x)
    }
}
impl From<SetKind> for SetExpression {
    fn from(x: SetKind) -> Self {
        Self::SetKind(x)
    }
}
impl From<SetExpression> for Expression {
    fn from(x: SetExpression) -> Self {
        match x {
            SetExpression::SetTerm(h) => Self::SetTerm(h),
            SetExpression::SetType(h) => Self::SetType(h),
            SetExpression::SetKind(h) => Self::SetKind(h),
        }
    }
}
impl TryFrom<Expression> for SetExpression {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        match x {
            Expression::SetTerm(h) => Ok(Self::SetTerm(h)),
            Expression::SetType(h) => Ok(Self::SetType(h)),
            Expression::SetKind(h) => Ok(Self::SetKind(h)),
            _ => Err("wrong syntax family".into()),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SetArgument {
    SetTerm(SetTerm),
    SetType(SetType),
}
impl From<SetTerm> for SetArgument {
    fn from(x: SetTerm) -> Self {
        Self::SetTerm(x)
    }
}
impl From<SetType> for SetArgument {
    fn from(x: SetType) -> Self {
        Self::SetType(x)
    }
}
impl From<SetArgument> for Expression {
    fn from(x: SetArgument) -> Self {
        match x {
            SetArgument::SetTerm(h) => Self::SetTerm(h),
            SetArgument::SetType(h) => Self::SetType(h),
        }
    }
}
impl TryFrom<Expression> for SetArgument {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        match x {
            Expression::SetTerm(h) => Ok(Self::SetTerm(h)),
            Expression::SetType(h) => Ok(Self::SetType(h)),
            _ => Err("wrong syntax family".into()),
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
pub enum Program {
    Value(Value),
    Computation(Computation),
}
impl From<Value> for Program {
    fn from(x: Value) -> Self {
        Self::Value(x)
    }
}
impl From<Computation> for Program {
    fn from(x: Computation) -> Self {
        Self::Computation(x)
    }
}
impl From<Program> for Expression {
    fn from(x: Program) -> Self {
        match x {
            Program::Value(h) => Self::Value(h),
            Program::Computation(h) => Self::Computation(h),
        }
    }
}
impl TryFrom<Expression> for Program {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        match x {
            Expression::Value(h) => Ok(Self::Value(h)),
            Expression::Computation(h) => Ok(Self::Computation(h)),
            _ => Err("wrong syntax family".into()),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Expression {
    SetTerm(SetTerm),
    SetType(SetType),
    SetKind(SetKind),
    ValueType(ValueType),
    ComputationType(ComputationType),
    ValueKind(ValueKind),
    ComputationKind(ComputationKind),
    Value(Value),
    Computation(Computation),
}
impl From<SetTerm> for Expression {
    fn from(x: SetTerm) -> Self {
        Self::SetTerm(x)
    }
}
impl From<SetType> for Expression {
    fn from(x: SetType) -> Self {
        Self::SetType(x)
    }
}
impl From<SetKind> for Expression {
    fn from(x: SetKind) -> Self {
        Self::SetKind(x)
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
impl From<Value> for Expression {
    fn from(x: Value) -> Self {
        Self::Value(x)
    }
}
impl From<Computation> for Expression {
    fn from(x: Computation) -> Self {
        Self::Computation(x)
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
        predicate: SetType,
    },
    SubsetIntro {
        superset: SetType,
        subset: SetTerm,
        element: SetTerm,
        proof: SetTerm,
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
        accessibility: SetTerm,
    },
    SetRunCase {
        state_ty: SetType,
        result_ty: SetType,
        step: SetTerm,
        initial: SetTerm,
        transition: SetTerm,
        accessibility: SetTerm,
        transition_equality: SetTerm,
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
        program: Program,
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
        predicate: SetType,
        base: SetTerm,
        equality: SetTerm,
    },
    TakeSet {
        domain: SetType,
        codomain: SetType,
        map: SetTerm,
        existence: SetTerm,
        uniqueness: SetTerm,
    },
    TakeProp {
        domain: SetType,
        proposition: SetType,
        map: SetTerm,
        existence: SetTerm,
    },
    TakeEq {
        func: SetTerm,
        domain: SetType,
        codomain: SetType,
        element: SetTerm,
        existence: SetTerm,
        uniqueness: SetTerm,
    },
    SetExt {
        left: SetTerm,
        right: SetTerm,
        left_to_right: SetTerm,
        right_to_left: SetTerm,
    },
    FunExt {
        left: SetTerm,
        right: SetTerm,
        pointwise: SetTerm,
    },
    ClassicalIndefiniteChoice {
        domain: SetType,
        family: SetType,
        inhabited: SetTerm,
    },
    AccIntro {
        state_ty: SetType,
        result_ty: SetType,
        step: SetTerm,
        state: SetTerm,
        predecessors: SetTerm,
    },
    AccDescent {
        state_ty: SetType,
        result_ty: SetType,
        step: SetTerm,
        from: SetTerm,
        to: SetTerm,
        accessibility: SetTerm,
        transition: SetTerm,
    },
    IndCtor {
        inductive: InductiveId,
        constructor: usize,
        parameters: Vec<SetArgument>,
    },
    IndElim {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: SetArgument,
        motive_domains: Vec<SetExpression>,
        motive_body: SetExpression,
        cases: Vec<SetArgument>,
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
    pub sort: SetSort,
    pub form: SetTermForm,
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
    RunStep {
        state_ty: SetType,
        result_ty: SetType,
    },
    Acc {
        state_ty: SetType,
        result_ty: SetType,
        step: SetTerm,
        state: SetTerm,
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
        parameters: Vec<SetArgument>,
    },
    IndCtor {
        inductive: InductiveId,
        constructor: usize,
        parameters: Vec<SetArgument>,
    },
    IndElim {
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: SetArgument,
        motive_domains: Vec<SetExpression>,
        motive_body: SetExpression,
        cases: Vec<SetArgument>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetTypeNode {
    pub sort: SetSort,
    pub form: SetTypeForm,
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
        parameters: Vec<SetArgument>,
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
    pub sort: SetSort,
    pub form: SetKindForm,
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
impl TryFrom<Expression> for Value {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::Value(h) = x {
            Ok(h)
        } else {
            Err("expected Value".into())
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueForm {
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
        computation: Computation,
    },
    Continue {
        state_ty: ValueType,
        result_ty: ValueType,
        next: Value,
    },
    Finish {
        state_ty: ValueType,
        result_ty: ValueType,
        output: Value,
    },
    InductiveConstructor {
        inductive: ProgramInductiveId,
        constructor: usize,
        parameters: Vec<ProgramType>,
        fields: Vec<Value>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueNode {
    pub level: usize,
    pub form: ValueForm,
}
impl TryFrom<Expression> for Computation {
    type Error = String;
    fn try_from(x: Expression) -> Result<Self, String> {
        if let Expression::Computation(h) = x {
            Ok(h)
        } else {
            Err("expected Computation".into())
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComputationForm {
    ModuleParam {
        parameter: ModuleParamId,
    },
    Constant {
        definition: DefId,
    },
    Return {
        value: Value,
    },
    Force {
        value: Value,
    },
    LambdaTerm {
        rule: ProductRule,
        var: SymbolId,
        domain: ValueType,
        body: Computation,
    },
    LambdaType {
        rule: ProductRule,
        var: SymbolId,
        domain: ProgramKind,
        body: Computation,
    },
    AppTerm {
        rule: ProductRule,
        function: Computation,
        argument: Value,
    },
    AppType {
        rule: ProductRule,
        function: Computation,
        argument: ProgramType,
    },
    Sequence {
        var: SymbolId,
        value_ty: ValueType,
        computation: Computation,
        body: Computation,
    },
    ValueLet {
        var: SymbolId,
        value_ty: ValueType,
        value: Value,
        body: Computation,
    },
    Case {
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
        result_ty: ComputationType,
        scrutinee: Value,
        branches: Vec<Computation>,
    },
    Run {
        state_ty: ValueType,
        result_ty: ValueType,
        step: Value,
        initial: Value,
    },
    RunCase {
        state_ty: ValueType,
        result_ty: ValueType,
        step: Value,
        initial: Value,
        transition: Computation,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputationNode {
    pub level: usize,
    pub form: ComputationForm,
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
    setterm: RefCell<Vec<Data>>,
    settype: RefCell<Vec<Data>>,
    setkind: RefCell<Vec<Data>>,
    valuetype: RefCell<Vec<Data>>,
    computationtype: RefCell<Vec<Data>>,
    valuekind: RefCell<Vec<Data>>,
    computationkind: RefCell<Vec<Data>>,
    value: RefCell<Vec<Data>>,
    computation: RefCell<Vec<Data>>,
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
        self.data(e.into()).sort
    }
    pub(crate) fn data(&self, e: Expression) -> Data {
        match e {
            Expression::SetTerm(h) => self.setterm.borrow()[h.index()].clone(),
            Expression::SetType(h) => self.settype.borrow()[h.index()].clone(),
            Expression::SetKind(h) => self.setkind.borrow()[h.index()].clone(),
            Expression::ValueType(h) => self.valuetype.borrow()[h.index()].clone(),
            Expression::ComputationType(h) => self.computationtype.borrow()[h.index()].clone(),
            Expression::ValueKind(h) => self.valuekind.borrow()[h.index()].clone(),
            Expression::ComputationKind(h) => self.computationkind.borrow()[h.index()].clone(),
            Expression::Value(h) => self.value.borrow()[h.index()].clone(),
            Expression::Computation(h) => self.computation.borrow()[h.index()].clone(),
        }
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
            Family::SetType => {
                let mut v = self.settype.borrow_mut();
                let h = SetType(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::SetKind => {
                let mut v = self.setkind.borrow_mut();
                let h = SetKind(u32::try_from(v.len()).expect("arena exhausted"));
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
            Family::Value => {
                let mut v = self.value.borrow_mut();
                let h = Value(u32::try_from(v.len()).expect("arena exhausted"));
                v.push(data);
                h.into()
            }
            Family::Computation => {
                let mut v = self.computation.borrow_mut();
                let h = Computation(u32::try_from(v.len()).expect("arena exhausted"));
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
    SetType,
    SetKind,
    ValueType,
    ComputationType,
    ValueKind,
    ComputationKind,
    Value,
    Computation,
}
impl Expression {
    pub fn family(self) -> Family {
        match self {
            Self::SetTerm(..) => Family::SetTerm,
            Self::SetType(..) => Family::SetType,
            Self::SetKind(..) => Family::SetKind,
            Self::ValueType(..) => Family::ValueType,
            Self::ComputationType(..) => Family::ComputationType,
            Self::ValueKind(..) => Family::ValueKind,
            Self::ComputationKind(..) => Family::ComputationKind,
            Self::Value(..) => Family::Value,
            Self::Computation(..) => Family::Computation,
        }
    }
}
impl Family {
    pub fn stage(self) -> Stage {
        match self {
            Self::SetTerm => Stage::Term,
            Self::SetType => Stage::Type,
            Self::SetKind => Stage::Kind,
            Self::ValueType => Stage::Type,
            Self::ComputationType => Stage::Type,
            Self::ValueKind => Stage::Kind,
            Self::ComputationKind => Stage::Kind,
            Self::Value => Stage::Term,
            Self::Computation => Stage::Term,
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
            (BaseSort::Set(_) | BaseSort::Prop, Stage::Term) => Self::SetTerm,
            (BaseSort::Set(_) | BaseSort::Prop, Stage::Type) => Self::SetType,
            (BaseSort::Set(_) | BaseSort::Prop, Stage::Kind) => Self::SetKind,
            (BaseSort::Value(_), Stage::Term) => Self::Value,
            (BaseSort::Value(_), Stage::Type) => Self::ValueType,
            (BaseSort::Value(_), Stage::Kind) => Self::ValueKind,
            (BaseSort::Computation(_), Stage::Term) => Self::Computation,
            (BaseSort::Computation(_), Stage::Type) => Self::ComputationType,
            (BaseSort::Computation(_), Stage::Kind) => Self::ComputationKind,
        }
    }
}
impl ArenaNode for SetTermNode {
    type Handle = SetTerm;
    fn allocate(self, arena: &Arena) -> SetTerm {
        let sort = self.sort.into();
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
            SetTermForm::IdRefl { element } => {
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: element.into(),
                }]];
                (Op::IdRefl, fields)
            }
            SetTermForm::ExistsIntro { element, set } => {
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
            SetTermForm::SubsetElim {
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
            SetTermForm::IdElim {
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
            SetTermForm::TakeProp {
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
            SetTermForm::TakeEq {
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
            SetTermForm::SetExt {
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
            SetTermForm::FunExt {
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
            SetTermForm::ClassicalIndefiniteChoice {
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
            SetTermForm::AccIntro {
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
            SetTermForm::AccDescent {
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
            SetTermForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .enumerate()
                        .map(|(_i, x)| Child {
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
                        .enumerate()
                        .map(|(_i, x)| Child {
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
            Op::IdRefl => SetTermForm::IdRefl {
                element: data.child(0).try_into().expect("family"),
            },
            Op::ExistsIntro => SetTermForm::ExistsIntro {
                element: data.child(0).try_into().expect("family"),
                set: data.child(1).try_into().expect("family"),
            },
            Op::SubsetElim => SetTermForm::SubsetElim {
                element: data.child(0).try_into().expect("family"),
                subset: data.child(1).try_into().expect("family"),
                superset: data.child(2).try_into().expect("family"),
            },
            Op::IdElim { var } => SetTermForm::IdElim {
                var,
                left: data.child(0).try_into().expect("family"),
                right: data.child(1).try_into().expect("family"),
                ty: data.child(2).try_into().expect("family"),
                predicate: data.child(3).try_into().expect("family"),
                base: data.child(4).try_into().expect("family"),
                equality: data.child(5).try_into().expect("family"),
            },
            Op::TakeSet => SetTermForm::TakeSet {
                domain: data.child(0).try_into().expect("family"),
                codomain: data.child(1).try_into().expect("family"),
                map: data.child(2).try_into().expect("family"),
                existence: data.child(3).try_into().expect("family"),
                uniqueness: data.child(4).try_into().expect("family"),
            },
            Op::TakeProp => SetTermForm::TakeProp {
                domain: data.child(0).try_into().expect("family"),
                proposition: data.child(1).try_into().expect("family"),
                map: data.child(2).try_into().expect("family"),
                existence: data.child(3).try_into().expect("family"),
            },
            Op::TakeEq => SetTermForm::TakeEq {
                func: data.child(0).try_into().expect("family"),
                domain: data.child(1).try_into().expect("family"),
                codomain: data.child(2).try_into().expect("family"),
                element: data.child(3).try_into().expect("family"),
                existence: data.child(4).try_into().expect("family"),
                uniqueness: data.child(5).try_into().expect("family"),
            },
            Op::SetExt => SetTermForm::SetExt {
                left: data.child(0).try_into().expect("family"),
                right: data.child(1).try_into().expect("family"),
                left_to_right: data.child(2).try_into().expect("family"),
                right_to_left: data.child(3).try_into().expect("family"),
            },
            Op::FunExt => SetTermForm::FunExt {
                left: data.child(0).try_into().expect("family"),
                right: data.child(1).try_into().expect("family"),
                pointwise: data.child(2).try_into().expect("family"),
            },
            Op::ClassicalIndefiniteChoice => SetTermForm::ClassicalIndefiniteChoice {
                domain: data.child(0).try_into().expect("family"),
                family: data.child(1).try_into().expect("family"),
                inhabited: data.child(2).try_into().expect("family"),
            },
            Op::AccIntro => SetTermForm::AccIntro {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                state: data.child(3).try_into().expect("family"),
                predecessors: data.child(4).try_into().expect("family"),
            },
            Op::AccDescent => SetTermForm::AccDescent {
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
            sort: data.sort.try_into().expect("Set/Prop index"),
            form,
        }
    }
}
impl ArenaNode for SetTypeNode {
    type Handle = SetType;
    fn allocate(self, arena: &Arena) -> SetType {
        let sort = self.sort.into();
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
            SetTypeForm::Pred {
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
            SetTypeForm::Equal { left, right } => {
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
            SetTypeForm::Exists { set } => {
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: set.into(),
                }]];
                (Op::Exists, fields)
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
            SetTypeForm::Acc {
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
                        .enumerate()
                        .map(|(_i, x)| Child {
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
                        .enumerate()
                        .map(|(_i, x)| Child {
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
                        .enumerate()
                        .map(|(_i, x)| Child {
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
            Op::Pred => SetTypeForm::Pred {
                superset: data.child(0).try_into().expect("family"),
                subset: data.child(1).try_into().expect("family"),
                element: data.child(2).try_into().expect("family"),
            },
            Op::Equal => SetTypeForm::Equal {
                left: data.child(0).try_into().expect("family"),
                right: data.child(1).try_into().expect("family"),
            },
            Op::Exists => SetTypeForm::Exists {
                set: data.child(0).try_into().expect("family"),
            },
            Op::RunStep => SetTypeForm::RunStep {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
            },
            Op::Acc => SetTypeForm::Acc {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                state: data.child(3).try_into().expect("family"),
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
            sort: data.sort.try_into().expect("Set/Prop index"),
            form,
        }
    }
}
impl ArenaNode for SetKindNode {
    type Handle = SetKind;
    fn allocate(self, arena: &Arena) -> SetKind {
        let sort = self.sort.into();
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
                        .enumerate()
                        .map(|(_i, x)| Child {
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
            sort: data.sort.try_into().expect("Set/Prop index"),
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
                        .enumerate()
                        .map(|(_i, x)| Child {
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
impl ArenaNode for ValueNode {
    type Handle = Value;
    fn allocate(self, arena: &Arena) -> Value {
        let sort = BaseSort::Value(self.level);
        let (op, fields) = match self.form {
            ValueForm::Bound { index } => {
                let fields = vec![];
                (Op::Bound { index }, fields)
            }
            ValueForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            ValueForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
            ValueForm::ThunkValue { computation } => {
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: computation.into(),
                }]];
                (Op::ThunkValue, fields)
            }
            ValueForm::Continue {
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
            ValueForm::Finish {
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
            ValueForm::InductiveConstructor {
                inductive,
                constructor,
                parameters,
                fields,
            } => {
                let fields = vec![
                    parameters
                        .into_iter()
                        .enumerate()
                        .map(|(_i, x)| Child {
                            depth: 0,
                            expression: x.into(),
                        })
                        .collect(),
                    fields
                        .into_iter()
                        .enumerate()
                        .map(|(_i, x)| Child {
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
            .store(Family::Value, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}
impl ArenaHandle for Value {
    type Node = ValueNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::Bound { index } => ValueForm::Bound { index },
            Op::ModuleParam { parameter } => ValueForm::ModuleParam { parameter },
            Op::Constant { definition } => ValueForm::Constant { definition },
            Op::ThunkValue => ValueForm::ThunkValue {
                computation: data.child(0).try_into().expect("family"),
            },
            Op::Continue => ValueForm::Continue {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                next: data.child(2).try_into().expect("family"),
            },
            Op::Finish => ValueForm::Finish {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                output: data.child(2).try_into().expect("family"),
            },
            Op::InductiveConstructor {
                inductive,
                constructor,
            } => ValueForm::InductiveConstructor {
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
        ValueNode {
            level: data.sort.level().expect("Program level"),
            form,
        }
    }
}
impl ArenaNode for ComputationNode {
    type Handle = Computation;
    fn allocate(self, arena: &Arena) -> Computation {
        let sort = BaseSort::Computation(self.level);
        let (op, fields) = match self.form {
            ComputationForm::ModuleParam { parameter } => {
                let fields = vec![];
                (Op::ModuleParam { parameter }, fields)
            }
            ComputationForm::Constant { definition } => {
                let fields = vec![];
                (Op::Constant { definition }, fields)
            }
            ComputationForm::Return { value } => {
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: value.into(),
                }]];
                (Op::Return, fields)
            }
            ComputationForm::Force { value } => {
                let fields = vec![vec![Child {
                    depth: 0,
                    expression: value.into(),
                }]];
                (Op::Force, fields)
            }
            ComputationForm::LambdaTerm {
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
            ComputationForm::LambdaType {
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
            ComputationForm::AppTerm {
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
            ComputationForm::AppType {
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
            ComputationForm::Sequence {
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
            ComputationForm::ValueLet {
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
            ComputationForm::Case {
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
            ComputationForm::Run {
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
            ComputationForm::RunCase {
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
            .store(Family::Computation, Data { sort, op, fields })
            .try_into()
            .expect("family")
    }
}
impl ArenaHandle for Computation {
    type Node = ComputationNode;
    fn get(self, arena: &Arena) -> Self::Node {
        let data = arena.data(self.into());
        let form = match data.op.clone() {
            Op::ModuleParam { parameter } => ComputationForm::ModuleParam { parameter },
            Op::Constant { definition } => ComputationForm::Constant { definition },
            Op::Return => ComputationForm::Return {
                value: data.child(0).try_into().expect("family"),
            },
            Op::Force => ComputationForm::Force {
                value: data.child(0).try_into().expect("family"),
            },
            Op::LambdaTerm { rule, var } => ComputationForm::LambdaTerm {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::LambdaType { rule, var } => ComputationForm::LambdaType {
                rule,
                var,
                domain: data.child(0).try_into().expect("family"),
                body: data.child(1).try_into().expect("family"),
            },
            Op::AppTerm { rule } => ComputationForm::AppTerm {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::AppType { rule } => ComputationForm::AppType {
                rule,
                function: data.child(0).try_into().expect("family"),
                argument: data.child(1).try_into().expect("family"),
            },
            Op::Sequence { var } => ComputationForm::Sequence {
                var,
                value_ty: data.child(0).try_into().expect("family"),
                computation: data.child(1).try_into().expect("family"),
                body: data.child(2).try_into().expect("family"),
            },
            Op::ValueLet { var } => ComputationForm::ValueLet {
                var,
                value_ty: data.child(0).try_into().expect("family"),
                value: data.child(1).try_into().expect("family"),
                body: data.child(2).try_into().expect("family"),
            },
            Op::Case { inductive, binders } => ComputationForm::Case {
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
            Op::Run => ComputationForm::Run {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                initial: data.child(3).try_into().expect("family"),
            },
            Op::RunCase => ComputationForm::RunCase {
                state_ty: data.child(0).try_into().expect("family"),
                result_ty: data.child(1).try_into().expect("family"),
                step: data.child(2).try_into().expect("family"),
                initial: data.child(3).try_into().expect("family"),
                transition: data.child(4).try_into().expect("family"),
            },
            _ => unreachable!("invalid arena partition"),
        };
        ComputationNode {
            level: data.sort.level().expect("Program level"),
            form,
        }
    }
}
