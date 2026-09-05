//! The four syntactic categories of the CBPV Program calculus.

use serde::{Deserialize, Serialize};

use crate::ids::{DefId, MetaVarId, ModuleParamId, ProgramInductiveId, SymbolId};

macro_rules! handle {
    ($name:ident) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
        pub struct $name(u32);

        impl $name {
            pub fn index(self) -> usize {
                self.0 as usize
            }
            pub(crate) fn from_index(index: u32) -> Self {
                Self(index)
            }
        }
    };
}

handle!(ValueType);
handle!(ComputationType);
handle!(Value);
handle!(Computation);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProgramType {
    Value(ValueType),
    Computation(ComputationType),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Program {
    Value(Value),
    Computation(Computation),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProgramArgument {
    Type(ValueType),
    Value(Value),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ValueTypeNode {
    Bound(usize),
    ModuleParam(ModuleParamId),
    Meta {
        metavariable: MetaVarId,
        spine: Vec<ProgramArgument>,
    },
    Thunk {
        computation_ty: ComputationType,
    },
    RunStep {
        state_ty: ValueType,
        result_ty: ValueType,
    },
    Inductive {
        indspec: ProgramInductiveId,
        parameters: Vec<ValueType>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ComputationTypeNode {
    Meta {
        metavariable: MetaVarId,
        spine: Vec<ProgramArgument>,
    },
    Return {
        value_ty: ValueType,
    },
    Function {
        domain: ValueType,
        codomain: ComputationType,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ProgramCaseBranch {
    pub binders: Vec<SymbolId>,
    pub body: Computation,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ValueNode {
    Bound(usize),
    ModuleParam(ModuleParamId),
    Meta {
        metavariable: MetaVarId,
        spine: Vec<ProgramArgument>,
    },
    DefinedConstant(DefId),
    Thunk {
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
        indspec: ProgramInductiveId,
        parameters: Vec<ValueType>,
        idx: usize,
        fields: Vec<Value>,
    },
    InductiveProjection {
        indspec: ProgramInductiveId,
        parameters: Vec<ValueType>,
        value: Value,
        field: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ComputationNode {
    Meta {
        metavariable: MetaVarId,
        spine: Vec<ProgramArgument>,
    },
    DefinedConstant(DefId),
    Return {
        value: Value,
    },
    Force {
        value: Value,
    },
    Lambda {
        var: SymbolId,
        value_ty: ValueType,
        body: Computation,
    },
    Application {
        computation: Computation,
        value: Value,
    },
    Sequence {
        computation: Computation,
        var: SymbolId,
        value_ty: ValueType,
        body: Computation,
    },
    ValueLet {
        var: SymbolId,
        value: Value,
        body: Computation,
    },
    Case {
        indspec: ProgramInductiveId,
        scrutinee: Value,
        branches: Vec<ProgramCaseBranch>,
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ProgramContextEntry {
    Type { var: SymbolId },
    Value { var: SymbolId, ty: ValueType },
}

pub type ProgramContext = Vec<ProgramContextEntry>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ProgramJudgement {
    ValueType(ValueType),
    ComputationType(ComputationType),
    Value {
        value: Value,
        ty: ValueType,
    },
    Computation {
        computation: Computation,
        ty: ComputationType,
    },
}
