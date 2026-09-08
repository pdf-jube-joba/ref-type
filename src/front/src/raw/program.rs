//! The four syntactic categories of the CBPV Program calculus.

use crate::raw::ids::{DefId, MetaVarId, ModuleParamId, ProgramInductiveId, SymbolId};

macro_rules! handle {
    ($name:ident) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
handle!(ValueTerm);
handle!(ComputationTerm);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProgramType {
    ValueType(ValueType),
    ComputationType(ComputationType),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProgramTerm {
    ValueTerm(ValueTerm),
    ComputationTerm(ComputationTerm),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProgramArgument {
    ValueType(ValueType),
    ValueTerm(ValueTerm),
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProgramCaseBranch {
    pub binders: Vec<SymbolId>,
    pub body: ComputationTerm,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueTermNode {
    Bound(usize),
    ModuleParam(ModuleParamId),
    Meta {
        metavariable: MetaVarId,
        spine: Vec<ProgramArgument>,
    },
    DefinedConstant(DefId),
    Thunk {
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
        indspec: ProgramInductiveId,
        parameters: Vec<ValueType>,
        idx: usize,
        fields: Vec<ValueTerm>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComputationTermNode {
    Meta {
        metavariable: MetaVarId,
        spine: Vec<ProgramArgument>,
    },
    DefinedConstant(DefId),
    Return {
        value: ValueTerm,
    },
    Force {
        value: ValueTerm,
    },
    Lambda {
        var: SymbolId,
        value_ty: ValueType,
        body: ComputationTerm,
    },
    Application {
        computation: ComputationTerm,
        value: ValueTerm,
    },
    Sequence {
        computation: ComputationTerm,
        var: SymbolId,
        value_ty: ValueType,
        body: ComputationTerm,
    },
    ValueLet {
        var: SymbolId,
        value_ty: ValueType,
        value: ValueTerm,
        body: ComputationTerm,
    },
    Case {
        indspec: ProgramInductiveId,
        scrutinee: ValueTerm,
        branches: Vec<ProgramCaseBranch>,
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
pub enum ProgramContextEntry {
    ValueType { var: SymbolId },
    ValueTerm { var: SymbolId, ty: ValueType },
}

pub type ProgramContext = Vec<ProgramContextEntry>;
