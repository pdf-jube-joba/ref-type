//! The four syntactic categories of the CBPV Program calculus.

use crate::raw::ids::{DefId, MetaVarId, ModuleParamId, ProgramInductiveId, SymbolId};
use hashconsing::HConsed;
use std::ops::Deref;

macro_rules! handle {
    ($name:ident, $node:ident) => {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        pub struct $name(pub(crate) HConsed<$node>);

        impl $name {
            pub fn index(&self) -> usize {
                usize::try_from(self.0.uid()).expect("front hashconsing ID exceeds usize")
            }
        }

        impl Deref for $name {
            type Target = $node;

            fn deref(&self) -> &Self::Target {
                self.0.get()
            }
        }
    };
}

handle!(ValueType, ValueTypeNode);
handle!(ComputationType, ComputationTypeNode);
handle!(ValueTerm, ValueTermNode);
handle!(ComputationTerm, ComputationTermNode);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProgramType {
    ValueType(ValueType),
    ComputationType(ComputationType),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProgramTerm {
    ValueTerm(ValueTerm),
    ComputationTerm(ComputationTerm),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProgramArgument {
    ValueType(ValueType),
    ValueTerm(ValueTerm),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProgramCaseBranch {
    pub binders: Vec<SymbolId>,
    pub body: ComputationTerm,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueTermNode {
    Bound(usize),
    ModuleParam(ModuleParamId),
    Meta {
        metavariable: MetaVarId,
        spine: Vec<ProgramArgument>,
    },
    DefinedConstant(DefId),
    DefinitionInstance {
        definition: DefId,
        parameters: Vec<ValueType>,
    },
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ComputationTermNode {
    Meta {
        metavariable: MetaVarId,
        spine: Vec<ProgramArgument>,
    },
    DefinedConstant(DefId),
    DefinitionInstance {
        definition: DefId,
        parameters: Vec<ValueType>,
    },
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
        accessibility: crate::raw::exp::Exp,
    },
    RunCase {
        state_ty: ValueType,
        result_ty: ValueType,
        step: ValueTerm,
        initial: ValueTerm,
        transition: ComputationTerm,
        accessibility: crate::raw::exp::Exp,
        transition_equality: crate::raw::exp::Exp,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProgramContextEntry {
    ValueType { var: SymbolId },
    ValueTerm { var: SymbolId, ty: ValueType },
}

pub type ProgramContext = Vec<ProgramContextEntry>;
