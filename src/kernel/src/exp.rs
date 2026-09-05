//! Set/Prop syntax and the typed kernel arena.

use std::cell::RefCell;

use serde::{Deserialize, Serialize};

use crate::{
    ids::{DefId, InductiveId, MetaVarId, ModuleParamId, ProgramInductiveId, SymbolId},
    program::{
        Computation, ComputationNode, ComputationType, ComputationTypeNode, Program, ProgramType,
        Value, ValueNode, ValueType, ValueTypeNode,
    },
    sort::Sort,
};

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

handle!(Exp);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ReflectedProgramCaseBranch {
    pub binders: Vec<SymbolId>,
    pub body: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ExpNode {
    Sort(Sort),
    Bound(usize),
    ModuleParam(ModuleParamId),
    ReflectedProgramParam(ModuleParamId),
    Meta {
        metavariable: MetaVarId,
        spine: Vec<Exp>,
    },
    DefinedConstant(DefId),
    Prod {
        var: SymbolId,
        ty: Exp,
        body: Exp,
    },
    Lam {
        var: SymbolId,
        ty: Exp,
        body: Exp,
    },
    App {
        func: Exp,
        arg: Exp,
    },
    IndType {
        indspec: InductiveId,
        parameters: Vec<Exp>,
    },
    IndCtor {
        indspec: InductiveId,
        parameters: Vec<Exp>,
        idx: usize,
    },
    IndElim {
        indspec: InductiveId,
        elim: Exp,
        return_type: Exp,
        cases: Vec<Exp>,
    },
    IndProjection {
        indspec: InductiveId,
        parameters: Vec<Exp>,
        value: Exp,
        field: usize,
    },
    ReflectedProgramCase {
        indspec: ProgramInductiveId,
        scrutinee: Exp,
        branches: Vec<ReflectedProgramCaseBranch>,
    },
    RunStep {
        state_ty: Exp,
        result_ty: Exp,
    },
    Continue {
        state_ty: Exp,
        result_ty: Exp,
        next: Exp,
    },
    Finish {
        state_ty: Exp,
        result_ty: Exp,
        output: Exp,
    },
    Proof {
        proposition: Exp,
    },
    Acc {
        state_ty: Exp,
        result_ty: Exp,
        step: Exp,
        state: Exp,
    },
    RunStepRec {
        state_ty: Exp,
        result_ty: Exp,
        motive: Exp,
        on_continue: Exp,
        on_finish: Exp,
        scrutinee: Exp,
    },
    SetRun {
        state_ty: Exp,
        result_ty: Exp,
        step: Exp,
        initial: Exp,
    },
    SetRunCase {
        state_ty: Exp,
        result_ty: Exp,
        step: Exp,
        initial: Exp,
        transition: Exp,
    },
    BoxType {
        program_ty: ProgramType,
    },
    BoxProgram {
        program_ty: ProgramType,
        program: Program,
    },
    ForceBox {
        program_ty: ProgramType,
        boxed: Exp,
    },
    BoxApp {
        function: Exp,
        argument: Exp,
    },
    RfType {
        program_ty: ProgramType,
    },
    RfTerm {
        program_ty: ProgramType,
        program: Program,
    },
    AccIntro {
        state_ty: Exp,
        result_ty: Exp,
        step: Exp,
        state: Exp,
        predecessors: Exp,
    },
    AccDescent {
        state_ty: Exp,
        result_ty: Exp,
        step: Exp,
        from: Exp,
        to: Exp,
        accessibility: Exp,
        transition: Exp,
    },
    PowerSet {
        set: Exp,
    },
    SubSet {
        var: SymbolId,
        set: Exp,
        predicate: Exp,
    },
    Pred {
        superset: Exp,
        subset: Exp,
        element: Exp,
    },
    TypeLift {
        superset: Exp,
        subset: Exp,
    },
    SubsetIntro {
        superset: Exp,
        subset: Exp,
        element: Exp,
        proof: Exp,
    },
    Equal {
        left: Exp,
        right: Exp,
    },
    Exists {
        set: Exp,
    },
    TakeSet {
        domain: Exp,
        codomain: Exp,
        map: Exp,
        existence: Exp,
        uniqueness: Exp,
    },
    TakeProp {
        domain: Exp,
        proposition: Exp,
        map: Exp,
        existence: Exp,
    },
    ExistsIntro {
        element: Exp,
        set: Exp,
    },
    SubsetElim {
        element: Exp,
        subset: Exp,
        superset: Exp,
    },
    IdRefl {
        element: Exp,
    },
    IdElim {
        left: Exp,
        right: Exp,
        ty: Exp,
        var: SymbolId,
        predicate: Exp,
        base: Exp,
        equality: Exp,
    },
    AxiomSetExt {
        left: Exp,
        right: Exp,
        left_to_right: Exp,
        right_to_left: Exp,
    },
    AxiomFunExt {
        left: Exp,
        right: Exp,
        pointwise: Exp,
    },
    AxiomClassicalIndefiniteChoice {
        domain: Exp,
        family: Exp,
        inhabited: Exp,
    },
    TakeEq {
        func: Exp,
        domain: Exp,
        codomain: Exp,
        element: Exp,
        existence: Exp,
        uniqueness: Exp,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ProofObligation {
    pub context: ExpContext,
    pub proposition: Exp,
    pub rule: &'static str,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ProofEvidence {
    pub context: ExpContext,
    pub proposition: Exp,
    pub witness: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ExpContextEntry {
    pub var: SymbolId,
    pub ty: Exp,
}

pub type ExpContext = Vec<ExpContextEntry>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct ExpJudgement {
    pub term: Exp,
    pub ty: Exp,
}

pub trait ArenaNode: Sized {
    type Handle;
    fn allocate(self, arena: &Arena) -> Self::Handle;
}

pub trait ArenaHandle: Copy {
    type Node: Clone;
    fn get(self, arena: &Arena) -> Self::Node;
}

macro_rules! arena_partition {
    ($node:ty, $handle:ty, $field:ident) => {
        impl ArenaNode for $node {
            type Handle = $handle;
            fn allocate(self, arena: &Arena) -> Self::Handle {
                let mut nodes = arena.$field.borrow_mut();
                let index =
                    u32::try_from(nodes.len()).expect("kernel arena partition exceeded u32::MAX");
                nodes.push(self);
                <$handle>::from_index(index)
            }
        }

        impl ArenaHandle for $handle {
            type Node = $node;
            fn get(self, arena: &Arena) -> Self::Node {
                arena.$field.borrow()[self.index()].clone()
            }
        }
    };
}

#[derive(Debug, Default)]
pub struct Arena {
    exps: RefCell<Vec<ExpNode>>,
    value_types: RefCell<Vec<ValueTypeNode>>,
    computation_types: RefCell<Vec<ComputationTypeNode>>,
    values: RefCell<Vec<ValueNode>>,
    computations: RefCell<Vec<ComputationNode>>,
}

arena_partition!(ExpNode, Exp, exps);
arena_partition!(ValueTypeNode, ValueType, value_types);
arena_partition!(ComputationTypeNode, ComputationType, computation_types);
arena_partition!(ValueNode, Value, values);
arena_partition!(ComputationNode, Computation, computations);

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc<N: ArenaNode>(&self, node: N) -> N::Handle {
        node.allocate(self)
    }

    pub fn get<H: ArenaHandle>(&self, handle: H) -> H::Node {
        handle.get(self)
    }

    pub fn len(&self) -> usize {
        self.exps.borrow().len()
            + self.value_types.borrow().len()
            + self.computation_types.borrow().len()
            + self.values.borrow().len()
            + self.computations.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn sort(&self, sort: Sort) -> Exp {
        self.alloc(ExpNode::Sort(sort))
    }
    pub fn exp_bound(&self, index: usize) -> Exp {
        self.alloc(ExpNode::Bound(index))
    }
    pub fn value_type_bound(&self, index: usize) -> ValueType {
        self.alloc(ValueTypeNode::Bound(index))
    }
    pub fn value_bound(&self, index: usize) -> Value {
        self.alloc(ValueNode::Bound(index))
    }
    pub fn exp_module_param(&self, parameter: ModuleParamId) -> Exp {
        self.alloc(ExpNode::ModuleParam(parameter))
    }
    pub fn value_type_module_param(&self, parameter: ModuleParamId) -> ValueType {
        self.alloc(ValueTypeNode::ModuleParam(parameter))
    }
    pub fn value_module_param(&self, parameter: ModuleParamId) -> Value {
        self.alloc(ValueNode::ModuleParam(parameter))
    }

    pub fn as_module_param(&self, exp: Exp) -> Option<ModuleParamId> {
        match self.get(exp) {
            ExpNode::ModuleParam(parameter) => Some(parameter),
            _ => None,
        }
    }
}
