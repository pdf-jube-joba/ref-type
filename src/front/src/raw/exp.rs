//! Unclassified Set/Prop syntax and the front-end arena used during elaboration.

use hashconsing::{HConsed, HConsign, HashConsign};
use rustc_hash::FxBuildHasher;
use std::{cell::RefCell, ops::Deref};

use crate::raw::{
    ids::{DefId, InductiveId, MetaVarId, ModuleParamId, ProgramInductiveId, SymbolId},
    program::{
        ComputationTerm, ComputationTermNode, ComputationType, ComputationTypeNode, ValueTerm,
        ValueTermNode, ValueType, ValueTypeNode,
    },
    sort::Sort,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Exp(HConsed<ExpNode>);

impl Exp {
    pub fn index(&self) -> usize {
        usize::try_from(self.0.uid()).expect("front hashconsing ID exceeds usize")
    }
}
impl Deref for Exp {
    type Target = ExpNode;

    fn deref(&self) -> &Self::Target {
        self.0.get()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ReflectedProgramCaseBranch {
    pub binders: Vec<SymbolId>,
    pub body: Exp,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Axiom {
    SetExt {
        left: Exp,
        right: Exp,
        left_to_right: Exp,
        right_to_left: Exp,
    },
    FunExt {
        left: Exp,
        right: Exp,
        pointwise: Exp,
    },
    ClassicalIndefiniteChoice {
        domain: Exp,
        family: Exp,
        inhabited: Exp,
    },
}

/// A derivation whose conclusion is the judgement `Γ |= P`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Prove {
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
    Axiom(Axiom),
    TakeEq {
        func: Exp,
        domain: Exp,
        codomain: Exp,
        element: Exp,
        existence: Exp,
        uniqueness: Exp,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpNode {
    Sort(Sort),
    Bound(usize),
    /// A Set/Prop module parameter.
    ModuleParam(ModuleParamId),
    /// The Set/Prop term obtained by reflecting a Program module parameter.
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
    IndCase {
        indspec: InductiveId,
        scrutinee: Exp,
        return_type: Exp,
        branches: Vec<Exp>,
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
        accessibility: Exp,
    },
    SetRunCase {
        state_ty: Exp,
        result_ty: Exp,
        step: Exp,
        initial: Exp,
        transition: Exp,
        accessibility: Exp,
        transition_equality: Exp,
    },
    BoxType {
        program_ty: ComputationType,
    },
    BoxProgram {
        program_ty: ComputationType,
        program: ComputationTerm,
    },
    ForceBox {
        program_ty: ComputationType,
        boxed: Exp,
    },
    BoxApp {
        function: Exp,
        argument: Exp,
    },
    Prove(Prove),
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpContextEntry {
    pub var: SymbolId,
    pub ty: Exp,
}

pub type ExpContext = Vec<ExpContextEntry>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpJudgement {
    pub term: Exp,
    pub ty: Exp,
}

pub trait ArenaNode: Sized {
    type Handle;
    fn allocate(self, arena: &Arena) -> Self::Handle;
}

pub trait ArenaHandle: Clone {
    type Node: Clone;
    fn get(&self, arena: &Arena) -> Self::Node;
}

macro_rules! arena_partition {
    ($node:ty, $handle:ident, $field:ident) => {
        impl ArenaNode for $node {
            type Handle = $handle;
            fn allocate(self, arena: &Arena) -> Self::Handle {
                $handle(arena.$field.borrow_mut().mk(self))
            }
        }

        impl ArenaHandle for $handle {
            type Node = $node;
            fn get(&self, _arena: &Arena) -> Self::Node {
                self.0.get().clone()
            }
        }
    };
}

pub struct Arena {
    exp_consign: RefCell<HConsign<ExpNode, FxBuildHasher>>,
    value_types: RefCell<HConsign<ValueTypeNode, FxBuildHasher>>,
    computation_types: RefCell<HConsign<ComputationTypeNode, FxBuildHasher>>,
    values: RefCell<HConsign<ValueTermNode, FxBuildHasher>>,
    computations: RefCell<HConsign<ComputationTermNode, FxBuildHasher>>,
}

impl Default for Arena {
    fn default() -> Self {
        Self {
            exp_consign: RefCell::new(HConsign::with_hasher(FxBuildHasher)),
            value_types: RefCell::new(HConsign::with_hasher(FxBuildHasher)),
            computation_types: RefCell::new(HConsign::with_hasher(FxBuildHasher)),
            values: RefCell::new(HConsign::with_hasher(FxBuildHasher)),
            computations: RefCell::new(HConsign::with_hasher(FxBuildHasher)),
        }
    }
}

impl std::fmt::Debug for Arena {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Arena").finish_non_exhaustive()
    }
}

impl ArenaNode for ExpNode {
    type Handle = Exp;

    fn allocate(self, arena: &Arena) -> Self::Handle {
        Exp(arena.exp_consign.borrow_mut().mk(self))
    }
}

impl ArenaHandle for Exp {
    type Node = ExpNode;

    fn get(&self, _arena: &Arena) -> Self::Node {
        self.0.get().clone()
    }
}

arena_partition!(ValueTypeNode, ValueType, value_types);
arena_partition!(ComputationTypeNode, ComputationType, computation_types);
arena_partition!(ValueTermNode, ValueTerm, values);
arena_partition!(ComputationTermNode, ComputationTerm, computations);

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    #[cfg(test)]
    pub(crate) fn exp_len(&self) -> usize {
        self.exp_consign.borrow().len()
    }

    pub fn alloc<N: ArenaNode>(&self, node: N) -> N::Handle {
        node.allocate(self)
    }

    pub fn get<H: ArenaHandle>(&self, handle: H) -> H::Node {
        handle.get(self)
    }

    pub(crate) fn reuse_exp(&self, original: Exp, node: ExpNode) -> Exp {
        if *original == node {
            original
        } else {
            self.alloc(node)
        }
    }

    pub(crate) fn borrow_exp(&self, exp: Exp) -> Exp {
        exp
    }

    pub fn collect(&self) {
        self.exp_consign.borrow_mut().collect();
        self.value_types.borrow_mut().collect();
        self.computation_types.borrow_mut().collect();
        self.values.borrow_mut().collect();
        self.computations.borrow_mut().collect();
    }

    pub(crate) fn borrow_value_type(&self, ty: ValueType) -> ValueTypeNode {
        ty.0.get().clone()
    }

    pub(crate) fn borrow_value(&self, value: ValueTerm) -> ValueTermNode {
        value.0.get().clone()
    }

    pub(crate) fn borrow_computation(&self, term: ComputationTerm) -> ComputationTermNode {
        term.0.get().clone()
    }

    pub(crate) fn reuse_value_type(&self, original: ValueType, node: ValueTypeNode) -> ValueType {
        if *original == node {
            original
        } else {
            self.alloc(node)
        }
    }

    pub(crate) fn reuse_computation_type(
        &self,
        original: ComputationType,
        node: ComputationTypeNode,
    ) -> ComputationType {
        if *original == node {
            original
        } else {
            self.alloc(node)
        }
    }

    pub(crate) fn reuse_value(&self, original: ValueTerm, node: ValueTermNode) -> ValueTerm {
        if *original == node {
            original
        } else {
            self.alloc(node)
        }
    }

    pub(crate) fn reuse_computation(
        &self,
        original: ComputationTerm,
        node: ComputationTermNode,
    ) -> ComputationTerm {
        if *original == node {
            original
        } else {
            self.alloc(node)
        }
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

    pub fn value_bound(&self, index: usize) -> ValueTerm {
        self.alloc(ValueTermNode::Bound(index))
    }

    pub fn exp_module_param(&self, parameter: ModuleParamId) -> Exp {
        self.alloc(ExpNode::ModuleParam(parameter))
    }

    pub fn value_type_module_param(&self, parameter: ModuleParamId) -> ValueType {
        self.alloc(ValueTypeNode::ModuleParam(parameter))
    }

    #[cfg(test)]
    pub(crate) fn as_module_param(&self, exp: Exp) -> Option<ModuleParamId> {
        match self.get(exp) {
            ExpNode::ModuleParam(parameter) => Some(parameter),
            _ => None,
        }
    }
}
