//! Unclassified Set/Prop syntax and the front-end arena used during elaboration.

use super::traversal::Term;
use kernel::sharing::LooseBound;
use rustc_hash::{FxHashMap, FxHasher};
use std::{
    cell::{Ref, RefCell},
    hash::{Hash, Hasher},
};

use crate::{
    ids::{DefId, InductiveId, MetaVarId, ModuleParamId, ProgramInductiveId, SymbolId},
    program::{
        ComputationTerm, ComputationTermNode, ComputationType, ComputationTypeNode, ValueTerm,
        ValueTermNode, ValueType, ValueTypeNode,
    },
    sort::Sort,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Exp(u32);

impl Exp {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub fn from_index(index: u32) -> Self {
        Self(index)
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

/// Working nodes are released at unit boundaries. Promoted nodes keep their
/// handles, and an index is never reused within an environment.
#[derive(Debug)]
struct NodeStore<N> {
    frozen: FxHashMap<usize, N>,
    chunks: Vec<Vec<N>>,
    base: usize,
    working_len: usize,
}

impl<N> Default for NodeStore<N> {
    fn default() -> Self {
        Self {
            frozen: FxHashMap::default(),
            chunks: Vec::new(),
            base: 0,
            working_len: 0,
        }
    }
}

impl<N> NodeStore<N> {
    const CHUNK_SIZE: usize = 1024;

    fn len(&self) -> usize {
        self.frozen.len() + self.working_len
    }
    fn next_index(&self) -> usize {
        self.base + self.working_len
    }
    fn is_frozen(&self, index: usize) -> bool {
        index < self.base
    }
    fn contains(&self, index: usize) -> bool {
        if index < self.base {
            self.frozen.contains_key(&index)
        } else {
            index < self.next_index()
        }
    }

    fn push(&mut self, node: N) {
        if self.working_len & (Self::CHUNK_SIZE - 1) == 0 {
            self.chunks.push(Vec::with_capacity(Self::CHUNK_SIZE));
        }
        self.chunks.last_mut().unwrap().push(node);
        self.working_len += 1;
    }

    fn freeze(&mut self, mut retain: impl FnMut(usize) -> bool) {
        for (offset, node) in self.chunks.drain(..).flatten().enumerate() {
            let index = self.base + offset;
            if retain(index) {
                self.frozen.insert(index, node);
            }
        }
        self.base += self.working_len;
        self.working_len = 0;
    }
}

impl<N> std::ops::Index<usize> for NodeStore<N> {
    type Output = N;
    fn index(&self, index: usize) -> &N {
        if index < self.base {
            return self.frozen.get(&index).expect("expired raw working handle");
        }
        let offset = index - self.base;
        &self.chunks[offset / Self::CHUNK_SIZE][offset % Self::CHUNK_SIZE]
    }
}

macro_rules! arena_partition {
    ($node:ty, $handle:ty, $field:ident) => {
        impl ArenaNode for $node {
            type Handle = $handle;
            fn allocate(self, arena: &Arena) -> Self::Handle {
                let mut nodes = arena.$field.borrow_mut();
                let index = u32::try_from(nodes.next_index())
                    .expect("kernel arena partition exceeded u32::MAX");
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
    exps: RefCell<NodeStore<ExpNode>>,
    interned_exps: RefCell<FxHashMap<u64, Exp>>,
    frozen_exps: RefCell<FxHashMap<u64, Exp>>,
    loose_bounds: RefCell<NodeStore<LooseBound>>,
    program_loose_bounds: RefCell<FxHashMap<Term, Option<usize>>>,
    value_types: RefCell<NodeStore<ValueTypeNode>>,
    computation_types: RefCell<NodeStore<ComputationTypeNode>>,
    values: RefCell<NodeStore<ValueTermNode>>,
    computations: RefCell<NodeStore<ComputationTermNode>>,
}

impl ArenaNode for ExpNode {
    type Handle = Exp;

    fn allocate(self, arena: &Arena) -> Self::Handle {
        let mut hasher = FxHasher::default();
        self.hash(&mut hasher);
        let fingerprint = hasher.finish();
        if let Some(existing) = arena.frozen_exps.borrow().get(&fingerprint)
            && arena.exps.borrow()[existing.index()] == self
        {
            return *existing;
        }
        let mut interner = arena.interned_exps.borrow_mut();
        let entry = interner.entry(fingerprint);
        if let std::collections::hash_map::Entry::Occupied(existing) = &entry
            && arena.exps.borrow()[existing.get().index()] == self
        {
            return *existing.get();
        }
        let mut nodes = arena.exps.borrow_mut();
        let index =
            u32::try_from(nodes.next_index()).expect("kernel arena partition exceeded u32::MAX");
        nodes.push(self);
        arena.loose_bounds.borrow_mut().push(LooseBound::default());
        drop(nodes);
        let result = Exp::from_index(index);
        // A hash collision only misses a sharing opportunity; equality above
        // prevents distinct expressions from ever receiving the same handle.
        entry.or_insert(result);
        result
    }
}

impl ArenaHandle for Exp {
    type Node = ExpNode;

    fn get(self, arena: &Arena) -> Self::Node {
        arena.exps.borrow()[self.index()].clone()
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

    fn is_frozen(&self, term: Term) -> bool {
        match term {
            Term::Logical(term) => self.exps.borrow().is_frozen(term.index()),
            Term::ValueType(term) => self.value_types.borrow().is_frozen(term.index()),
            Term::ComputationType(term) => self.computation_types.borrow().is_frozen(term.index()),
            Term::Value(term) => self.values.borrow().is_frozen(term.index()),
            Term::Computation(term) => self.computations.borrow().is_frozen(term.index()),
        }
    }

    /// Promote the transitive closure of published roots, preserving shared DAGs.
    /// Frozen nodes cannot reference newer working nodes, so traversal stops there.
    pub fn freeze(&self, mut roots: Vec<Term>) {
        let mut live = rustc_hash::FxHashSet::default();
        while let Some(term) = roots.pop() {
            if self.is_frozen(term) || !live.insert(term) {
                continue;
            }
            term.visit_children(self, |child, _| roots.push(child));
        }
        self.exps
            .borrow_mut()
            .freeze(|index| live.contains(&Term::Logical(Exp::from_index(index as u32))));
        self.loose_bounds
            .borrow_mut()
            .freeze(|index| live.contains(&Term::Logical(Exp::from_index(index as u32))));
        self.value_types
            .borrow_mut()
            .freeze(|index| live.contains(&Term::ValueType(ValueType::from_index(index as u32))));
        self.computation_types.borrow_mut().freeze(|index| {
            live.contains(&Term::ComputationType(ComputationType::from_index(
                index as u32,
            )))
        });
        self.values
            .borrow_mut()
            .freeze(|index| live.contains(&Term::Value(ValueTerm::from_index(index as u32))));
        self.computations.borrow_mut().freeze(|index| {
            live.contains(&Term::Computation(ComputationTerm::from_index(
                index as u32,
            )))
        });
        let working = std::mem::take(&mut *self.interned_exps.borrow_mut());
        let mut frozen = self.frozen_exps.borrow_mut();
        for (hash, term) in working {
            if self.exps.borrow().contains(term.index()) {
                frozen.entry(hash).or_insert(term);
            }
        }
        *self.program_loose_bounds.borrow_mut() = FxHashMap::default();
    }

    pub fn allocated_node_counts(&self) -> [(&'static str, usize); 5] {
        [
            ("Logical", self.exps.borrow().next_index()),
            ("ValueType", self.value_types.borrow().next_index()),
            (
                "ComputationType",
                self.computation_types.borrow().next_index(),
            ),
            ("ValueTerm", self.values.borrow().next_index()),
            ("ComputationTerm", self.computations.borrow().next_index()),
        ]
    }

    pub fn reachable_node_counts(&self, mut roots: Vec<Term>) -> [usize; 5] {
        let mut seen = rustc_hash::FxHashSet::default();
        let mut counts = [0; 5];
        while let Some(term) = roots.pop() {
            if !seen.insert(term) {
                continue;
            }
            counts[match term {
                Term::Logical(_) => 0,
                Term::ValueType(_) => 1,
                Term::ComputationType(_) => 2,
                Term::Value(_) => 3,
                Term::Computation(_) => 4,
            }] += 1;
            term.visit_children(self, |child, _| roots.push(child));
        }
        counts
    }

    pub fn max_loose_bound(&self, term: Term) -> Option<usize> {
        let cached = match term {
            Term::Logical(e) => self.loose_bounds.borrow()[e.index()].get(),
            _ => self.program_loose_bounds.borrow().get(&term).copied(),
        };
        if let Some(result) = cached {
            return result;
        }
        let mut result = term.bound_index(self);
        term.visit_children(self, |child, depth| {
            if let Some(index) = self
                .max_loose_bound(child)
                .and_then(|i| i.checked_sub(depth))
            {
                result = Some(result.map_or(index, |old| old.max(index)));
            }
        });
        match term {
            Term::Logical(e) => self.loose_bounds.borrow()[e.index()].set(result),
            _ => {
                self.program_loose_bounds.borrow_mut().insert(term, result);
            }
        }
        result
    }

    /// Number of retained nodes in each syntax family.
    pub fn node_counts(&self) -> [(&'static str, usize); 5] {
        [
            ("Logical", self.exps.borrow().len()),
            ("ValueType", self.value_types.borrow().len()),
            ("ComputationType", self.computation_types.borrow().len()),
            ("ValueTerm", self.values.borrow().len()),
            ("ComputationTerm", self.computations.borrow().len()),
        ]
    }

    #[cfg(test)]
    pub fn exp_len(&self) -> usize {
        self.exps.borrow().len()
    }

    pub fn alloc<N: ArenaNode>(&self, node: N) -> N::Handle {
        kernel::control::checkpoint();
        node.allocate(self)
    }

    pub fn get<H: ArenaHandle>(&self, handle: H) -> H::Node {
        handle.get(self)
    }

    pub fn reuse_exp(&self, original: Exp, node: ExpNode) -> Exp {
        if self.exps.borrow()[original.index()] == node {
            original
        } else {
            self.alloc(node)
        }
    }

    // Drop the guard before allocating in the same arena partition.
    pub fn borrow_exp(&self, exp: Exp) -> Ref<'_, ExpNode> {
        Ref::map(self.exps.borrow(), |nodes| &nodes[exp.index()])
    }

    pub fn borrow_value_type(&self, ty: ValueType) -> Ref<'_, ValueTypeNode> {
        Ref::map(self.value_types.borrow(), |nodes| &nodes[ty.index()])
    }

    pub fn borrow_value(&self, value: ValueTerm) -> Ref<'_, ValueTermNode> {
        Ref::map(self.values.borrow(), |nodes| &nodes[value.index()])
    }

    pub fn borrow_computation(&self, term: ComputationTerm) -> Ref<'_, ComputationTermNode> {
        Ref::map(self.computations.borrow(), |nodes| &nodes[term.index()])
    }

    pub fn reuse_value_type(&self, original: ValueType, node: ValueTypeNode) -> ValueType {
        if self.value_types.borrow()[original.index()] == node {
            original
        } else {
            self.alloc(node)
        }
    }

    pub fn reuse_computation_type(
        &self,
        original: ComputationType,
        node: ComputationTypeNode,
    ) -> ComputationType {
        if self.computation_types.borrow()[original.index()] == node {
            original
        } else {
            self.alloc(node)
        }
    }

    pub fn reuse_value(&self, original: ValueTerm, node: ValueTermNode) -> ValueTerm {
        if self.values.borrow()[original.index()] == node {
            original
        } else {
            self.alloc(node)
        }
    }

    pub fn reuse_computation(
        &self,
        original: ComputationTerm,
        node: ComputationTermNode,
    ) -> ComputationTerm {
        if self.computations.borrow()[original.index()] == node {
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
    pub fn as_module_param(&self, exp: Exp) -> Option<ModuleParamId> {
        match self.get(exp) {
            ExpNode::ModuleParam(parameter) => Some(parameter),
            _ => None,
        }
    }
}
