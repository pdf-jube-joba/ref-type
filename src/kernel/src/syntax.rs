//! Shared PTS syntax for elaboration, unification, and checking.
use crate::ids::{DefinitionId, InductiveId, ParameterId, ProgramInductiveId, SymbolId};
use crate::sort::Sort;
use rustc_hash::FxHashMap;
use std::{cell::RefCell, rc::Rc};

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Expression(u32);
artifact::identity!(Expression, "expression");
impl Expression {
    /// Reconstruct an opaque handle for a validated import table.
    pub fn from_index(index: u32) -> Self {
        Self(index)
    }
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MetaId {
    #[serde(deserialize_with = "crate::ids::deserialize_identity")]
    pub(crate) session: u64,
    pub(crate) index: u32,
}

impl MetaId {
    /// Allocate a rigid frontend atom without creating a solver entry or node.
    pub fn fresh_atom() -> Self {
        Self {
            session: crate::ids::fresh_identity(),
            index: 0,
        }
    }
}

impl artifact::Relocate for MetaId {
    fn relocate(&mut self, r: &mut artifact::Relocation) -> artifact::Result<()> {
        (self.session, self.index) = r.pair("meta", (self.session, self.index))?;
        Ok(())
    }
}

#[derive(
    artifact::Relocate,
    serde::Serialize,
    serde::Deserialize,
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    Hash,
)]
pub enum Mode {
    Pure,
    Computation,
}

#[derive(
    artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Eq, Hash,
)]
pub enum Node {
    Ascribe {
        term: Expression,
        ty: Expression,
    },
    Sort(Sort),
    Bound(usize),
    Parameter(ParameterId),
    Definition {
        id: DefinitionId,
        arguments: Vec<Expression>,
    },
    Meta {
        id: MetaId,
        arguments: Vec<Expression>,
    },
    Product {
        var: SymbolId,
        domain: Expression,
        body: Expression,
    },
    Lambda {
        mode: Mode,
        var: SymbolId,
        domain: Expression,
        body: Expression,
    },
    App {
        mode: Mode,
        function: Expression,
        argument: Expression,
    },
    Reflect {
        term: Expression,
    },
    Subset {
        var: SymbolId,
        set: Expression,
        predicate: Expression,
    },
    SubsetIntro {
        superset: Expression,
        subset: Expression,
        element: Expression,
        proof: Expression,
    },
    Continue {
        state_ty: Expression,
        result_ty: Expression,
        next: Expression,
    },
    Finish {
        state_ty: Expression,
        result_ty: Expression,
        output: Expression,
    },
    SetRun {
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        initial: Expression,
        accessibility: Expression,
    },
    SetRunCase {
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        initial: Expression,
        transition: Expression,
        accessibility: Expression,
        transition_equality: Expression,
    },
    SetStepMatch {
        state_ty: Expression,
        result_ty: Expression,
        motive: Expression,
        on_continue: Expression,
        on_finish: Expression,
    },
    ProgramStepMatch {
        state_ty: Expression,
        result_ty: Expression,
        computation_ty: Expression,
        on_continue: Expression,
        on_finish: Expression,
        scrutinee: Expression,
    },
    BoxProgram {
        program_ty: Expression,
        program: Expression,
    },
    ForceBox {
        program_ty: Expression,
        boxed: Expression,
    },
    BoxApp {
        function: Expression,
        argument: Expression,
    },
    BoxTypeApp {
        function: Expression,
        argument: Expression,
    },
    Choice {
        set: Expression,
        existence: Expression,
        uniqueness: Expression,
    },
    IndCtor {
        inductive: InductiveId,
        constructor: usize,
        parameters: Vec<Expression>,
    },
    IndElim {
        motive_bindings: Vec<(SymbolId, Expression)>,
        inductive: InductiveId,
        scrutinee: Expression,
        motive: Expression,
        cases: Vec<Expression>,
    },
    Case {
        inductive: InductiveId,
        scrutinee: Expression,
        motive: Expression,
        branches: Vec<Expression>,
    },
    SetCase {
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
        scrutinee: Expression,
        branches: Vec<Expression>,
    },
    PowerSet {
        set: Expression,
    },
    TypeLift {
        superset: Expression,
        subset: Expression,
    },
    RunStep {
        state_ty: Expression,
        result_ty: Expression,
    },
    BoxType {
        program_ty: Expression,
    },
    IndType {
        inductive: InductiveId,
        parameters: Vec<Expression>,
    },
    IdRefl {
        element: Expression,
    },
    ExistsIntro {
        element: Expression,
        set: Expression,
    },
    SubsetElim {
        element: Expression,
        subset: Expression,
        superset: Expression,
    },
    IdElim {
        var: SymbolId,
        left: Expression,
        right: Expression,
        ty: Expression,
        family: Expression,
        base: Expression,
        equality: Expression,
    },
    TransportEq {
        var: SymbolId,
        ty: Expression,
        index: Expression,
        family: Expression,
        base: Expression,
    },
    TakeProp {
        domain: Expression,
        proposition: Expression,
        map: Expression,
        existence: Expression,
    },
    ChoiceEq {
        set: Expression,
        element: Expression,
        existence: Expression,
        uniqueness: Expression,
    },
    SetExt {
        left: Expression,
        right: Expression,
        left_to_right: Expression,
        right_to_left: Expression,
    },
    FunExt {
        left: Expression,
        right: Expression,
        pointwise: Expression,
    },
    ClassicalIndefiniteChoice {
        domain: Expression,
        family: Expression,
        inhabited: Expression,
    },
    Pred {
        superset: Expression,
        subset: Expression,
        element: Expression,
    },
    Equal {
        left: Expression,
        right: Expression,
    },
    Exists {
        set: Expression,
    },
    ThunkValue {
        computation: Expression,
    },
    ProgramContinue {
        state_ty: Expression,
        result_ty: Expression,
        next: Expression,
    },
    ProgramFinish {
        state_ty: Expression,
        result_ty: Expression,
        output: Expression,
    },
    InductiveConstructor {
        inductive: ProgramInductiveId,
        constructor: usize,
        parameters: Vec<Expression>,
        fields: Vec<Expression>,
    },
    Thunk {
        computation_ty: Expression,
    },
    ProgramRunStep {
        state_ty: Expression,
        result_ty: Expression,
    },
    Inductive {
        inductive: ProgramInductiveId,
        parameters: Vec<Expression>,
    },
    Return {
        value: Expression,
    },
    Force {
        value: Expression,
    },
    Sequence {
        var: SymbolId,
        value_ty: Expression,
        computation: Expression,
        body: Expression,
    },
    ValueLet {
        var: SymbolId,
        value_ty: Expression,
        value: Expression,
        body: Expression,
    },
    ProgramCase {
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
        scrutinee: Expression,
        branches: Vec<Expression>,
    },
    Run {
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        initial: Expression,
        accessibility: Expression,
    },
    RunCase {
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        initial: Expression,
        transition: Expression,
        accessibility: Expression,
        transition_equality: Expression,
    },
    ReturnType {
        value_ty: Expression,
    },
}

// A child list records traversal order, nested binders, and vector fields.
macro_rules! visit_slots {
    ($visit:ident;) => {};
    ($visit:ident; ..$children:ident @ $binders:ident, $($rest:tt)*) => {
        for (i, child) in IntoIterator::into_iter($children).enumerate() {
            $visit(child, $binders.get(i).map_or(0, Vec::len))?;
        }
        visit_slots!($visit; $($rest)*);
    };
    ($visit:ident; ..$children:ident, $($rest:tt)*) => {
        for child in $children {
            $visit(child, 0)?;
        }
        visit_slots!($visit; $($rest)*);
    };
    ($visit:ident; $child:ident @ $depth:expr, $($rest:tt)*) => {
        $visit($child, $depth)?;
        visit_slots!($visit; $($rest)*);
    };
    ($visit:ident; $child:ident, $($rest:tt)*) => {
        $visit($child, 0)?;
        visit_slots!($visit; $($rest)*);
    };
}

// Shared field order and binder depths for borrowed traversal and rewriting.
macro_rules! node_children {
    ($node:expr, $visit:ident) => {
        match $node {
            Node::Ascribe { term, ty } => {
                visit_slots!($visit; term, ty,);
            }
            Node::Sort(_) | Node::Bound(_) | Node::Parameter(_) => {
                visit_slots!($visit; );
            }
            Node::Definition { arguments, .. } | Node::Meta { arguments, .. } => {
                visit_slots!($visit; ..arguments,);
            }
            Node::Product { domain, body, .. } | Node::Lambda { domain, body, .. } => {
                visit_slots!($visit; domain, body @ 1,);
            }
            Node::App { function, argument, .. }
            | Node::BoxApp { function, argument }
            | Node::BoxTypeApp { function, argument } => {
                visit_slots!($visit; function, argument,);
            }
            Node::Reflect { term } => {
                visit_slots!($visit; term,);
            }
            Node::Subset { set, predicate, .. } => {
                visit_slots!($visit; set, predicate @ 1,);
            }
            Node::SubsetIntro { superset, subset, element, proof, .. } => {
                visit_slots!($visit; superset, subset, element, proof,);
            }
            Node::Continue { state_ty, result_ty, next, .. }
            | Node::ProgramContinue { state_ty, result_ty, next, .. } => {
                visit_slots!($visit; state_ty, result_ty, next,);
            }
            Node::Finish { state_ty, result_ty, output, .. }
            | Node::ProgramFinish { state_ty, result_ty, output, .. } => {
                visit_slots!($visit; state_ty, result_ty, output,);
            }
            Node::SetRun { state_ty, result_ty, step, initial, accessibility, .. }
            | Node::Run { state_ty, result_ty, step, initial, accessibility, .. } => {
                visit_slots!($visit; state_ty, result_ty, step, initial, accessibility,);
            }
            Node::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
                ..
            }
            | Node::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
                ..
            } => {
                visit_slots!($visit;
                    state_ty,
                    result_ty,
                    step,
                    initial,
                    transition,
                    accessibility,
                    transition_equality,
                );
            }
            Node::SetStepMatch { state_ty, result_ty, motive, on_continue, on_finish, } => {
                visit_slots!($visit; state_ty, result_ty, motive, on_continue, on_finish,);
            }
            Node::ProgramStepMatch {
                state_ty,
                result_ty,
                computation_ty: motive,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                visit_slots!($visit;
                    state_ty,
                    result_ty,
                    motive,
                    on_continue,
                    on_finish,
                    scrutinee,
                );
            }
            Node::BoxProgram { program_ty, program, .. } => {
                visit_slots!($visit; program_ty, program,);
            }
            Node::ForceBox { program_ty, boxed, .. } => {
                visit_slots!($visit; program_ty, boxed,);
            }
            Node::Choice { set, existence, uniqueness, .. } => {
                visit_slots!($visit; set, existence, uniqueness,);
            }
            Node::IndCtor { parameters, .. }
            | Node::IndType { parameters, .. }
            | Node::Inductive { parameters, .. } => {
                visit_slots!($visit; ..parameters,);
            }
            Node::IndElim { scrutinee, motive_bindings, motive, cases, .. } => {
                $visit(scrutinee, 0)?;
                let depth = motive_bindings.len();
                for (i, (_, domain)) in IntoIterator::into_iter(motive_bindings).enumerate() {
                    $visit(domain, i)?;
                }
                visit_slots!($visit; motive @ depth, ..cases,);
            }
            Node::Case { scrutinee, motive, branches, .. } => {
                visit_slots!($visit; scrutinee, motive, ..branches,);
            }
            Node::SetCase { scrutinee, branches, binders, .. }
            | Node::ProgramCase { scrutinee, branches, binders, .. } => {
                visit_slots!($visit; scrutinee, ..branches @ binders,);
            }
            Node::PowerSet { set, .. }
            | Node::Exists { set, .. } => {
                visit_slots!($visit; set,);
            }
            Node::TypeLift { superset, subset, .. } => {
                visit_slots!($visit; superset, subset,);
            }
            Node::RunStep { state_ty, result_ty, .. }
            | Node::ProgramRunStep { state_ty, result_ty, .. } => {
                visit_slots!($visit; state_ty, result_ty,);
            }
            Node::BoxType { program_ty, .. } => {
                visit_slots!($visit; program_ty,);
            }
            Node::IdRefl { element, .. } => {
                visit_slots!($visit; element,);
            }
            Node::ExistsIntro { element, set, .. } => {
                visit_slots!($visit; element, set,);
            }
            Node::SubsetElim { element, subset, superset, .. } => {
                visit_slots!($visit; element, subset, superset,);
            }
            Node::TransportEq { ty, index, family, base, .. } => {
                visit_slots!($visit; ty, index, family @ 1, base,);
            }
            Node::IdElim { left, right, ty, family, base, equality, .. } => {
                visit_slots!($visit; left, right, ty, family @ 1, base, equality,);
            }
            Node::TakeProp { domain, proposition, map, existence, .. } => {
                visit_slots!($visit; domain, proposition, map, existence,);
            }
            Node::ChoiceEq { set, element, existence, uniqueness, .. } => {
                visit_slots!($visit; set, element, existence, uniqueness,);
            }
            Node::SetExt { left, right, left_to_right, right_to_left, .. } => {
                visit_slots!($visit; left, right, left_to_right, right_to_left,);
            }
            Node::FunExt { left, right, pointwise, .. } => {
                visit_slots!($visit; left, right, pointwise,);
            }
            Node::ClassicalIndefiniteChoice { domain, family, inhabited, .. } => {
                visit_slots!($visit; domain, family, inhabited,);
            }
            Node::Pred { superset, subset, element, .. } => {
                visit_slots!($visit; superset, subset, element,);
            }
            Node::Equal { left, right, .. } => {
                visit_slots!($visit; left, right,);
            }
            Node::ThunkValue { computation, .. } => {
                visit_slots!($visit; computation,);
            }
            Node::InductiveConstructor { parameters, fields, .. } => {
                visit_slots!($visit; ..parameters, ..fields,);
            }
            Node::Thunk { computation_ty, .. } => {
                visit_slots!($visit; computation_ty,);
            }
            Node::Return { value, .. }
            | Node::Force { value, .. } => {
                visit_slots!($visit; value,);
            }
            Node::Sequence { value_ty, computation, body, .. } => {
                visit_slots!($visit; value_ty, computation, body @ 1,);
            }
            Node::ValueLet { value_ty, value, body, .. } => {
                visit_slots!($visit; value_ty, value, body @ 1,);
            }
            Node::ReturnType { value_ty, .. } => {
                visit_slots!($visit; value_ty,);
            }
        }
    };
}

impl Node {
    /// Visit immediate child expressions with their additional binder depth.
    pub fn try_for_each_child<E>(
        &self,
        mut visit: impl FnMut(Expression, usize) -> Result<(), E>,
    ) -> Result<(), E> {
        let mut slot = |child: &Expression, depth| visit(*child, depth);
        node_children!(self, slot);
        Ok(())
    }
}

#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
struct Properties {
    // Separate presence/meta bits avoid the padding of (Option<usize>, bool)
    // for every arena slot, including retired scratch expressions.
    bounds: Vec<u32>,
    flags: Vec<u8>,
    wide_bounds: FxHashMap<usize, usize>,
}

impl Properties {
    fn push(&mut self, (bound, meta, parameter): (Option<usize>, bool, bool)) {
        let bound_value = bound.unwrap_or(0);
        if bound_value > u32::MAX as usize {
            self.wide_bounds.insert(self.bounds.len(), bound_value);
        }
        self.bounds.push(bound_value.min(u32::MAX as usize) as u32);
        self.flags
            .push(u8::from(bound.is_some()) | (u8::from(meta) << 1) | (u8::from(parameter) << 2));
    }

    fn get(&self, index: usize) -> (Option<usize>, bool, bool) {
        let flags = self.flags[index];
        (
            (flags & 1 != 0).then(|| {
                if self.bounds[index] == u32::MAX {
                    self.wide_bounds
                        .get(&index)
                        .copied()
                        .unwrap_or(u32::MAX as usize)
                } else {
                    self.bounds[index] as usize
                }
            }),
            flags & 2 != 0,
            flags & 4 != 0,
        )
    }
}

// Hashes select candidate chains; complete nodes establish identity. A compact
// fingerprint and handle keep each intern bucket's payload at eight bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct NodeHash(u32);
impl std::hash::Hash for NodeHash {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u32(self.0);
    }
}

#[derive(Debug, Default)]
struct Storage {
    nodes: crate::node_store::NodeStore,
    interned: FxHashMap<NodeHash, Expression>,
    hot: crate::sharing::Cache<NodeHash, (Node, Expression), { 1 << 16 }>,
    collisions: FxHashMap<Expression, Expression>,
    live: usize,
    properties: Properties,
}

impl Storage {
    fn hash(node: &Node) -> NodeHash {
        use std::hash::{Hash, Hasher};
        let mut hash = rustc_hash::FxHasher::default();
        node.hash(&mut hash);
        let hash = hash.finish();
        NodeHash((hash ^ (hash >> 32)) as u32)
    }

    fn intern(&mut self, index: usize, node: &Node) {
        let hash = Self::hash(node);
        let previous = self.interned.insert(hash, Expression(index as u32));
        if let Some(previous) = previous {
            self.collisions.insert(Expression(index as u32), previous);
        }
        self.live += 1;
    }

    fn discard(&mut self, index: usize) {
        if let Some(node) = self.nodes.take(index).expect("retire expression") {
            let hash = Self::hash(&node);
            let mut current = self.interned.get(&hash).copied();
            let mut previous: Option<Expression> = None;
            while let Some(e) = current {
                let next = self.collisions.get(&e).copied();
                if e.index() == index {
                    if let Some(previous) = previous {
                        if let Some(next) = next {
                            self.collisions.insert(previous, next);
                        } else {
                            self.collisions.remove(&previous);
                        }
                    } else if let Some(next) = next {
                        self.interned.insert(hash, next);
                    } else {
                        self.interned.remove(&hash);
                    }
                    self.collisions.remove(&e);
                    self.live -= 1;
                    return;
                }
                previous = Some(e);
                current = next;
            }
            panic!("live expression missing from intern index");
        }
    }
    fn node_properties(&self, node: &Node) -> (Option<usize>, bool, bool) {
        let mut properties = (
            if let Node::Bound(i) = node {
                Some(*i)
            } else {
                None
            },
            matches!(node, Node::Meta { .. }),
            matches!(node, Node::Parameter(_)),
        );
        let _: Result<(), std::convert::Infallible> = node.try_for_each_child(|child, depth| {
            let (bound, meta, parameter) = self.properties.get(child.index());
            if let Some(i) = bound.and_then(|i| i.checked_sub(depth)) {
                properties.0 = Some(properties.0.map_or(i, |old| old.max(i)));
            }
            properties.1 |= meta;
            properties.2 |= parameter;
            Ok(())
        });
        properties
    }
}

#[derive(Debug, Clone, Default)]
pub struct Arena(Rc<RefCell<Storage>>);
impl Arena {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn alloc(&self, node: Node) -> Expression {
        let mut storage = self.0.borrow_mut();
        if crate::resources::collection_requested() {
            storage.nodes.set_budget(64 * 1024 * 1024);
        }
        let hash = Storage::hash(&node);
        if let Some((previous, expression)) = storage.hot.get(&hash)
            && previous == &node
            && storage.nodes.is_live(expression.index())
        {
            return *expression;
        }
        let mut candidate = storage.interned.get(&hash).copied();
        while let Some(e) = candidate {
            if storage
                .nodes
                .get(e.index())
                .expect("read interned expression")
                .as_deref()
                == Some(&node)
            {
                storage.hot.insert(hash, (node, e));
                return e;
            }
            candidate = storage.collisions.get(&e).copied();
        }
        let properties = storage.node_properties(&node);
        let index = storage.nodes.len();
        let e = Expression(u32::try_from(index).expect("expression arena exhausted"));
        storage.properties.push(properties);
        storage.intern(index, &node);
        storage.hot.insert(hash, (node.clone(), e));
        storage
            .nodes
            .push(Some(node))
            .expect("append expression page");
        e
    }
    pub fn read(&self, e: Expression) -> Rc<Node> {
        self.0
            .borrow_mut()
            .nodes
            .get(e.index())
            .expect("load expression page")
            .expect("discarded scratch expression")
    }
    pub fn get(&self, e: Expression) -> Node {
        self.read(e).as_ref().clone()
    }
    pub fn len(&self) -> usize {
        self.0.borrow().live
    }
    pub fn store_stats(&self) -> crate::StoreStats {
        let storage = self.0.borrow();
        let mut stats = storage.nodes.stats();
        stats.live_nodes = storage.live;
        stats.hash_collisions = storage.collisions.len();
        stats.index_capacity_bytes += storage.interned.capacity()
            * std::mem::size_of::<(NodeHash, Expression)>()
            + storage.collisions.capacity() * std::mem::size_of::<(Expression, Expression)>()
            + storage.properties.bounds.capacity() * std::mem::size_of::<u32>()
            + storage.properties.flags.capacity()
            + storage.properties.wide_bounds.capacity() * std::mem::size_of::<(usize, usize)>();
        stats
    }
    pub fn set_resident_budget(&self, bytes: usize) {
        self.0.borrow_mut().nodes.set_budget(bytes);
    }
    pub fn trim(&self) -> std::io::Result<()> {
        self.0.borrow_mut().nodes.trim(None)
    }
    pub(crate) fn scratch_mark(&self) -> usize {
        self.0.borrow().nodes.len()
    }
    pub(crate) fn rollback_import(&self, mark: usize) {
        let mut storage = self.0.borrow_mut();
        storage.hot.clear();
        for index in mark..storage.nodes.len() {
            storage.discard(index);
        }
        storage
            .nodes
            .truncate(mark)
            .expect("roll back expression import");
        storage
            .properties
            .wide_bounds
            .retain(|&index, _| index < mark);
        storage.properties.bounds.truncate(mark);
        storage.properties.flags.truncate(mark);
    }
    pub(crate) fn is_live(&self, e: Expression) -> bool {
        self.0.borrow().nodes.is_live(e.index())
    }
    pub(crate) fn finish_scratch(
        &self,
        mark: usize,
        roots: impl IntoIterator<Item = Expression>,
    ) -> usize {
        let mut pending: Vec<_> = roots.into_iter().collect();
        pending.extend(self.0.borrow_mut().nodes.pinned(mark));
        let mut live = rustc_hash::FxHashSet::default();
        while let Some(e) = pending.pop() {
            if e.index() >= mark && live.insert(e) {
                pending.extend(self.children(e).into_iter().map(|(e, _)| e));
            }
        }
        let mut storage = self.0.borrow_mut();
        let before = storage.live;
        for index in mark..storage.nodes.len() {
            if !live.contains(&Expression(index as u32)) {
                storage.discard(index);
            }
        }
        before - storage.live
    }
    pub fn contains_meta(&self, e: Expression) -> bool {
        self.properties(e).1
    }
    pub fn contains_parameter(&self, e: Expression) -> bool {
        self.properties(e).2
    }
    pub fn max_loose_bound(&self, e: Expression) -> Option<usize> {
        self.properties(e).0
    }
    fn properties(&self, e: Expression) -> (Option<usize>, bool, bool) {
        self.0.borrow().properties.get(e.index())
    }
    pub fn node_counts(&self) -> Vec<(&'static str, usize)> {
        vec![("Expression", self.len())]
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn sort(&self, sort: Sort) -> Expression {
        self.alloc(Node::Sort(sort))
    }
    pub fn bound(&self, index: usize) -> Expression {
        self.alloc(Node::Bound(index))
    }

    pub fn map_children<E>(
        &self,
        e: Expression,
        mut visit: impl FnMut(Expression, usize) -> Result<Expression, E>,
    ) -> Result<Expression, E> {
        let mut changed = false;
        let node = self.map_node_children(self.get(e), |child, depth| {
            let mapped = visit(child, depth)?;
            changed |= mapped != child;
            Ok(mapped)
        })?;
        Ok(if changed { self.alloc(node) } else { e })
    }
    pub fn map_node_children<E>(
        &self,
        mut node: Node,
        mut visit: impl FnMut(Expression, usize) -> Result<Expression, E>,
    ) -> Result<Node, E> {
        let mut slot = |child: &mut Expression, depth| {
            *child = visit(*child, depth)?;
            Ok(())
        };
        node_children!(&mut node, slot);
        Ok(node)
    }

    pub fn try_for_each_child<E>(
        &self,
        e: Expression,
        visit: impl FnMut(Expression, usize) -> Result<(), E>,
    ) -> Result<(), E> {
        self.read(e).try_for_each_child(visit)
    }

    pub fn children(&self, e: Expression) -> Vec<(Expression, usize)> {
        let mut children = Vec::new();
        let _: Result<_, std::convert::Infallible> = self.try_for_each_child(e, |child, depth| {
            children.push((child, depth));
            Ok(())
        });
        children
    }
}

#[derive(
    artifact::Relocate, serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Eq, Hash,
)]
pub struct Binding {
    pub var: SymbolId,
    pub ty: Expression,
}
pub type Context = Vec<Binding>;

// Node indices remain stable across snapshots; interning tables are reconstructed.
struct InlineArena<'a>(&'a Arena);
impl serde::Serialize for InlineArena<'_> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeSeq;
        let mut storage = self.0.0.borrow_mut();
        let mut seq = serializer.serialize_seq(Some(storage.nodes.len()))?;
        for index in 0..storage.nodes.len() {
            let node = storage
                .nodes
                .get(index)
                .map_err(serde::ser::Error::custom)?;
            seq.serialize_element(&node)?;
        }
        seq.end()
    }
}
struct InlineOwned(Arena);
impl<'de> serde::Deserialize<'de> for InlineOwned {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Nodes;
        impl<'de> serde::de::Visitor<'de> for Nodes {
            type Value = Arena;
            fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str("expression graph")
            }
            fn visit_seq<A: serde::de::SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> Result<Arena, A::Error> {
                let mut storage = Storage::default();
                while let Some(node) = seq.next_element::<Option<Node>>()? {
                    let index = storage.nodes.len();
                    u32::try_from(index).map_err(serde::de::Error::custom)?;
                    if let Some(node) = &node {
                        node.try_for_each_child(|child, _| {
                            if child.index() >= index || !storage.nodes.is_live(child.index()) {
                                return Err(serde::de::Error::custom("invalid arena reference"));
                            }
                            Ok(())
                        })?;
                        storage.intern(index, node);
                    }
                    let properties = node
                        .as_ref()
                        .map_or((None, false, false), |node| storage.node_properties(node));
                    storage.properties.push(properties);
                    storage.nodes.push(node).map_err(serde::de::Error::custom)?;
                }
                Ok(Arena(Rc::new(RefCell::new(storage))))
            }
        }
        deserializer.deserialize_seq(Nodes).map(InlineOwned)
    }
}

#[derive(serde::Serialize)]
struct StoredArena<'a> {
    identity_boundary: u64,
    nodes: crate::node_store::StoredNodes,
    properties: &'a Properties,
    interned: &'a FxHashMap<NodeHash, Expression>,
    collisions: &'a FxHashMap<Expression, Expression>,
}
#[derive(serde::Deserialize)]
struct RestoredArena {
    identity_boundary: u64,
    nodes: crate::node_store::StoredNodes,
    properties: Properties,
    interned: FxHashMap<NodeHash, Expression>,
    collisions: FxHashMap<Expression, Expression>,
}
impl serde::Serialize for Arena {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeTuple;
        let mut tuple = serializer.serialize_tuple(2)?;
        if let Some(store) = crate::graph_store::current() {
            let mut storage = self.0.borrow_mut();
            let nodes = storage
                .nodes
                .snapshot(store)
                .map_err(serde::ser::Error::custom)?;
            tuple.serialize_element(&1u8)?;
            tuple.serialize_element(&StoredArena {
                identity_boundary: crate::ids::identity_boundary(),
                nodes,
                properties: &storage.properties,
                interned: &storage.interned,
                collisions: &storage.collisions,
            })?;
        } else {
            tuple.serialize_element(&0u8)?;
            tuple.serialize_element(&InlineArena(self))?;
        }
        tuple.end()
    }
}
impl<'de> serde::Deserialize<'de> for Arena {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Graph;
        impl<'de> serde::de::Visitor<'de> for Graph {
            type Value = Arena;
            fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str("stored expression graph")
            }
            fn visit_seq<A: serde::de::SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> Result<Arena, A::Error> {
                use serde::de::Error;
                match seq.next_element::<u8>()? {
                    Some(0) => seq
                        .next_element::<InlineOwned>()?
                        .map(|arena| arena.0)
                        .ok_or_else(|| A::Error::custom("missing inline graph")),
                    Some(1) => {
                        let saved: RestoredArena = seq
                            .next_element()?
                            .ok_or_else(|| A::Error::custom("missing stored graph"))?;
                        crate::ids::reserve_identities(saved.identity_boundary);
                        let store = crate::graph_store::current()
                            .ok_or_else(|| A::Error::custom("graph store unavailable"))?;
                        let nodes = crate::node_store::NodeStore::restore(saved.nodes, store)
                            .map_err(A::Error::custom)?;
                        let len = nodes.len();
                        if len > u32::MAX as usize
                            || saved.properties.bounds.len() != len
                            || saved.properties.flags.len() != len
                        {
                            return Err(A::Error::custom("invalid graph indices"));
                        }
                        let mut seen = vec![false; len];
                        let mut live = 0;
                        for &head in saved.interned.values() {
                            let mut current = Some(head);
                            while let Some(node) = current {
                                if !nodes.is_live(node.index())
                                    || std::mem::replace(&mut seen[node.index()], true)
                                {
                                    return Err(A::Error::custom("invalid intern index"));
                                }
                                live += 1;
                                current = saved.collisions.get(&node).copied();
                            }
                        }
                        if (0..len).any(|index| seen[index] != nodes.is_live(index))
                            || saved
                                .collisions
                                .keys()
                                .any(|node| !nodes.is_live(node.index()))
                        {
                            return Err(A::Error::custom("incomplete intern index"));
                        }
                        let storage = Storage {
                            nodes,
                            properties: saved.properties,
                            interned: saved.interned,
                            collisions: saved.collisions,
                            live,
                            ..Storage::default()
                        };
                        Ok(Arena(Rc::new(RefCell::new(storage))))
                    }
                    _ => Err(A::Error::custom("unknown graph storage format")),
                }
            }
        }
        deserializer.deserialize_tuple(2, Graph)
    }
}

impl Node {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Ascribe { .. } => "Ascribe",
            Self::Sort(..) => "Sort",
            Self::Bound(..) => "Bound",
            Self::Parameter(..) => "Parameter",
            Self::Definition { .. } => "Definition",
            Self::Meta { .. } => "Meta",
            Self::Product { .. } => "Product",
            Self::Lambda { .. } => "Lambda",
            Self::App { .. } => "App",
            Self::Reflect { .. } => "Reflect",
            Self::Subset { .. } => "Subset",
            Self::SubsetIntro { .. } => "SubsetIntro",
            Self::Continue { .. } => "Continue",
            Self::Finish { .. } => "Finish",
            Self::SetRun { .. } => "SetRun",
            Self::SetRunCase { .. } => "SetRunCase",
            Self::SetStepMatch { .. } => "SetStepMatch",
            Self::ProgramStepMatch { .. } => "ProgramStepMatch",
            Self::BoxProgram { .. } => "BoxProgram",
            Self::ForceBox { .. } => "ForceBox",
            Self::BoxApp { .. } => "BoxApp",
            Self::BoxTypeApp { .. } => "BoxTypeApp",
            Self::Choice { .. } => "Choice",
            Self::IndCtor { .. } => "IndCtor",
            Self::IndElim { .. } => "IndElim",
            Self::Case { .. } => "Case",
            Self::SetCase { .. } => "SetCase",
            Self::PowerSet { .. } => "PowerSet",
            Self::TypeLift { .. } => "TypeLift",
            Self::RunStep { .. } => "RunStep",
            Self::BoxType { .. } => "BoxType",
            Self::IndType { .. } => "IndType",
            Self::IdRefl { .. } => "IdRefl",
            Self::ExistsIntro { .. } => "ExistsIntro",
            Self::SubsetElim { .. } => "SubsetElim",
            Self::IdElim { .. } => "IdElim",
            Self::TransportEq { .. } => "TransportEq",
            Self::TakeProp { .. } => "TakeProp",
            Self::ChoiceEq { .. } => "ChoiceEq",
            Self::SetExt { .. } => "SetExt",
            Self::FunExt { .. } => "FunExt",
            Self::ClassicalIndefiniteChoice { .. } => "ClassicalIndefiniteChoice",
            Self::Pred { .. } => "Pred",
            Self::Equal { .. } => "Equal",
            Self::Exists { .. } => "Exists",
            Self::ThunkValue { .. } => "ThunkValue",
            Self::ProgramContinue { .. } => "ProgramContinue",
            Self::ProgramFinish { .. } => "ProgramFinish",
            Self::InductiveConstructor { .. } => "InductiveConstructor",
            Self::Thunk { .. } => "Thunk",
            Self::ProgramRunStep { .. } => "ProgramRunStep",
            Self::Inductive { .. } => "Inductive",
            Self::Return { .. } => "Return",
            Self::Force { .. } => "Force",
            Self::Sequence { .. } => "Sequence",
            Self::ValueLet { .. } => "ValueLet",
            Self::ProgramCase { .. } => "ProgramCase",
            Self::Run { .. } => "Run",
            Self::RunCase { .. } => "RunCase",
            Self::ReturnType { .. } => "ReturnType",
        }
    }
}

#[cfg(test)]
mod intern_tests {
    use super::*;

    #[test]
    fn hash_collisions_preserve_handles_through_snapshot_and_rollback() {
        let mut hashes = FxHashMap::default();
        let (left, right) = (0..1_000_000)
            .find_map(|index| {
                hashes
                    .insert(Storage::hash(&Node::Bound(index)), index)
                    .map(|previous| (Node::Bound(previous), Node::Bound(index)))
            })
            .expect("collision in compact candidate keys");
        let arena = Arena::default();
        let first = arena.alloc(left.clone());
        let mark = arena.scratch_mark();
        let second = arena.alloc(right.clone());
        assert_ne!(first, second);
        assert_eq!(arena.alloc(left.clone()), first);
        assert_eq!(arena.alloc(right.clone()), second);
        let bytes = postcard::to_stdvec(&arena).unwrap();
        arena.rollback_import(mark);
        assert_eq!(arena.alloc(left.clone()), first);
        let restored: Arena = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(restored.alloc(left), first);
        assert_eq!(restored.alloc(right), second);
    }
}
