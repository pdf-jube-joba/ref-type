//! Shared PTS syntax for elaboration, unification, and checking.
use crate::ids::{DefinitionId, InductiveId, ParameterId, ProgramInductiveId, SymbolId};
use crate::sort::Sort;
use rustc_hash::FxHashMap;
use std::{cell::RefCell, rc::Rc};

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Expression(u32);
impl Expression {
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    Pure,
    Computation,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
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
        predicate: Expression,
        base: Expression,
        equality: Expression,
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
            Node::IndElim { scrutinee, motive, cases, .. } => {
                visit_slots!($visit; scrutinee, motive, ..cases,);
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
            Node::IdElim { left, right, ty, predicate, base, equality, .. } => {
                visit_slots!($visit; left, right, ty, predicate @ 1, base, equality,);
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
    fn try_for_each_child<E>(
        &self,
        mut visit: impl FnMut(Expression, usize) -> Result<(), E>,
    ) -> Result<(), E> {
        let mut slot = |child: &Expression, depth| visit(*child, depth);
        node_children!(self, slot);
        Ok(())
    }
}

#[derive(Debug, Default)]
struct Storage {
    nodes: Vec<Option<Rc<Node>>>,
    interned: FxHashMap<Rc<Node>, Expression>,
    properties: FxHashMap<Expression, (Option<usize>, bool)>,
}

#[derive(Debug, Clone, Default)]
pub struct Arena(Rc<RefCell<Storage>>);
impl Arena {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn alloc(&self, node: Node) -> Expression {
        let mut storage = self.0.borrow_mut();
        if let Some(&e) = storage.interned.get(&node) {
            return e;
        }
        let e = Expression(u32::try_from(storage.nodes.len()).expect("expression arena exhausted"));
        let node = Rc::new(node);
        storage.nodes.push(Some(node.clone()));
        storage.interned.insert(node, e);
        e
    }
    pub fn read(&self, e: Expression) -> Rc<Node> {
        self.0.borrow().nodes[e.index()]
            .as_ref()
            .expect("discarded scratch expression")
            .clone()
    }
    pub fn get(&self, e: Expression) -> Node {
        self.0.borrow().nodes[e.index()]
            .as_ref()
            .expect("discarded scratch expression")
            .as_ref()
            .clone()
    }
    pub fn len(&self) -> usize {
        self.0.borrow().interned.len()
    }
    pub(crate) fn scratch_mark(&self) -> usize {
        self.0.borrow().nodes.len()
    }
    pub(crate) fn is_live(&self, e: Expression) -> bool {
        self.0
            .borrow()
            .nodes
            .get(e.index())
            .is_some_and(Option::is_some)
    }
    pub(crate) fn finish_scratch(
        &self,
        mark: usize,
        roots: impl IntoIterator<Item = Expression>,
    ) -> usize {
        let mut pending = roots.into_iter().collect::<Vec<_>>();
        // A retained read snapshot also keeps its children alive.
        pending.extend(
            self.0
                .borrow()
                .nodes
                .iter()
                .enumerate()
                .skip(mark)
                .filter_map(|(i, n)| {
                    n.as_ref()
                        .filter(|n| Rc::strong_count(n) > 2)
                        .map(|_| Expression(i as u32))
                }),
        );
        let mut live = rustc_hash::FxHashSet::default();
        while let Some(e) = pending.pop() {
            if e.index() >= mark && live.insert(e) {
                pending.extend(self.children(e).into_iter().map(|(e, _)| e));
            }
        }
        let mut storage = self.0.borrow_mut();
        let mut removed = 0;
        for i in mark..storage.nodes.len() {
            let e = Expression(i as u32);
            if !live.contains(&e)
                && let Some(node) = storage.nodes[i].take()
            {
                storage.interned.remove(&node);
                storage.properties.remove(&e);
                removed += 1;
            }
        }
        removed
    }
    pub fn contains_meta(&self, e: Expression) -> bool {
        self.properties(e).1
    }
    pub fn max_loose_bound(&self, e: Expression) -> Option<usize> {
        self.properties(e).0
    }
    fn properties(&self, e: Expression) -> (Option<usize>, bool) {
        if let Some(&result) = self.0.borrow().properties.get(&e) {
            return result;
        }
        let node = self.read(e);
        let mut result = (
            if let Node::Bound(i) = *node {
                Some(i)
            } else {
                None
            },
            matches!(*node, Node::Meta { .. }),
        );
        let _: Result<(), std::convert::Infallible> = node.try_for_each_child(|child, depth| {
            let (bound, meta) = self.properties(child);
            if let Some(i) = bound.and_then(|i| i.checked_sub(depth)) {
                result.0 = Some(result.0.map_or(i, |old| old.max(i)));
            }
            result.1 |= meta;
            Ok(())
        });
        self.0.borrow_mut().properties.insert(e, result);
        result
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

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Binding {
    pub var: SymbolId,
    pub ty: Expression,
}
pub type Context = Vec<Binding>;

// Node indices remain stable across snapshots; interning tables are reconstructed.
impl serde::Serialize for Arena {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.borrow().nodes.serialize(serializer)
    }
}
impl<'de> serde::Deserialize<'de> for Arena {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let nodes = Vec::<Option<Rc<Node>>>::deserialize(deserializer)?;
        let mut interned = FxHashMap::default();
        for (index, node) in nodes.iter().enumerate() {
            if let Some(node) = node {
                let expression =
                    Expression(u32::try_from(index).map_err(serde::de::Error::custom)?);
                node.try_for_each_child(|child, _| {
                    if child.index() >= index
                        || !nodes.get(child.index()).is_some_and(Option::is_some)
                    {
                        return Err(serde::de::Error::custom("invalid arena reference"));
                    }
                    Ok(())
                })?;
                interned.insert(node.clone(), expression);
            }
        }
        Ok(Self(Rc::new(RefCell::new(Storage {
            nodes,
            interned,
            properties: FxHashMap::default(),
        }))))
    }
}
