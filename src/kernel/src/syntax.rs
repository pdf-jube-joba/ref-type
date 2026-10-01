//! Shared PTS syntax for elaboration, unification, and checking.
use crate::ids::{DefinitionId, InductiveId, ParameterId, ProgramInductiveId, SymbolId};
use crate::sort::Sort;
use rustc_hash::FxHashMap;
use std::{cell::RefCell, rc::Rc};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Expression(u32);
impl Expression {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MetaId {
    pub(crate) session: u64,
    pub(crate) index: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    Pure,
    Computation,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    TakeSet {
        domain: Expression,
        codomain: Expression,
        map: Expression,
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
    TakeEq {
        func: Expression,
        domain: Expression,
        codomain: Expression,
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
    AccIntro {
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        state: Expression,
        predecessors: Expression,
    },
    AccDescent {
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        from: Expression,
        to: Expression,
        accessibility: Expression,
        transition: Expression,
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
    Acc {
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        state: Expression,
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

#[derive(Debug, Default)]
struct Storage {
    nodes: Vec<Option<Rc<Node>>>,
    interned: FxHashMap<Rc<Node>, Expression>,
    bounds: FxHashMap<Expression, Option<usize>>,
    metas: FxHashMap<Expression, bool>,
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
        (*self.read(e)).clone()
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
                storage.bounds.remove(&e);
                storage.metas.remove(&e);
                removed += 1;
            }
        }
        removed
    }
    pub fn contains_meta(&self, e: Expression) -> bool {
        if let Some(&result) = self.0.borrow().metas.get(&e) {
            return result;
        }
        let result = matches!(self.get(e), Node::Meta { .. })
            || self
                .children(e)
                .into_iter()
                .any(|(e, _)| self.contains_meta(e));
        self.0.borrow_mut().metas.insert(e, result);
        result
    }
    pub fn max_loose_bound(&self, e: Expression) -> Option<usize> {
        if let Some(&result) = self.0.borrow().bounds.get(&e) {
            return result;
        }
        let mut result = match self.get(e) {
            Node::Bound(i) => Some(i),
            _ => None,
        };
        for (child, depth) in self.children(e) {
            if let Some(i) = self
                .max_loose_bound(child)
                .and_then(|i| i.checked_sub(depth))
            {
                result = Some(result.map_or(i, |old| old.max(i)));
            }
        }
        self.0.borrow_mut().bounds.insert(e, result);
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
        visit: impl FnMut(Expression, usize) -> Result<Expression, E>,
    ) -> Result<Expression, E> {
        let original = self.read(e);
        let node = self.map_node_children((*original).clone(), visit)?;
        Ok(if *original == node {
            e
        } else {
            self.alloc(node)
        })
    }
    pub fn map_node_children<E>(
        &self,
        mut node: Node,
        mut visit: impl FnMut(Expression, usize) -> Result<Expression, E>,
    ) -> Result<Node, E> {
        match &mut node {
            Node::Ascribe { term, ty } => {
                *term = visit(*term, 0)?;
                *ty = visit(*ty, 0)?;
            }
            Node::Sort(_) | Node::Bound(_) | Node::Parameter(_) => {}
            Node::Definition { arguments, .. } | Node::Meta { arguments, .. } => {
                for argument in arguments {
                    *argument = visit(*argument, 0)?;
                }
            }
            Node::Product { domain, body, .. } | Node::Lambda { domain, body, .. } => {
                *domain = visit(*domain, 0)?;
                *body = visit(*body, 1)?;
            }
            Node::App {
                function, argument, ..
            } => {
                *function = visit(*function, 0)?;
                *argument = visit(*argument, 0)?;
            }
            Node::Reflect { term } => {
                *term = visit(*term, 0)?;
            }
            Node::Subset { set, predicate, .. } => {
                *set = visit(*set, 0)?;
                *predicate = visit(*predicate, 1)?;
            }
            Node::SubsetIntro {
                superset,
                subset,
                element,
                proof,
                ..
            } => {
                *superset = visit(*superset, 0)?;
                *subset = visit(*subset, 0)?;
                *element = visit(*element, 0)?;
                *proof = visit(*proof, 0)?;
            }
            Node::Continue {
                state_ty,
                result_ty,
                next,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *next = visit(*next, 0)?;
            }
            Node::Finish {
                state_ty,
                result_ty,
                output,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *output = visit(*output, 0)?;
            }
            Node::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *step = visit(*step, 0)?;
                *initial = visit(*initial, 0)?;
                *accessibility = visit(*accessibility, 0)?;
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
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *step = visit(*step, 0)?;
                *initial = visit(*initial, 0)?;
                *transition = visit(*transition, 0)?;
                *accessibility = visit(*accessibility, 0)?;
                *transition_equality = visit(*transition_equality, 0)?;
            }
            Node::SetStepMatch {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *motive = visit(*motive, 0)?;
                *on_continue = visit(*on_continue, 0)?;
                *on_finish = visit(*on_finish, 0)?;
            }
            Node::ProgramStepMatch {
                state_ty,
                result_ty,
                computation_ty: motive,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *motive = visit(*motive, 0)?;
                *on_continue = visit(*on_continue, 0)?;
                *on_finish = visit(*on_finish, 0)?;
                *scrutinee = visit(*scrutinee, 0)?;
            }
            Node::BoxProgram {
                program_ty,
                program,
                ..
            } => {
                *program_ty = visit(*program_ty, 0)?;
                *program = visit(*program, 0)?;
            }
            Node::ForceBox {
                program_ty, boxed, ..
            } => {
                *program_ty = visit(*program_ty, 0)?;
                *boxed = visit(*boxed, 0)?;
            }
            Node::BoxApp { function, argument } => {
                *function = visit(*function, 0)?;
                *argument = visit(*argument, 0)?;
            }
            Node::BoxTypeApp { function, argument } => {
                *function = visit(*function, 0)?;
                *argument = visit(*argument, 0)?;
            }
            Node::TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
                ..
            } => {
                *domain = visit(*domain, 0)?;
                *codomain = visit(*codomain, 0)?;
                *map = visit(*map, 0)?;
                *existence = visit(*existence, 0)?;
                *uniqueness = visit(*uniqueness, 0)?;
            }
            Node::IndCtor { parameters, .. } => {
                for child in parameters {
                    *child = visit(*child, 0)?;
                }
            }
            Node::IndElim {
                scrutinee,
                motive,
                cases,
                ..
            } => {
                *scrutinee = visit(*scrutinee, 0)?;
                *motive = visit(*motive, 0)?;
                for child in cases {
                    *child = visit(*child, 0)?;
                }
            }
            Node::Case {
                scrutinee,
                motive,
                branches,
                ..
            } => {
                *scrutinee = visit(*scrutinee, 0)?;
                *motive = visit(*motive, 0)?;
                for child in branches {
                    *child = visit(*child, 0)?;
                }
            }
            Node::SetCase {
                scrutinee,
                branches,
                binders,
                ..
            } => {
                *scrutinee = visit(*scrutinee, 0)?;
                for (i, child) in branches.iter_mut().enumerate() {
                    *child = visit(*child, binders.get(i).map_or(0, Vec::len))?;
                }
            }
            Node::PowerSet { set, .. } => {
                *set = visit(*set, 0)?;
            }
            Node::TypeLift {
                superset, subset, ..
            } => {
                *superset = visit(*superset, 0)?;
                *subset = visit(*subset, 0)?;
            }
            Node::RunStep {
                state_ty,
                result_ty,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
            }
            Node::BoxType { program_ty, .. } => {
                *program_ty = visit(*program_ty, 0)?;
            }
            Node::IndType { parameters, .. } => {
                for child in parameters {
                    *child = visit(*child, 0)?;
                }
            }
            Node::IdRefl { element, .. } => {
                *element = visit(*element, 0)?;
            }
            Node::ExistsIntro { element, set, .. } => {
                *element = visit(*element, 0)?;
                *set = visit(*set, 0)?;
            }
            Node::SubsetElim {
                element,
                subset,
                superset,
                ..
            } => {
                *element = visit(*element, 0)?;
                *subset = visit(*subset, 0)?;
                *superset = visit(*superset, 0)?;
            }
            Node::IdElim {
                left,
                right,
                ty,
                predicate,
                base,
                equality,
                ..
            } => {
                *left = visit(*left, 0)?;
                *right = visit(*right, 0)?;
                *ty = visit(*ty, 0)?;
                *predicate = visit(*predicate, 1)?;
                *base = visit(*base, 0)?;
                *equality = visit(*equality, 0)?;
            }
            Node::TakeProp {
                domain,
                proposition,
                map,
                existence,
                ..
            } => {
                *domain = visit(*domain, 0)?;
                *proposition = visit(*proposition, 0)?;
                *map = visit(*map, 0)?;
                *existence = visit(*existence, 0)?;
            }
            Node::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
                ..
            } => {
                *func = visit(*func, 0)?;
                *domain = visit(*domain, 0)?;
                *codomain = visit(*codomain, 0)?;
                *element = visit(*element, 0)?;
                *existence = visit(*existence, 0)?;
                *uniqueness = visit(*uniqueness, 0)?;
            }
            Node::SetExt {
                left,
                right,
                left_to_right,
                right_to_left,
                ..
            } => {
                *left = visit(*left, 0)?;
                *right = visit(*right, 0)?;
                *left_to_right = visit(*left_to_right, 0)?;
                *right_to_left = visit(*right_to_left, 0)?;
            }
            Node::FunExt {
                left,
                right,
                pointwise,
                ..
            } => {
                *left = visit(*left, 0)?;
                *right = visit(*right, 0)?;
                *pointwise = visit(*pointwise, 0)?;
            }
            Node::ClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
                ..
            } => {
                *domain = visit(*domain, 0)?;
                *family = visit(*family, 0)?;
                *inhabited = visit(*inhabited, 0)?;
            }
            Node::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *step = visit(*step, 0)?;
                *state = visit(*state, 0)?;
                *predecessors = visit(*predecessors, 0)?;
            }
            Node::AccDescent {
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *step = visit(*step, 0)?;
                *from = visit(*from, 0)?;
                *to = visit(*to, 0)?;
                *accessibility = visit(*accessibility, 0)?;
                *transition = visit(*transition, 0)?;
            }
            Node::Pred {
                superset,
                subset,
                element,
                ..
            } => {
                *superset = visit(*superset, 0)?;
                *subset = visit(*subset, 0)?;
                *element = visit(*element, 0)?;
            }
            Node::Equal { left, right, .. } => {
                *left = visit(*left, 0)?;
                *right = visit(*right, 0)?;
            }
            Node::Exists { set, .. } => {
                *set = visit(*set, 0)?;
            }
            Node::Acc {
                state_ty,
                result_ty,
                step,
                state,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *step = visit(*step, 0)?;
                *state = visit(*state, 0)?;
            }
            Node::ThunkValue { computation, .. } => {
                *computation = visit(*computation, 0)?;
            }
            Node::ProgramContinue {
                state_ty,
                result_ty,
                next,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *next = visit(*next, 0)?;
            }
            Node::ProgramFinish {
                state_ty,
                result_ty,
                output,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *output = visit(*output, 0)?;
            }
            Node::InductiveConstructor {
                parameters, fields, ..
            } => {
                for child in parameters {
                    *child = visit(*child, 0)?;
                }
                for child in fields {
                    *child = visit(*child, 0)?;
                }
            }
            Node::Thunk { computation_ty, .. } => {
                *computation_ty = visit(*computation_ty, 0)?;
            }
            Node::ProgramRunStep {
                state_ty,
                result_ty,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
            }
            Node::Inductive { parameters, .. } => {
                for child in parameters {
                    *child = visit(*child, 0)?;
                }
            }
            Node::Return { value, .. } => {
                *value = visit(*value, 0)?;
            }
            Node::Force { value, .. } => {
                *value = visit(*value, 0)?;
            }
            Node::Sequence {
                value_ty,
                computation,
                body,
                ..
            } => {
                *value_ty = visit(*value_ty, 0)?;
                *computation = visit(*computation, 0)?;
                *body = visit(*body, 1)?;
            }
            Node::ValueLet {
                value_ty,
                value,
                body,
                ..
            } => {
                *value_ty = visit(*value_ty, 0)?;
                *value = visit(*value, 0)?;
                *body = visit(*body, 1)?;
            }
            Node::ProgramCase {
                scrutinee,
                branches,
                binders,
                ..
            } => {
                *scrutinee = visit(*scrutinee, 0)?;
                for (i, child) in branches.iter_mut().enumerate() {
                    *child = visit(*child, binders.get(i).map_or(0, Vec::len))?;
                }
            }
            Node::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *step = visit(*step, 0)?;
                *initial = visit(*initial, 0)?;
                *accessibility = visit(*accessibility, 0)?;
            }
            Node::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
                ..
            } => {
                *state_ty = visit(*state_ty, 0)?;
                *result_ty = visit(*result_ty, 0)?;
                *step = visit(*step, 0)?;
                *initial = visit(*initial, 0)?;
                *transition = visit(*transition, 0)?;
                *accessibility = visit(*accessibility, 0)?;
                *transition_equality = visit(*transition_equality, 0)?;
            }
            Node::ReturnType { value_ty, .. } => {
                *value_ty = visit(*value_ty, 0)?;
            }
        }
        Ok(node)
    }

    pub fn children(&self, e: Expression) -> Vec<(Expression, usize)> {
        let mut children = Vec::new();
        let _: Result<_, std::convert::Infallible> = self.map_children(e, |child, depth| {
            children.push((child, depth));
            Ok(child)
        });
        children
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Binding {
    pub var: SymbolId,
    pub ty: Expression,
}
pub type Context = Vec<Binding>;
