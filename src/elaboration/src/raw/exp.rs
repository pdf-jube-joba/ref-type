//! Source-facing views and provenance for the shared kernel expression arena.

use super::traversal::Term;
use rustc_hash::FxHashMap;
use std::{cell::RefCell, rc::Rc};

use crate::raw::{
    ids::{DefId, InductiveId, MetaVarId, ModuleParamId, ProgramInductiveId, SymbolId},
    program::{
        ComputationTerm, ComputationTermNode, ComputationType, ComputationTypeNode, ValueTerm,
        ValueTermNode, ValueType, ValueTypeNode,
    },
    sort::Sort,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Exp(pub(crate) kernel::syntax::Expression);

impl Exp {}

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Atom {
    Definition(DefId),
    Instance(DefId),
    Meta(u8, MetaVarId, Vec<bool>),
}
#[derive(Debug, Default)]
struct Atoms {
    ids: FxHashMap<Atom, kernel::syntax::MetaId>,
    keys: FxHashMap<kernel::syntax::MetaId, Atom>,
    allocator: kernel::metavariables::MetaContext,
}
#[derive(Debug, Clone)]
struct DefinitionView {
    source: Option<DefId>,
    captures: Vec<ModuleParamId>,
    body: kernel::syntax::Expression,
}
/// The frontend uses the kernel DAG. Names awaiting resolution are frontend-owned atoms.
#[derive(Debug, Default)]
pub struct Arena {
    pub(crate) core: kernel::syntax::Arena,
    atoms: RefCell<Atoms>,
    loose_bounds: RefCell<FxHashMap<Term, Option<usize>>>,
    pub(crate) datatype_reflections:
        RefCell<FxHashMap<kernel::ids::ProgramInductiveId, kernel::ids::InductiveId>>,
    pub(crate) inductive_captures: RefCell<FxHashMap<kernel::ids::InductiveId, (usize, usize)>>,
    definitions: RefCell<FxHashMap<kernel::ids::DefinitionId, DefinitionView>>,
}
impl Arena {
    pub fn new() -> Self {
        Self::default()
    }
    fn source_inductive_parameters(
        &self,
        id: kernel::ids::InductiveId,
        parameters: Vec<kernel::syntax::Expression>,
    ) -> Vec<Exp> {
        let skip = self
            .inductive_captures
            .borrow()
            .get(&id)
            .filter(|(captures, explicit)| {
                *captures + *explicit == parameters.len()
                    && parameters[..*captures]
                        .iter()
                        .all(|&e| matches!(self.core.get(e), kernel::syntax::Node::Parameter(_)))
            })
            .map_or(0, |(captures, _)| *captures);
        parameters.into_iter().skip(skip).map(Exp).collect()
    }
    pub(crate) fn bind_definition(
        &self,
        id: kernel::ids::DefinitionId,
        source: Option<DefId>,
        captures: Vec<ModuleParamId>,
        body: kernel::syntax::Expression,
    ) {
        self.definitions.borrow_mut().insert(
            id,
            DefinitionView {
                source,
                captures,
                body,
            },
        );
    }
    pub(crate) fn definition_captures(
        &self,
        id: kernel::ids::DefinitionId,
    ) -> Option<Vec<ModuleParamId>> {
        self.definitions
            .borrow()
            .get(&id)
            .map(|view| view.captures.clone())
    }
    pub(crate) fn bind_meta(&self, source: MetaVarId, id: kernel::syntax::MetaId) {
        self.bind_program_meta(source, id, 0, vec![]);
    }
    pub(crate) fn bind_program_meta(
        &self,
        source: MetaVarId,
        id: kernel::syntax::MetaId,
        category: u8,
        kinds: Vec<bool>,
    ) {
        let key = Atom::Meta(category, source, kinds);
        let mut atoms = self.atoms.borrow_mut();
        atoms.ids.insert(key.clone(), id);
        atoms.keys.insert(id, key);
    }
    pub(crate) fn definition_body(
        &self,
        id: kernel::ids::DefinitionId,
    ) -> kernel::syntax::Expression {
        self.definitions
            .borrow()
            .get(&id)
            .expect("source definition")
            .body
    }
    fn reference_view(
        &self,
        id: kernel::ids::DefinitionId,
        arguments: Vec<kernel::syntax::Expression>,
        program: bool,
    ) -> kernel::syntax::Expression {
        let view = self
            .definitions
            .borrow()
            .get(&id)
            .expect("definition has frontend provenance")
            .clone();
        let nominal = arguments.len() >= view.captures.len()
            && arguments
                .iter()
                .zip(&view.captures)
                .all(|(&e, &id)| match self.core.get(e) {
                    N::Parameter(actual) => actual == id.into(),
                    N::Reflect { term } => {
                        matches!(self.core.get(term),N::Parameter(actual) if actual==id.into())
                    }
                    _ => false,
                });
        if nominal && let Some(source) = view.source {
            let parameters = arguments[view.captures.len()..].to_vec();
            if program && !parameters.is_empty() {
                return self.atom(Atom::Instance(source), parameters);
            }
            let mut result = self.atom(Atom::Definition(source), vec![]);
            for argument in parameters {
                result = self.core.alloc(N::App {
                    mode: Mode::Pure,
                    function: result,
                    argument,
                });
            }
            return result;
        }
        kernel::calculus::instantiate(&self.core, view.body, &arguments)
            .expect("validated definition arguments")
    }
    fn atom(
        &self,
        key: Atom,
        arguments: Vec<kernel::syntax::Expression>,
    ) -> kernel::syntax::Expression {
        let mut atoms = self.atoms.borrow_mut();
        let id = if let Some(&id) = atoms.ids.get(&key) {
            id
        } else {
            let e = atoms.allocator.fresh(&self.core, vec![], None);
            let kernel::syntax::Node::Meta { id, .. } = self.core.get(e) else {
                unreachable!()
            };
            atoms.ids.insert(key.clone(), id);
            atoms.keys.insert(id, key);
            id
        };
        self.core
            .alloc(kernel::syntax::Node::Meta { id, arguments })
    }
    pub(crate) fn atom_key(&self, id: kernel::syntax::MetaId) -> Atom {
        self.atoms
            .borrow()
            .keys
            .get(&id)
            .expect("frontend atom")
            .clone()
    }
    pub fn alloc<N: ArenaNode>(&self, node: N) -> N::Handle {
        node.allocate(self)
    }
    pub fn get<H: ArenaHandle>(&self, handle: H) -> H::Node {
        handle.get(self)
    }
    pub(crate) fn max_loose_bound(&self, term: Term) -> Option<usize> {
        if let Some(&max) = self.loose_bounds.borrow().get(&term) {
            return max;
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
        self.loose_bounds.borrow_mut().insert(term, result);
        result
    }
    pub fn node_counts(&self) -> [(&'static str, usize); 1] {
        [("Expression", self.core.len())]
    }
    #[cfg(test)]
    pub(crate) fn exp_len(&self) -> usize {
        self.core.len()
    }
    pub(crate) fn reuse_exp(&self, original: Exp, node: ExpNode) -> Exp {
        if self.get(original) == node {
            original
        } else {
            self.alloc(node)
        }
    }
    pub(crate) fn borrow_exp(&self, e: Exp) -> Rc<ExpNode> {
        Rc::new(self.get(e))
    }
    pub(crate) fn reuse_value_type(&self, original: ValueType, node: ValueTypeNode) -> ValueType {
        if self.get(original) == node {
            original
        } else {
            self.alloc(node)
        }
    }
    pub(crate) fn borrow_value_type(&self, e: ValueType) -> Rc<ValueTypeNode> {
        Rc::new(self.get(e))
    }
    pub(crate) fn reuse_computation_type(
        &self,
        original: ComputationType,
        node: ComputationTypeNode,
    ) -> ComputationType {
        if self.get(original) == node {
            original
        } else {
            self.alloc(node)
        }
    }
    pub(crate) fn reuse_value(&self, original: ValueTerm, node: ValueTermNode) -> ValueTerm {
        if self.get(original) == node {
            original
        } else {
            self.alloc(node)
        }
    }
    pub(crate) fn borrow_value(&self, e: ValueTerm) -> Rc<ValueTermNode> {
        Rc::new(self.get(e))
    }
    pub(crate) fn reuse_computation(
        &self,
        original: ComputationTerm,
        node: ComputationTermNode,
    ) -> ComputationTerm {
        if self.get(original) == node {
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

use kernel::syntax::{Mode, Node as N};
impl ArenaNode for ExpNode {
    type Handle = Exp;
    fn allocate(self, arena: &Arena) -> Exp {
        let node = match self {
            ExpNode::Prod { var, ty, body } => N::Product {
                var,
                domain: ty.0,
                body: body.0,
            },
            ExpNode::Lam { var, ty, body } => N::Lambda {
                var,
                domain: ty.0,
                body: body.0,
                mode: Mode::Pure,
            },
            ExpNode::App { func, arg } => N::App {
                function: func.0,
                argument: arg.0,
                mode: Mode::Pure,
            },
            ExpNode::IndType {
                indspec,
                parameters,
            } => N::IndType {
                inductive: indspec.into(),
                parameters: parameters.into_iter().map(|e| e.0).collect(),
            },
            ExpNode::IndCtor {
                indspec,
                parameters,
                idx,
            } => N::IndCtor {
                inductive: indspec.into(),
                parameters: parameters.into_iter().map(|e| e.0).collect(),
                constructor: idx,
            },
            ExpNode::IndElim {
                indspec,
                elim,
                return_type,
                cases,
            } => N::IndElim {
                inductive: indspec.into(),
                scrutinee: elim.0,
                motive: return_type.0,
                cases: cases.into_iter().map(|e| e.0).collect(),
            },
            ExpNode::IndCase {
                indspec,
                scrutinee,
                return_type,
                branches,
            } => N::Case {
                inductive: indspec.into(),
                scrutinee: scrutinee.0,
                motive: return_type.0,
                branches: branches.into_iter().map(|e| e.0).collect(),
            },
            ExpNode::RunStep {
                state_ty,
                result_ty,
            } => N::RunStep {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
            },
            ExpNode::Continue {
                state_ty,
                result_ty,
                next,
            } => N::Continue {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
                next: next.0,
            },
            ExpNode::Finish {
                state_ty,
                result_ty,
                output,
            } => N::Finish {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
                output: output.0,
            },
            ExpNode::Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => N::Acc {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
                step: step.0,
                state: state.0,
            },
            ExpNode::RunStepRec {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => N::Recursor {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
                motive: motive.0,
                on_continue: on_continue.0,
                on_finish: on_finish.0,
                scrutinee: scrutinee.0,
            },
            ExpNode::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => N::SetRun {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
                step: step.0,
                initial: initial.0,
                accessibility: accessibility.0,
            },
            ExpNode::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => N::SetRunCase {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
                step: step.0,
                initial: initial.0,
                transition: transition.0,
                accessibility: accessibility.0,
                transition_equality: transition_equality.0,
            },
            ExpNode::BoxType { program_ty } => N::BoxType {
                program_ty: program_ty.0,
            },
            ExpNode::BoxProgram {
                program_ty,
                program,
            } => N::BoxProgram {
                program_ty: program_ty.0,
                program: program.0,
            },
            ExpNode::ForceBox { program_ty, boxed } => N::ForceBox {
                program_ty: program_ty.0,
                boxed: boxed.0,
            },
            ExpNode::BoxApp { function, argument } => N::BoxApp {
                function: function.0,
                argument: argument.0,
            },
            ExpNode::PowerSet { set } => N::PowerSet { set: set.0 },
            ExpNode::SubSet {
                var,
                set,
                predicate,
            } => N::Subset {
                var,
                set: set.0,
                predicate: predicate.0,
            },
            ExpNode::Pred {
                superset,
                subset,
                element,
            } => N::Pred {
                superset: superset.0,
                subset: subset.0,
                element: element.0,
            },
            ExpNode::TypeLift { superset, subset } => N::TypeLift {
                superset: superset.0,
                subset: subset.0,
            },
            ExpNode::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => N::SubsetIntro {
                superset: superset.0,
                subset: subset.0,
                element: element.0,
                proof: proof.0,
            },
            ExpNode::Equal { left, right } => N::Equal {
                left: left.0,
                right: right.0,
            },
            ExpNode::Exists { set } => N::Exists { set: set.0 },
            ExpNode::TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
            } => N::TakeSet {
                domain: domain.0,
                codomain: codomain.0,
                map: map.0,
                existence: existence.0,
                uniqueness: uniqueness.0,
            },
            ExpNode::TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => N::TakeProp {
                domain: domain.0,
                proposition: proposition.0,
                map: map.0,
                existence: existence.0,
            },
            ExpNode::Meta {
                metavariable,
                spine,
            } => {
                return Exp(arena.atom(
                    Atom::Meta(0, metavariable, vec![]),
                    spine.into_iter().map(|e| e.0).collect(),
                ));
            }
            ExpNode::Bound(i) => N::Bound(i),
            ExpNode::ModuleParam(id) => N::Parameter(id.into()),
            ExpNode::DefinedConstant(id) => return Exp(arena.atom(Atom::Definition(id), vec![])),
            ExpNode::Sort(sort) => N::Sort(lower_sort(sort)),
            ExpNode::ReflectedProgramParam(id) => N::Reflect {
                term: arena.core.alloc(N::Parameter(id.into())),
            },
            ExpNode::Prove(proof) => lower_proof(proof),
            ExpNode::ReflectedProgramCase {
                indspec,
                scrutinee,
                branches,
            } => N::SetCase {
                inductive: indspec.into(),
                scrutinee: scrutinee.0,
                binders: branches.iter().map(|b| b.binders.clone()).collect(),
                branches: branches.into_iter().map(|b| b.body.0).collect(),
            },
        };
        Exp(arena.core.alloc(node))
    }
}
impl ArenaHandle for Exp {
    type Node = ExpNode;
    fn get(self, arena: &Arena) -> ExpNode {
        match arena.core.get(self.0) {
            N::Definition { id, arguments } => {
                Exp(arena.reference_view(id, arguments, false)).get(arena)
            }
            N::Product {
                var, domain, body, ..
            } => ExpNode::Prod {
                var,
                ty: Exp(domain),
                body: Exp(body),
            },
            N::Lambda {
                var, domain, body, ..
            } => ExpNode::Lam {
                var,
                ty: Exp(domain),
                body: Exp(body),
            },
            N::App {
                function, argument, ..
            } => ExpNode::App {
                func: Exp(function),
                arg: Exp(argument),
            },
            N::IndType {
                inductive,
                parameters,
                ..
            } => ExpNode::IndType {
                indspec: InductiveId {
                    module: crate::raw::ids::ModuleId((inductive.0 >> 32) as u32),
                    index: inductive.0 as u32,
                },
                parameters: arena.source_inductive_parameters(inductive, parameters),
            },
            N::IndCtor {
                inductive,
                parameters,
                constructor,
                ..
            } => ExpNode::IndCtor {
                indspec: InductiveId {
                    module: crate::raw::ids::ModuleId((inductive.0 >> 32) as u32),
                    index: inductive.0 as u32,
                },
                parameters: arena.source_inductive_parameters(inductive, parameters),
                idx: constructor,
            },
            N::IndElim {
                inductive,
                scrutinee,
                motive,
                cases,
                ..
            } => ExpNode::IndElim {
                indspec: InductiveId {
                    module: crate::raw::ids::ModuleId((inductive.0 >> 32) as u32),
                    index: inductive.0 as u32,
                },
                elim: Exp(scrutinee),
                return_type: Exp(motive),
                cases: cases.into_iter().map(Exp).collect(),
            },
            N::Case {
                inductive,
                scrutinee,
                motive,
                branches,
                ..
            } => ExpNode::IndCase {
                indspec: InductiveId {
                    module: crate::raw::ids::ModuleId((inductive.0 >> 32) as u32),
                    index: inductive.0 as u32,
                },
                scrutinee: Exp(scrutinee),
                return_type: Exp(motive),
                branches: branches.into_iter().map(Exp).collect(),
            },
            N::RunStep {
                state_ty,
                result_ty,
                ..
            } => ExpNode::RunStep {
                state_ty: Exp(state_ty),
                result_ty: Exp(result_ty),
            },
            N::Continue {
                state_ty,
                result_ty,
                next,
                ..
            } => ExpNode::Continue {
                state_ty: Exp(state_ty),
                result_ty: Exp(result_ty),
                next: Exp(next),
            },
            N::Finish {
                state_ty,
                result_ty,
                output,
                ..
            } => ExpNode::Finish {
                state_ty: Exp(state_ty),
                result_ty: Exp(result_ty),
                output: Exp(output),
            },
            N::Acc {
                state_ty,
                result_ty,
                step,
                state,
                ..
            } => ExpNode::Acc {
                state_ty: Exp(state_ty),
                result_ty: Exp(result_ty),
                step: Exp(step),
                state: Exp(state),
            },
            N::Recursor {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
                ..
            } => ExpNode::RunStepRec {
                state_ty: Exp(state_ty),
                result_ty: Exp(result_ty),
                motive: Exp(motive),
                on_continue: Exp(on_continue),
                on_finish: Exp(on_finish),
                scrutinee: Exp(scrutinee),
            },
            N::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
                ..
            } => ExpNode::SetRun {
                state_ty: Exp(state_ty),
                result_ty: Exp(result_ty),
                step: Exp(step),
                initial: Exp(initial),
                accessibility: Exp(accessibility),
            },
            N::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
                ..
            } => ExpNode::SetRunCase {
                state_ty: Exp(state_ty),
                result_ty: Exp(result_ty),
                step: Exp(step),
                initial: Exp(initial),
                transition: Exp(transition),
                accessibility: Exp(accessibility),
                transition_equality: Exp(transition_equality),
            },
            N::BoxType { program_ty, .. } => ExpNode::BoxType {
                program_ty: ComputationType(program_ty),
            },
            N::BoxProgram {
                program_ty,
                program,
                ..
            } => ExpNode::BoxProgram {
                program_ty: ComputationType(program_ty),
                program: ComputationTerm(program),
            },
            N::ForceBox {
                program_ty, boxed, ..
            } => ExpNode::ForceBox {
                program_ty: ComputationType(program_ty),
                boxed: Exp(boxed),
            },
            N::BoxApp {
                function, argument, ..
            } => ExpNode::BoxApp {
                function: Exp(function),
                argument: Exp(argument),
            },
            N::PowerSet { set, .. } => ExpNode::PowerSet { set: Exp(set) },
            N::Subset {
                var,
                set,
                predicate,
                ..
            } => ExpNode::SubSet {
                var,
                set: Exp(set),
                predicate: Exp(predicate),
            },
            N::Pred {
                superset,
                subset,
                element,
                ..
            } => ExpNode::Pred {
                superset: Exp(superset),
                subset: Exp(subset),
                element: Exp(element),
            },
            N::TypeLift {
                superset, subset, ..
            } => ExpNode::TypeLift {
                superset: Exp(superset),
                subset: Exp(subset),
            },
            N::SubsetIntro {
                superset,
                subset,
                element,
                proof,
                ..
            } => ExpNode::SubsetIntro {
                superset: Exp(superset),
                subset: Exp(subset),
                element: Exp(element),
                proof: Exp(proof),
            },
            N::Equal { left, right, .. } => ExpNode::Equal {
                left: Exp(left),
                right: Exp(right),
            },
            N::Exists { set, .. } => ExpNode::Exists { set: Exp(set) },
            N::TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
                ..
            } => ExpNode::TakeSet {
                domain: Exp(domain),
                codomain: Exp(codomain),
                map: Exp(map),
                existence: Exp(existence),
                uniqueness: Exp(uniqueness),
            },
            N::TakeProp {
                domain,
                proposition,
                map,
                existence,
                ..
            } => ExpNode::TakeProp {
                domain: Exp(domain),
                proposition: Exp(proposition),
                map: Exp(map),
                existence: Exp(existence),
            },
            N::Meta { id, arguments } => match arena.atom_key(id) {
                Atom::Definition(id) => ExpNode::DefinedConstant(id),
                Atom::Meta(_, metavariable, _) => ExpNode::Meta {
                    metavariable,
                    spine: arguments.into_iter().map(Exp).collect(),
                },
                _ => panic!("logical atom category"),
            },
            N::Parameter(id) => ExpNode::ModuleParam(id.into()),
            N::Bound(i) => ExpNode::Bound(i),
            N::Sort(sort) => ExpNode::Sort(raise_sort(sort)),
            N::Reflect { term } => match arena.core.get(term) {
                N::Parameter(id) => ExpNode::ReflectedProgramParam(id.into()),
                N::Bound(i) => ExpNode::Bound(i),
                _ => Exp(kernel::reflection::Reflection::new(arena)
                    .reflect_bound(term)
                    .expect("resolved reflection"))
                .get(arena),
            },
            N::SetCase {
                inductive,
                scrutinee,
                binders,
                branches,
            } => ExpNode::ReflectedProgramCase {
                indspec: ProgramInductiveId {
                    module: crate::raw::ids::ModuleId((inductive.0 >> 32) as u32),
                    index: inductive.0 as u32,
                },
                scrutinee: Exp(scrutinee),
                branches: branches
                    .into_iter()
                    .zip(binders)
                    .map(|(body, binders)| ReflectedProgramCaseBranch {
                        binders,
                        body: Exp(body),
                    })
                    .collect(),
            },
            node => ExpNode::Prove(raise_proof(node)),
        }
    }
}
impl ArenaNode for ValueTypeNode {
    type Handle = ValueType;
    fn allocate(self, arena: &Arena) -> ValueType {
        let node = match self {
            ValueTypeNode::Thunk { computation_ty } => N::Thunk {
                computation_ty: computation_ty.0,
            },
            ValueTypeNode::RunStep {
                state_ty,
                result_ty,
            } => N::ProgramRunStep {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
            },
            ValueTypeNode::Inductive {
                indspec,
                parameters,
            } => N::Inductive {
                inductive: indspec.into(),
                parameters: parameters.into_iter().map(|e| e.0).collect(),
            },
            ValueTypeNode::Meta {
                metavariable,
                spine,
            } => {
                let kinds = spine
                    .iter()
                    .map(|a| matches!(a, super::program::ProgramArgument::ValueType(_)))
                    .collect();
                let args = spine
                    .into_iter()
                    .map(|a| match a {
                        super::program::ProgramArgument::ValueType(e) => e.0,
                        super::program::ProgramArgument::ValueTerm(e) => e.0,
                    })
                    .collect();
                return ValueType(arena.atom(Atom::Meta(1, metavariable, kinds), args));
            }
            ValueTypeNode::Bound(i) => N::Bound(i),
            ValueTypeNode::ModuleParam(id) => N::Parameter(id.into()),
        };
        ValueType(arena.core.alloc(node))
    }
}
impl ArenaHandle for ValueType {
    type Node = ValueTypeNode;
    fn get(self, arena: &Arena) -> ValueTypeNode {
        match arena.core.get(self.0) {
            N::Definition { id, arguments } => {
                ValueType(arena.reference_view(id, arguments, true)).get(arena)
            }
            N::Thunk { computation_ty, .. } => ValueTypeNode::Thunk {
                computation_ty: ComputationType(computation_ty),
            },
            N::ProgramRunStep {
                state_ty,
                result_ty,
                ..
            } => ValueTypeNode::RunStep {
                state_ty: ValueType(state_ty),
                result_ty: ValueType(result_ty),
            },
            N::Inductive {
                inductive,
                parameters,
                ..
            } => ValueTypeNode::Inductive {
                indspec: ProgramInductiveId {
                    module: crate::raw::ids::ModuleId((inductive.0 >> 32) as u32),
                    index: inductive.0 as u32,
                },
                parameters: parameters.into_iter().map(ValueType).collect(),
            },
            N::Meta { id, arguments } => match arena.atom_key(id) {
                Atom::Meta(_, metavariable, kinds) => ValueTypeNode::Meta {
                    metavariable,
                    spine: arguments
                        .into_iter()
                        .zip(kinds)
                        .map(|(e, ty)| {
                            if ty {
                                super::program::ProgramArgument::ValueType(ValueType(e))
                            } else {
                                super::program::ProgramArgument::ValueTerm(ValueTerm(e))
                            }
                        })
                        .collect(),
                },
                _ => panic!("Program atom category"),
            },
            N::Parameter(id) => ValueTypeNode::ModuleParam(id.into()),
            N::Bound(i) => ValueTypeNode::Bound(i),
            node => panic!("incorrect frontend Program view: {node:?}"),
        }
    }
}
impl ArenaNode for ComputationTypeNode {
    type Handle = ComputationType;
    fn allocate(self, arena: &Arena) -> ComputationType {
        let node = match self {
            ComputationTypeNode::Return { value_ty } => N::ReturnType {
                value_ty: value_ty.0,
            },
            ComputationTypeNode::Meta {
                metavariable,
                spine,
            } => {
                let kinds = spine
                    .iter()
                    .map(|a| matches!(a, super::program::ProgramArgument::ValueType(_)))
                    .collect();
                let args = spine
                    .into_iter()
                    .map(|a| match a {
                        super::program::ProgramArgument::ValueType(e) => e.0,
                        super::program::ProgramArgument::ValueTerm(e) => e.0,
                    })
                    .collect();
                return ComputationType(arena.atom(Atom::Meta(2, metavariable, kinds), args));
            }
            ComputationTypeNode::Function { domain, codomain } => N::Product {
                var: SymbolId::ANONYMOUS,
                domain: domain.0,
                body: kernel::calculus::shift(&arena.core, codomain.0, 1, 0).unwrap(),
            },
        };
        ComputationType(arena.core.alloc(node))
    }
}
impl ArenaHandle for ComputationType {
    type Node = ComputationTypeNode;
    fn get(self, arena: &Arena) -> ComputationTypeNode {
        match arena.core.get(self.0) {
            N::Definition { id, arguments } => {
                ComputationType(arena.reference_view(id, arguments, true)).get(arena)
            }
            N::ReturnType { value_ty, .. } => ComputationTypeNode::Return {
                value_ty: ValueType(value_ty),
            },
            N::Meta { id, arguments } => match arena.atom_key(id) {
                Atom::Meta(_, metavariable, kinds) => ComputationTypeNode::Meta {
                    metavariable,
                    spine: arguments
                        .into_iter()
                        .zip(kinds)
                        .map(|(e, ty)| {
                            if ty {
                                super::program::ProgramArgument::ValueType(ValueType(e))
                            } else {
                                super::program::ProgramArgument::ValueTerm(ValueTerm(e))
                            }
                        })
                        .collect(),
                },
                _ => panic!("Program atom category"),
            },
            N::Product { domain, body, .. } => ComputationTypeNode::Function {
                domain: ValueType(domain),
                codomain: ComputationType(
                    kernel::calculus::instantiate(&arena.core, body, &[arena.core.bound(0)])
                        .unwrap(),
                ),
            },
            node => panic!("incorrect frontend Program view: {node:?}"),
        }
    }
}
impl ArenaNode for ValueTermNode {
    type Handle = ValueTerm;
    fn allocate(self, arena: &Arena) -> ValueTerm {
        let node = match self {
            ValueTermNode::Thunk { computation } => N::ThunkValue {
                computation: computation.0,
            },
            ValueTermNode::Continue {
                state_ty,
                result_ty,
                next,
            } => N::ProgramContinue {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
                next: next.0,
            },
            ValueTermNode::Finish {
                state_ty,
                result_ty,
                output,
            } => N::ProgramFinish {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
                output: output.0,
            },
            ValueTermNode::InductiveConstructor {
                indspec,
                parameters,
                idx,
                fields,
            } => N::InductiveConstructor {
                inductive: indspec.into(),
                parameters: parameters.into_iter().map(|e| e.0).collect(),
                constructor: idx,
                fields: fields.into_iter().map(|e| e.0).collect(),
            },
            ValueTermNode::Meta {
                metavariable,
                spine,
            } => {
                let kinds = spine
                    .iter()
                    .map(|a| matches!(a, super::program::ProgramArgument::ValueType(_)))
                    .collect();
                let args = spine
                    .into_iter()
                    .map(|a| match a {
                        super::program::ProgramArgument::ValueType(e) => e.0,
                        super::program::ProgramArgument::ValueTerm(e) => e.0,
                    })
                    .collect();
                return ValueTerm(arena.atom(Atom::Meta(3, metavariable, kinds), args));
            }
            ValueTermNode::Bound(i) => N::Bound(i),
            ValueTermNode::ModuleParam(id) => N::Parameter(id.into()),
            ValueTermNode::DefinedConstant(id) => {
                return ValueTerm(arena.atom(Atom::Definition(id), vec![]));
            }
            ValueTermNode::DefinitionInstance {
                definition,
                parameters,
            } => {
                return ValueTerm(arena.atom(
                    Atom::Instance(definition),
                    parameters.into_iter().map(|e| e.0).collect(),
                ));
            }
        };
        ValueTerm(arena.core.alloc(node))
    }
}
impl ArenaHandle for ValueTerm {
    type Node = ValueTermNode;
    fn get(self, arena: &Arena) -> ValueTermNode {
        match arena.core.get(self.0) {
            N::Definition { id, arguments } => {
                ValueTerm(arena.reference_view(id, arguments, true)).get(arena)
            }
            N::ThunkValue { computation, .. } => ValueTermNode::Thunk {
                computation: ComputationTerm(computation),
            },
            N::ProgramContinue {
                state_ty,
                result_ty,
                next,
                ..
            } => ValueTermNode::Continue {
                state_ty: ValueType(state_ty),
                result_ty: ValueType(result_ty),
                next: ValueTerm(next),
            },
            N::ProgramFinish {
                state_ty,
                result_ty,
                output,
                ..
            } => ValueTermNode::Finish {
                state_ty: ValueType(state_ty),
                result_ty: ValueType(result_ty),
                output: ValueTerm(output),
            },
            N::InductiveConstructor {
                inductive,
                parameters,
                constructor,
                fields,
                ..
            } => ValueTermNode::InductiveConstructor {
                indspec: ProgramInductiveId {
                    module: crate::raw::ids::ModuleId((inductive.0 >> 32) as u32),
                    index: inductive.0 as u32,
                },
                parameters: parameters.into_iter().map(ValueType).collect(),
                idx: constructor,
                fields: fields.into_iter().map(ValueTerm).collect(),
            },
            N::Meta { id, arguments } => match arena.atom_key(id) {
                Atom::Meta(_, metavariable, kinds) => ValueTermNode::Meta {
                    metavariable,
                    spine: arguments
                        .into_iter()
                        .zip(kinds)
                        .map(|(e, ty)| {
                            if ty {
                                super::program::ProgramArgument::ValueType(ValueType(e))
                            } else {
                                super::program::ProgramArgument::ValueTerm(ValueTerm(e))
                            }
                        })
                        .collect(),
                },
                Atom::Definition(id) => ValueTermNode::DefinedConstant(id),
                Atom::Instance(definition) => ValueTermNode::DefinitionInstance {
                    definition,
                    parameters: arguments.into_iter().map(ValueType).collect(),
                },
            },
            N::Parameter(id) => ValueTermNode::ModuleParam(id.into()),
            N::Bound(i) => ValueTermNode::Bound(i),
            node => panic!("incorrect frontend Program view: {node:?}"),
        }
    }
}
impl ArenaNode for ComputationTermNode {
    type Handle = ComputationTerm;
    fn allocate(self, arena: &Arena) -> ComputationTerm {
        let node = match self {
            ComputationTermNode::Return { value } => N::Return { value: value.0 },
            ComputationTermNode::Force { value } => N::Force { value: value.0 },
            ComputationTermNode::Lambda {
                var,
                value_ty,
                body,
            } => N::Lambda {
                var,
                domain: value_ty.0,
                body: body.0,
                mode: Mode::Computation,
            },
            ComputationTermNode::Application { computation, value } => N::App {
                function: computation.0,
                argument: value.0,
                mode: Mode::Computation,
            },
            ComputationTermNode::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => N::Sequence {
                computation: computation.0,
                var,
                value_ty: value_ty.0,
                body: body.0,
            },
            ComputationTermNode::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => N::ValueLet {
                var,
                value_ty: value_ty.0,
                value: value.0,
                body: body.0,
            },
            ComputationTermNode::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => N::Run {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
                step: step.0,
                initial: initial.0,
                accessibility: accessibility.0,
            },
            ComputationTermNode::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => N::RunCase {
                state_ty: state_ty.0,
                result_ty: result_ty.0,
                step: step.0,
                initial: initial.0,
                transition: transition.0,
                accessibility: accessibility.0,
                transition_equality: transition_equality.0,
            },
            ComputationTermNode::Meta {
                metavariable,
                spine,
            } => {
                let kinds = spine
                    .iter()
                    .map(|a| matches!(a, super::program::ProgramArgument::ValueType(_)))
                    .collect();
                let args = spine
                    .into_iter()
                    .map(|a| match a {
                        super::program::ProgramArgument::ValueType(e) => e.0,
                        super::program::ProgramArgument::ValueTerm(e) => e.0,
                    })
                    .collect();
                return ComputationTerm(arena.atom(Atom::Meta(4, metavariable, kinds), args));
            }
            ComputationTermNode::DefinedConstant(id) => {
                return ComputationTerm(arena.atom(Atom::Definition(id), vec![]));
            }
            ComputationTermNode::DefinitionInstance {
                definition,
                parameters,
            } => {
                return ComputationTerm(arena.atom(
                    Atom::Instance(definition),
                    parameters.into_iter().map(|e| e.0).collect(),
                ));
            }
            ComputationTermNode::Case {
                indspec,
                scrutinee,
                branches,
            } => N::ProgramCase {
                inductive: indspec.into(),
                scrutinee: scrutinee.0,
                binders: branches.iter().map(|b| b.binders.clone()).collect(),
                branches: branches.into_iter().map(|b| b.body.0).collect(),
            },
        };
        ComputationTerm(arena.core.alloc(node))
    }
}
impl ArenaHandle for ComputationTerm {
    type Node = ComputationTermNode;
    fn get(self, arena: &Arena) -> ComputationTermNode {
        match arena.core.get(self.0) {
            N::Definition { id, arguments } => {
                ComputationTerm(arena.reference_view(id, arguments, true)).get(arena)
            }
            N::Return { value, .. } => ComputationTermNode::Return {
                value: ValueTerm(value),
            },
            N::Force { value, .. } => ComputationTermNode::Force {
                value: ValueTerm(value),
            },
            N::Lambda {
                var, domain, body, ..
            } => ComputationTermNode::Lambda {
                var,
                value_ty: ValueType(domain),
                body: ComputationTerm(body),
            },
            N::App {
                function, argument, ..
            } => ComputationTermNode::Application {
                computation: ComputationTerm(function),
                value: ValueTerm(argument),
            },
            N::Sequence {
                computation,
                var,
                value_ty,
                body,
                ..
            } => ComputationTermNode::Sequence {
                computation: ComputationTerm(computation),
                var,
                value_ty: ValueType(value_ty),
                body: ComputationTerm(body),
            },
            N::ValueLet {
                var,
                value_ty,
                value,
                body,
                ..
            } => ComputationTermNode::ValueLet {
                var,
                value_ty: ValueType(value_ty),
                value: ValueTerm(value),
                body: ComputationTerm(body),
            },
            N::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
                ..
            } => ComputationTermNode::Run {
                state_ty: ValueType(state_ty),
                result_ty: ValueType(result_ty),
                step: ValueTerm(step),
                initial: ValueTerm(initial),
                accessibility: Exp(accessibility),
            },
            N::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
                ..
            } => ComputationTermNode::RunCase {
                state_ty: ValueType(state_ty),
                result_ty: ValueType(result_ty),
                step: ValueTerm(step),
                initial: ValueTerm(initial),
                transition: ComputationTerm(transition),
                accessibility: Exp(accessibility),
                transition_equality: Exp(transition_equality),
            },
            N::Meta { id, arguments } => match arena.atom_key(id) {
                Atom::Meta(_, metavariable, kinds) => ComputationTermNode::Meta {
                    metavariable,
                    spine: arguments
                        .into_iter()
                        .zip(kinds)
                        .map(|(e, ty)| {
                            if ty {
                                super::program::ProgramArgument::ValueType(ValueType(e))
                            } else {
                                super::program::ProgramArgument::ValueTerm(ValueTerm(e))
                            }
                        })
                        .collect(),
                },
                Atom::Definition(id) => ComputationTermNode::DefinedConstant(id),
                Atom::Instance(definition) => ComputationTermNode::DefinitionInstance {
                    definition,
                    parameters: arguments.into_iter().map(ValueType).collect(),
                },
            },
            N::ProgramCase {
                inductive,
                scrutinee,
                binders,
                branches,
            } => ComputationTermNode::Case {
                indspec: ProgramInductiveId {
                    module: crate::raw::ids::ModuleId((inductive.0 >> 32) as u32),
                    index: inductive.0 as u32,
                },
                scrutinee: ValueTerm(scrutinee),
                branches: branches
                    .into_iter()
                    .zip(binders)
                    .map(|(body, binders)| super::program::ProgramCaseBranch {
                        binders,
                        body: ComputationTerm(body),
                    })
                    .collect(),
            },
            node => panic!("incorrect frontend Program view: {node:?}"),
        }
    }
}
fn lower_proof(proof: Prove) -> N {
    match proof {
        Prove::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => N::AccIntro {
            state_ty: state_ty.0,
            result_ty: result_ty.0,
            step: step.0,
            state: state.0,
            predecessors: predecessors.0,
        },
        Prove::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => N::AccDescent {
            state_ty: state_ty.0,
            result_ty: result_ty.0,
            step: step.0,
            from: from.0,
            to: to.0,
            accessibility: accessibility.0,
            transition: transition.0,
        },
        Prove::ExistsIntro { element, set } => N::ExistsIntro {
            element: element.0,
            set: set.0,
        },
        Prove::SubsetElim {
            element,
            subset,
            superset,
        } => N::SubsetElim {
            element: element.0,
            subset: subset.0,
            superset: superset.0,
        },
        Prove::IdRefl { element } => N::IdRefl { element: element.0 },
        Prove::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => N::IdElim {
            left: left.0,
            right: right.0,
            ty: ty.0,
            var,
            predicate: predicate.0,
            base: base.0,
            equality: equality.0,
        },
        Prove::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => N::TakeEq {
            func: func.0,
            domain: domain.0,
            codomain: codomain.0,
            element: element.0,
            existence: existence.0,
            uniqueness: uniqueness.0,
        },
        Prove::Axiom(Axiom::SetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        }) => N::SetExt {
            left: left.0,
            right: right.0,
            left_to_right: left_to_right.0,
            right_to_left: right_to_left.0,
        },
        Prove::Axiom(Axiom::FunExt {
            left,
            right,
            pointwise,
        }) => N::FunExt {
            left: left.0,
            right: right.0,
            pointwise: pointwise.0,
        },
        Prove::Axiom(Axiom::ClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        }) => N::ClassicalIndefiniteChoice {
            domain: domain.0,
            family: family.0,
            inhabited: inhabited.0,
        },
    }
}
fn raise_proof(node: N) -> Prove {
    match node {
        N::AccIntro {
            state_ty,
            result_ty,
            step,
            state,
            predecessors,
        } => Prove::AccIntro {
            state_ty: Exp(state_ty),
            result_ty: Exp(result_ty),
            step: Exp(step),
            state: Exp(state),
            predecessors: Exp(predecessors),
        },
        N::AccDescent {
            state_ty,
            result_ty,
            step,
            from,
            to,
            accessibility,
            transition,
        } => Prove::AccDescent {
            state_ty: Exp(state_ty),
            result_ty: Exp(result_ty),
            step: Exp(step),
            from: Exp(from),
            to: Exp(to),
            accessibility: Exp(accessibility),
            transition: Exp(transition),
        },
        N::ExistsIntro { element, set } => Prove::ExistsIntro {
            element: Exp(element),
            set: Exp(set),
        },
        N::SubsetElim {
            element,
            subset,
            superset,
        } => Prove::SubsetElim {
            element: Exp(element),
            subset: Exp(subset),
            superset: Exp(superset),
        },
        N::IdRefl { element } => Prove::IdRefl {
            element: Exp(element),
        },
        N::IdElim {
            left,
            right,
            ty,
            var,
            predicate,
            base,
            equality,
        } => Prove::IdElim {
            left: Exp(left),
            right: Exp(right),
            ty: Exp(ty),
            var,
            predicate: Exp(predicate),
            base: Exp(base),
            equality: Exp(equality),
        },
        N::TakeEq {
            func,
            domain,
            codomain,
            element,
            existence,
            uniqueness,
        } => Prove::TakeEq {
            func: Exp(func),
            domain: Exp(domain),
            codomain: Exp(codomain),
            element: Exp(element),
            existence: Exp(existence),
            uniqueness: Exp(uniqueness),
        },
        N::SetExt {
            left,
            right,
            left_to_right,
            right_to_left,
        } => Prove::Axiom(Axiom::SetExt {
            left: Exp(left),
            right: Exp(right),
            left_to_right: Exp(left_to_right),
            right_to_left: Exp(right_to_left),
        }),
        N::FunExt {
            left,
            right,
            pointwise,
        } => Prove::Axiom(Axiom::FunExt {
            left: Exp(left),
            right: Exp(right),
            pointwise: Exp(pointwise),
        }),
        N::ClassicalIndefiniteChoice {
            domain,
            family,
            inhabited,
        } => Prove::Axiom(Axiom::ClassicalIndefiniteChoice {
            domain: Exp(domain),
            family: Exp(family),
            inhabited: Exp(inhabited),
        }),
        node => panic!("incorrect frontend logical view: {node:?}"),
    }
}
fn lower_sort(sort: Sort) -> kernel::sort::Sort {
    use kernel::sort::{BaseSort as B, Sort as S};
    match sort {
        Sort::Set(i) => S::Base(B::Set(i)),
        Sort::SetKind(i) => S::Upper(B::Set(i)),
        Sort::Prop => S::Base(B::Prop),
        Sort::PropKind => S::Upper(B::Prop),
    }
}
fn raise_sort(sort: kernel::sort::Sort) -> Sort {
    use kernel::sort::{BaseSort as B, Sort as S};
    match sort {
        S::Base(B::Set(i)) => Sort::Set(i),
        S::Upper(B::Set(i)) => Sort::SetKind(i),
        S::Base(B::Prop) => Sort::Prop,
        S::Upper(B::Prop) => Sort::PropKind,
        _ => panic!("Program sort in logical view"),
    }
}

impl kernel::reflection::Resolver for Arena {
    fn arena(&self) -> &kernel::syntax::Arena {
        &self.core
    }
    fn replacement(
        &self,
        e: kernel::syntax::Expression,
    ) -> Result<Option<kernel::syntax::Expression>, String> {
        if let N::Definition { id, arguments } = self.core.get(e) {
            return kernel::calculus::instantiate(&self.core, self.definition_body(id), &arguments)
                .map(Some);
        }
        Ok(None)
    }
    fn definition(
        &self,
        _id: kernel::ids::DefinitionId,
    ) -> Result<(kernel::ids::DefinitionId, Vec<bool>), String> {
        Err("unresolved definition reflection".into())
    }
    fn datatype(
        &self,
        id: kernel::ids::ProgramInductiveId,
    ) -> Result<kernel::ids::InductiveId, String> {
        self.datatype_reflections
            .borrow()
            .get(&id)
            .copied()
            .ok_or_else(|| "missing datatype reflection".into())
    }
}
