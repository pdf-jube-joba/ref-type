//! Kernel expressions and their append-only arena.

use std::cell::RefCell;

use crate::ids::{DefId, InductiveId, ModuleParamId, SymbolId};
use crate::sort::Sort;
use serde::{Deserialize, Serialize};

/// A stable index into an [`Arena`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NodeId(u32);

impl NodeId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// The expression handle used throughout the kernel.
pub type Exp = NodeId;

#[derive(Debug, Clone, Serialize)]
pub enum Node {
    Sort(Sort),
    /// A locally bound variable, counted outwards from the occurrence.
    /// `Bound(0)` refers to the nearest enclosing binder.
    Bound(usize),
    /// A parameter of a module. Locally bound variables use [`Node::Bound`].
    ModuleParam(ModuleParamId),
    // A reference to a defined constant. The definition is stored in the environment.
    DefinedConstant(DefId),
    // (var: ty) -> body where var is bound in body but not in ty
    Prod {
        var: SymbolId,
        ty: Exp,
        body: Exp, // bind one variable
    },
    // (var: ty) => body where var is bound in body but not in ty
    Lam {
        var: SymbolId,
        ty: Exp,
        body: Exp, // bind one variable
    },
    // usual application (f x)
    App {
        func: Exp,
        arg: Exp,
    },
    IndType {
        indspec: InductiveId,
        parameters: Vec<Exp>, // uncurry with parameter
    },
    IndCtor {
        indspec: InductiveId,
        parameters: Vec<Exp>, // uncurry with parameter
        idx: usize,
    },
    IndElim {
        // this is primitive recursion
        indspec: InductiveId,
        elim: Exp,
        return_type: Exp,
        cases: Vec<Exp>, // no bindings
    },
    // General recursion over the compute universe. Type annotations are kept
    // explicitly so reduction never has to invoke the type checker.
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
    RfType {
        compute_ty: Exp,
    },
    RfTerm {
        compute_ty: Exp,
        term: Exp,
    },
    Run {
        state_ty: Exp,
        result_ty: Exp,
        step: Exp,
        initial: Exp,
        // Implementation-only certificate corresponding to the Run rule's
        // termination premise. It has no computational role.
        termination: Exp,
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
    // {var: set | predicate} where var is bound in predicate but not in A
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
    // Introduce `element` into `subset` of `superset` using `proof`.
    // This is a typing annotation and erases to `element` computationally.
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
    // just non-emptyness proposition
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
    TakeEq {
        func: Exp,
        domain: Exp,
        codomain: Exp,
        element: Exp,
        existence: Exp,
        uniqueness: Exp,
    },
}

#[cfg(feature = "bench-internals")]
#[derive(Debug, Clone, Copy)]
pub struct ArenaMark {
    nodes: usize,
}

/// Append-only storage for every kernel expression node.
#[derive(Debug, Default)]
pub struct Arena {
    nodes: RefCell<Vec<Node>>,
}

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc(&self, node: Node) -> Exp {
        let mut nodes = self.nodes.borrow_mut();
        let index = u32::try_from(nodes.len()).expect("expression arena exceeded u32::MAX");
        nodes.push(node);
        NodeId(index)
    }

    /// Return a shallow copy. Child expressions remain cheap `NodeId`s.
    pub fn get(&self, id: Exp) -> Node {
        self.nodes.borrow()[id.index()].clone()
    }

    pub fn len(&self) -> usize {
        self.nodes.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.borrow().is_empty()
    }

    /// Checkpoint the arena for benchmark iteration cleanup.
    ///
    /// This is deliberately unavailable unless the `bench-internals` feature
    /// is enabled. Every expression allocated after the returned mark becomes
    /// invalid after [`Arena::rewind`].
    #[cfg(feature = "bench-internals")]
    pub fn mark(&self) -> ArenaMark {
        ArenaMark { nodes: self.len() }
    }

    /// Discard benchmark temporaries allocated after `mark`.
    ///
    /// Callers must not retain any expression allocated after the mark.
    #[cfg(feature = "bench-internals")]
    pub fn rewind(&self, mark: ArenaMark) {
        self.nodes.borrow_mut().truncate(mark.nodes);
    }

    pub fn sort(&self, sort: Sort) -> Exp {
        self.alloc(Node::Sort(sort))
    }

    pub fn bound(&self, index: usize) -> Exp {
        self.alloc(Node::Bound(index))
    }

    pub fn module_param(&self, parameter: ModuleParamId) -> Exp {
        self.alloc(Node::ModuleParam(parameter))
    }

    pub fn as_module_param(&self, exp: Exp) -> Option<ModuleParamId> {
        match self.get(exp) {
            Node::ModuleParam(parameter) => Some(parameter),
            _ => None,
        }
    }
}

pub type Context = Vec<(SymbolId, Exp)>;
