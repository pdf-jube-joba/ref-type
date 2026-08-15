use std::cell::RefCell;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SymbolId(pub u32);

impl SymbolId {
    pub const ANONYMOUS: Self = Self(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ModuleParamId {
    pub module: ModuleId,
    pub position: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Sort {
    Set(usize),     // predicative SET(i):
    SetKind(usize), // SET(i): SETKind(i)
    Prop,           // proposition
    PropKind,       // Prop: PropKind
    Univ,           // for programming language
    UnivKind,       // Type: TypeKind
}

// functional pure type system
impl Sort {
    // functional pure type system, i.e. foraeach s1, (s1, s2) in R => s2 is unique
    pub fn type_of_sort(self) -> Option<Self> {
        match self {
            Sort::Prop => Some(Sort::PropKind),
            Sort::PropKind => None,
            Sort::Univ => Some(Sort::PropKind),
            Sort::UnivKind => None,
            Sort::Set(i) => Some(Sort::SetKind(i)),
            Sort::SetKind(_) => None,
        }
    }

    // functional pure type system, i.e. for each s1, s2, (s1, s2, s3) in R => s3 is unique
    pub fn relation_of_sort(self, other: Self) -> Option<Self> {
        match (self, other) {
            // Prop: PropKind part（ non dependent ）
            (Sort::Prop, Sort::Prop) => Some(Sort::Prop),
            (Sort::PropKind, Sort::PropKind) => Some(Sort::PropKind),
            (Sort::PropKind, Sort::Prop) => Some(Sort::Prop), // Prop は impredicative
            (Sort::Prop, Sort::PropKind) => None,             // dependent なし
            // Set(i): SetKind(i) part (predicative)
            (Sort::Set(i), Sort::Set(j)) if i == j => Some(Sort::Set(i)),
            (Sort::Set(i), Sort::SetKind(j)) if i == j => Some(Sort::SetKind(i)),
            (Sort::SetKind(i), Sort::SetKind(j)) if i == j => Some(Sort::SetKind(i)),
            (Sort::SetKind(i), Sort::Set(j)) if i == j => Some(Sort::Set(i + 1)),
            (Sort::Set(_) | Sort::SetKind(_), Sort::Set(_) | Sort::SetKind(_)) => None,
            // Type: TypeKind (include dependent, impredicative)
            (Sort::Univ | Sort::UnivKind, Sort::Univ | Sort::UnivKind) => Some(other),
            // relation of set and prop
            (Sort::Set(_), Sort::PropKind) => Some(Sort::PropKind),
            (Sort::Set(_), Sort::Prop) => Some(Sort::Prop),
            (Sort::Prop | Sort::PropKind, Sort::Set(_)) => None,
            // other => None
            _ => None,
        }
    }

    // inductive type relation (restiction for large elimination)
    pub fn relation_of_sort_indelim(self, other: Self) -> Option<()> {
        match (self, other) {
            (
                Sort::PropKind
                | Sort::Prop
                | Sort::Set(_)
                | Sort::SetKind(_)
                | Sort::Univ
                | Sort::UnivKind,
                Sort::Prop,
            ) => Some(()),
            (Sort::Set(i), Sort::Set(j)) => {
                if i <= j {
                    Some(())
                } else {
                    None
                }
            }
            (Sort::Set(_), Sort::PropKind) => Some(()),
            (Sort::PropKind, Sort::PropKind) => Some(()),
            _ => None,
        }
    }

    pub fn can_lift_to(self, to: Self) -> bool {
        match (self, to) {
            (Sort::Set(i), Sort::Set(j)) if i <= j => true,
            (Sort::SetKind(i), Sort::SetKind(j)) if i <= j => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct DefinedConstant {
    pub ty: Exp,
    pub body: Exp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ModuleId(pub u32);

impl ModuleId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ModuleInstanceId {
    pub owner: ModuleId,
    pub local: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DefId {
    pub module: ModuleId,
    pub index: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct InductiveId {
    pub module: ModuleId,
    pub index: u32,
}

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
    DefinedConstant(DefId),
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

    pub fn mark(&self) -> ArenaMark {
        ArenaMark { nodes: self.len() }
    }

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
