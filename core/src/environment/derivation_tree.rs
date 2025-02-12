use termtree::Tree;

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErrCases {
    pub case: String,
    pub successes: Vec<DerChild>,
    pub error: ErrInfo,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DerChild {
    PartialDerivationTree(PartialDerivationTreeTypeCheck),
    Condition(Condition),
    NeedProve(ProvableJudgement),
}

impl From<PartialDerivationTreeTypeCheck> for DerChild {
    fn from(value: PartialDerivationTreeTypeCheck) -> Self {
        DerChild::PartialDerivationTree(value)
    }
}

impl From<Condition> for DerChild {
    fn from(value: Condition) -> Self {
        DerChild::Condition(value)
    }
}

impl From<ProvableJudgement> for DerChild {
    fn from(value: ProvableJudgement) -> Self {
        DerChild::NeedProve(value)
    }
}

impl DerChild {
    pub fn get_goals(&self) -> Vec<ProvableJudgement> {
        match self {
            DerChild::PartialDerivationTree(partial_derivation_tree_type_check) => {
                partial_derivation_tree_type_check.get_goals()
            }
            DerChild::Condition(_) => vec![],
            DerChild::NeedProve(provable_judgement) => vec![provable_judgement.clone()],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialDerivationTreeTypeCheck {
    pub head: TypeCheckJudgement,
    pub label: DerivationLabel,
    pub child: Vec<DerChild>,
    pub gen_and_case: (String, String),
    pub other_case: Vec<ErrCases>,
}

impl PartialDerivationTreeTypeCheck {
    pub fn get_goals(&self) -> Vec<ProvableJudgement> {
        let mut v = vec![];
        for der_child in &self.child {
            match der_child {
                DerChild::PartialDerivationTree(partial_derivation_tree_type_check) => {
                    v.extend(partial_derivation_tree_type_check.get_goals());
                }
                DerChild::Condition(_) => {}
                DerChild::NeedProve(provable_judgement) => {
                    v.push(provable_judgement.clone());
                }
            }
        }
        v
    }
}

impl PartialDerivationTreeTypeCheck {
    pub fn of_type(&self) -> &Exp {
        &self.head.type_of_term
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FailHead {
    InferFail(LocalContext, Exp),
    CheckFail(TypeCheckJudgement),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DerivationFailed {
    pub head: FailHead,
    pub generated_info: String,
    pub err_cases: Vec<ErrCases>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GoalTree {
    UnSolved(ProvableJudgement),
    Branch(Vec<GoalTree>),
}

impl GoalTree {
    pub fn is_empty(&self) -> bool {
        match self {
            GoalTree::UnSolved(_) => false,
            GoalTree::Branch(v) => v.iter().all(|goal| goal.is_empty()),
        }
    }
    pub fn first(&mut self) -> Option<&mut Self> {
        match self {
            GoalTree::UnSolved(_) => Some(self),
            GoalTree::Branch(v) => v.first_mut().map(|v| v.first()).flatten(),
        }
    }
    pub fn first_proposition(&mut self) -> Option<&mut ProvableJudgement> {
        match self {
            GoalTree::UnSolved(p) => Some(p),
            GoalTree::Branch(v) => v.first_mut().map(|v| v.first_proposition()).flatten(),
        }
    }
}

pub fn into_tree(v: Vec<ProvableJudgement>) -> Vec<GoalTree> {
    v.into_iter().map(GoalTree::UnSolved).collect()
}

pub enum Node {
    UnSolved(ProvableJudgement),
    Mid,
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::UnSolved(p) => write!(f, "{p}"),
            Node::Mid => write!(f, "..."),
        }
    }
}

pub fn into_printing_tree(v: &GoalTree) -> Tree<Node> {
    match v {
        GoalTree::UnSolved(p) => Tree::new(Node::UnSolved(p.clone())),
        GoalTree::Branch(v) => {
            let mut t = Tree::new(Node::Mid);
            t.extend(v.iter().map(|t| into_printing_tree(t)));
            t
        }
    }
}
