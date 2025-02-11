
use std::default;

use super::*;
use colored::Colorize;
use termtree::Tree;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Node {
    TypeCheckJudgement(TypeCheckJudgement),
    Label(DerivationLabel),
    ProvableJudgement(ProvableJudgement),
    Condition(Condition),
    Fail(FailHead),
    ErrCond(ErrOnCondition),
    ErrOther(String),
    ContextInfo(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum TreeConfig {
    #[default]
    OnlyGoals,
    SuccTree,
    AllCase,
}

fn error_string(s: String) -> String {
    format!("{}", s.red())
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = match self {
            Node::TypeCheckJudgement(type_check_judgement) => {
                format!("{type_check_judgement}")
            }
            Node::Label(label) => format!("{label}"),
            Node::ProvableJudgement(provable_judgement) => {
                format!("{}", format!("{provable_judgement}").green())
            }
            Node::Condition(condition) => format!("{condition}"),
            Node::Fail(fail_head) => match fail_head {
                FailHead::InferFail(local_context, exp) => {
                    error_string(format!("!{local_context} |- {exp}: !"))
                }
                FailHead::CheckFail(type_check_judgement) => {
                    error_string(format!("{type_check_judgement}"))
                }
            },
            Node::ErrCond(err) => error_string(err.err.clone()),
            Node::ErrOther(other) => error_string(other.clone()),
            Node::ContextInfo(extra_info) => format!("{extra_info:?}"),
        };
        write!(f, "{s}")
    }
}

fn node_to_tree(node: &DerChild, tree_config: &TreeConfig) -> Option<Tree<Node>> {
    match node {
        DerChild::PartialDerivationTree(partial_derivation_tree_type_check) => Some(
            tree_partial_derivation_tree(partial_derivation_tree_type_check, tree_config),
        ),
        DerChild::Condition(condition) => {
            if matches!(tree_config, TreeConfig::AllCase | TreeConfig::SuccTree) {
                Some(Tree::new(Node::Condition(condition.clone())))
            } else {
                None
            }
        }
        DerChild::NeedProve(provable_judgement) => Some(Tree::new(Node::ProvableJudgement(
            provable_judgement.clone(),
        ))),
    }
}

fn err_info(err_info: &ErrInfo, tree_config: &TreeConfig) -> Tree<Node> {
    match err_info {
        ErrInfo::Condition(err_on_condition) => Tree::new(Node::ErrCond(err_on_condition.clone())),
        ErrInfo::FailTree(derivation_failed) => tree_fail_tree(derivation_failed, tree_config),
        ErrInfo::Other(other) => Tree::new(Node::ErrOther(other.clone())),
    }
}

fn tree_err_case(err_case: &ErrCases, tree_config: &TreeConfig) -> Tree<Node> {
    let ErrCases {
        case,
        successes,
        error,
    } = err_case;
    let mut tree = Tree::new(Node::ContextInfo(format!("err info {case}")));

    tree.extend(
        successes
            .iter()
            .filter_map(|child| node_to_tree(child, tree_config)),
    );
    tree.push(err_info(error, tree_config));
    tree
}

fn tree_partial_derivation_tree(
    tree: &PartialDerivationTreeTypeCheck,
    tree_config: &TreeConfig,
) -> Tree<Node> {
    if *tree_config == TreeConfig::OnlyGoals {
        let mut show_tree = Tree::new(Node::TypeCheckJudgement(tree.head.clone()));
        show_tree.extend(
            tree.get_goals()
                .into_iter()
                .map(|goal| Node::ProvableJudgement(goal)),
        );
        return show_tree;
    }

    let PartialDerivationTreeTypeCheck {
        head,
        label,
        child,
        gen_and_case: (generated, case),
        other_case,
    } = tree;
    let mut tree = Tree::new(Node::TypeCheckJudgement(head.clone()));

    if matches!(tree_config, TreeConfig::SuccTree) {
        tree.push(Tree::new(Node::ContextInfo(format!(
            "generated {generated}, case {case}"
        ))));
        tree.push(Tree::new(Node::Label(label.clone())));
    }

    tree.extend(
        child
            .iter()
            .filter_map(|child| node_to_tree(child, tree_config)),
    );

    if matches!(tree_config, TreeConfig::AllCase) {
        tree.extend(
            other_case
                .iter()
                .map(|err_case| tree_err_case(err_case, tree_config)),
        );
    }
    tree
}

pub fn print_tree(tree: &PartialDerivationTreeTypeCheck, tree_config: &TreeConfig) -> String {
    tree_partial_derivation_tree(tree, tree_config).to_string()
}

fn tree_fail_tree(tree: &DerivationFailed, tree_config: &TreeConfig) -> Tree<Node> {
    let DerivationFailed {
        head,
        generated_info,
        err_cases,
    } = tree;
    let mut tree = Tree::new(Node::Fail(head.clone()));
    tree.push(Tree::new(Node::ContextInfo(generated_info.clone())));
    tree.extend(
        err_cases
            .iter()
            .map(|child| tree_err_case(child, tree_config)),
    );
    tree
}

pub fn print_fail_tree(tree: &DerivationFailed, tree_config: &TreeConfig) -> String {
    tree_fail_tree(tree, tree_config).to_string()
}
