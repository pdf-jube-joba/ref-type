use crate::{StringTree, TreeNode};
use kernel::exp::{
    Context, DefinedConstant, DerivationBase, DerivationFail, DerivationSuccess, Exp, FailHead,
    FailKind, GoalGenerated, ProveCommandBy, ProveGoal, Sort, SuccessHead, Var,
};

fn format_var(var: &Var) -> String {
    var.as_str().to_string()
}

pub(super) fn format_sort(sort: &Sort) -> String {
    match sort {
        Sort::Prop => "\\Prop".to_string(),
        Sort::PropKind => "\\PropKind".to_string(),
        Sort::Set(i) => format!("\\Set({i})"),
        Sort::SetKind(i) => format!("\\SetKind({i})"),
        Sort::Univ => "\\Univ".to_string(),
        Sort::UnivKind => "\\UnivKind".to_string(),
    }
}

pub(super) fn format_exp(exp: &Exp) -> String {
    match exp {
        Exp::Sort(sort) => format_sort(sort),
        Exp::Var(var) => format_var(var),
        Exp::Prod { var, ty, body } => format!(
            "({}: {}) -> {}",
            format_var(var),
            format_exp(ty),
            format_exp(body)
        ),
        Exp::Lam { var, ty, body } => format!(
            "({}: {}) => {}",
            format_var(var),
            format_exp(ty),
            format_exp(body)
        ),
        Exp::App { func, arg } => format!("({}) ({})", format_exp(func), format_exp(arg)),
        Exp::DefinedConstant(rc) => {
            format!("{}{}", super::print_rc_ptr(rc), format_defined_constant(rc))
        }
        Exp::IndType {
            indspec,
            parameters,
        } => format!(
            "{}[{}]",
            super::print_rc_ptr(indspec),
            parameters
                .iter()
                .map(format_exp)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Exp::IndCtor {
            indspec,
            parameters,
            idx,
        } => format!(
            "{}.{}[{}]",
            super::print_rc_ptr(indspec),
            idx,
            parameters
                .iter()
                .map(format_exp)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Exp::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => format!(
            "elim {} \\in {} \\return {} with {{{}}}",
            format_exp(elim),
            super::print_rc_ptr(indspec),
            format_exp(return_type),
            cases.iter().map(format_exp).collect::<Vec<_>>().join(", ")
        ),
        Exp::Cast { exp, to } => format!("{} as {}", format_exp(exp), format_exp(to)),
        Exp::ProveLater { prop } => format!("proof({})", format_exp(prop)),
        Exp::ProveHere { exp, goals } => format!(
            "proof_here {} with ({})",
            format_exp(exp),
            goals.iter().map(format_goal).collect::<Vec<_>>().join(", ")
        ),
        Exp::ProofTermRaw { command } => format!("proof_term({})", format_command(command)),
        Exp::PowerSet { set } => format!("Pow({})", format_exp(set)),
        Exp::SubSet {
            var,
            set,
            predicate,
        } => format!(
            "{{ {}: {} | {} }}",
            format_var(var),
            format_exp(set),
            format_exp(predicate)
        ),
        Exp::Pred {
            superset,
            subset,
            element,
        } => format!(
            "{} ∈ {} ⊆ {}",
            format_exp(element),
            format_exp(subset),
            format_exp(superset)
        ),
        Exp::TypeLift { superset, subset } => {
            format!("TypeLift({}, {})", format_exp(superset), format_exp(subset))
        }
        Exp::Equal { left, right } => format!("{} = {}", format_exp(left), format_exp(right)),
        Exp::Exists { set } => format!("\\exists {}", format_exp(set)),
        Exp::Take { map } => format!("\\Take {}", format_exp(map)),
    }
}

pub(super) fn format_ctx(ctx: &Context) -> String {
    ctx.iter()
        .map(|(var, ty)| format!("{}: {}", format_var(var), format_exp(ty)))
        .collect::<Vec<_>>()
        .join(", ")
}

pub(super) fn derivation_success_tree(derivation: &DerivationSuccess) -> StringTree {
    map_derivation_success(derivation)
}

pub(super) fn derivation_fail_tree(derivation: &DerivationFail) -> StringTree {
    map_derivation_fail(derivation)
}

pub(super) fn format_goal(goal: &ProveGoal) -> String {
    let ProveGoal {
        extended_ctx,
        goal_prop,
        command,
    } = goal;
    format!(
        "[..  {} |= {} by {}]",
        format_ctx(extended_ctx),
        format_exp(goal_prop),
        format_command(command)
    )
}

fn map_derivation_success(derivation: &DerivationSuccess) -> StringTree {
    let DerivationSuccess {
        head,
        base: DerivationBase {
            premises,
            rule,
            phase,
        },
        generated_goals,
        through,
    } = derivation;
    if *through {
        let through_tree = map_derivation_success(&premises[0]);
        let head_label = render_tree_node(&through_tree.head);
        StringTree {
            head: TreeNode::Success(format!("{head_label} through {rule}[{phase}]")),
            children: through_tree.children,
        }
    } else {
        let head_node = match head {
            SuccessHead::TypeJudgement { ctx, term, ty } => TreeNode::Success(format!(
                "[{} |- {} : {}] {} [{}]",
                format_ctx(ctx),
                format_exp(term),
                format_exp(ty),
                rule,
                phase
            )),
            SuccessHead::ProofJudgement { ctx, prop } => TreeNode::Success(format!(
                "[{} |= {}] {} [{}]",
                format_ctx(ctx),
                format_exp(prop),
                rule,
                phase
            )),
            SuccessHead::WellFormednessInductive { ctx, indspec } => TreeNode::Success(format!(
                "[{} |- wf_inductive {}]",
                format_ctx(ctx),
                super::print_rc_ptr(indspec)
            )),
            SuccessHead::Solve(derivation_success) => {
                let tree = map_derivation_success(derivation_success);
                return StringTree {
                    head: TreeNode::Success(format!("Solve goal{:p}", *derivation_success)),
                    children: vec![tree],
                };
            }
        };
        let mut children = premises
            .iter()
            .map(map_derivation_success)
            .collect::<Vec<_>>();
        for goal in generated_goals {
            children.push(goal_to_tree(goal));
        }
        StringTree {
            head: head_node,
            children,
        }
    }
}

fn goal_to_tree(goal: &GoalGenerated) -> StringTree {
    let GoalGenerated {
        ctx,
        proposition,
        solvetree,
    } = goal;
    match solvetree {
        Some(rc) => StringTree {
            head: TreeNode::Success(format!(
                "!Solved[{} |= {}] via {:p}",
                format_ctx(ctx),
                format_exp(proposition),
                *rc
            )),
            children: vec![],
        },
        None => StringTree {
            head: TreeNode::Pending(format!(
                "!UnSolved[{} |= {}]",
                format_ctx(ctx),
                format_exp(proposition)
            )),
            children: vec![],
        },
    }
}

fn map_derivation_fail(derivation: &DerivationFail) -> StringTree {
    let DerivationFail { base, head, kind } = derivation;

    let DerivationBase {
        premises,
        rule,
        phase,
    } = base.as_ref();

    let render =
        |node: TreeNode, premises: &[DerivationSuccess], extra_child: Option<StringTree>| {
            let mut children = premises
                .iter()
                .map(map_derivation_success)
                .collect::<Vec<_>>();
            if let Some(child) = extra_child {
                children.push(child);
            }
            StringTree {
                head: node,
                children,
            }
        };

    match kind {
        FailKind::Caused { cause } => {
            let head_node = match head {
                FailHead::TypeJudgement { ctx, term, ty } => TreeNode::ErrorCause(format!(
                    "[{} |- {} : {}]{{{cause}}} {} [{}]",
                    format_ctx(ctx),
                    format_exp(term),
                    ty.as_ref()
                        .map(format_exp)
                        .unwrap_or_else(|| "<??>".to_string()),
                    rule,
                    phase
                )),
                FailHead::ProofJudgement { ctx, prop } => TreeNode::ErrorCause(format!(
                    "[{} |= {}]{{{cause}}} {} [{}]",
                    format_ctx(ctx),
                    prop.as_ref()
                        .map(format_exp)
                        .unwrap_or_else(|| "<??>".to_string()),
                    rule,
                    phase
                )),
                FailHead::WellFormednessInductive { ctx, indspec } => {
                    TreeNode::ErrorCause(format!(
                        "[{} |- wf_inductive {}] {} [{}]",
                        format_ctx(ctx),
                        super::print_rc_ptr(indspec),
                        rule,
                        phase
                    ))
                }
                FailHead::Solve(derivation_success) => {
                    let tree = map_derivation_success(derivation_success);
                    return StringTree {
                        head: TreeNode::ErrorCause(format!(
                            "solved but something wrong{:p}",
                            *derivation_success
                        )),
                        children: vec![tree],
                    };
                }
            };
            render(head_node, premises, None)
        }
        FailKind::Propagate { fail, expect } => {
            let head_node = match head {
                FailHead::TypeJudgement { ctx, term, ty } => TreeNode::ErrorPropagate(format!(
                    "[{} |- {} : {}]{{{expect}}} {} [{}]",
                    format_ctx(ctx),
                    format_exp(term),
                    ty.as_ref()
                        .map(format_exp)
                        .unwrap_or_else(|| "<??>".to_string()),
                    rule,
                    phase
                )),
                FailHead::ProofJudgement { ctx, prop } => TreeNode::ErrorPropagate(format!(
                    "[{} |= {}]{{{expect}}} {} [{}]",
                    format_ctx(ctx),
                    prop.as_ref()
                        .map(format_exp)
                        .unwrap_or_else(|| "<??>".to_string()),
                    rule,
                    phase
                )),
                FailHead::WellFormednessInductive { ctx, indspec } => {
                    TreeNode::ErrorPropagate(format!(
                        "[{} |- wf_inductive {}] {} [{}]",
                        format_ctx(ctx),
                        super::print_rc_ptr(indspec),
                        rule,
                        phase
                    ))
                }
                FailHead::Solve(derivation_success) => {
                    let tree = map_derivation_success(derivation_success);
                    return StringTree {
                        head: TreeNode::ErrorPropagate(format!(
                            "solved but something wrong{:p}",
                            *derivation_success
                        )),
                        children: vec![tree],
                    };
                }
            };
            render(head_node, premises, Some(map_derivation_fail(fail)))
        }
    }
}

fn format_defined_constant(rc: &std::rc::Rc<DefinedConstant>) -> String {
    format!("[: {} := {}]", format_exp(&rc.ty), format_exp(&rc.body))
}

fn format_command(command: &ProveCommandBy) -> String {
    match command {
        ProveCommandBy::Construct(proof_term) => {
            format!("construct {}", format_exp(proof_term))
        }
        ProveCommandBy::ExactElem { elem, ty } => {
            format!("exact {} : {}", format_exp(elem), format_exp(ty))
        }
        ProveCommandBy::SubsetElim {
            elem,
            subset,
            superset,
        } => format!(
            "subset_elim {} in {} ⊆ {}",
            format_exp(elem),
            format_exp(subset),
            format_exp(superset)
        ),
        ProveCommandBy::IdRefl { elem } => format!("id_refl {}", format_exp(elem)),
        ProveCommandBy::IdElim {
            left: elem1,
            right: elem2,
            ty,
            var,
            predicate,
        } => format!(
            "id_elim {} = {} with ({}: {}) => {}",
            format_exp(elem1),
            format_exp(elem2),
            format_var(var),
            format_exp(ty),
            format_exp(predicate)
        ),
        ProveCommandBy::TakeEq {
            func,
            domain,
            codomain,
            elem,
        } => format!(
            "take_eq {}({}) in {} -> {} ",
            format_exp(func),
            format_exp(elem),
            format_exp(domain),
            format_exp(codomain)
        ),
        ProveCommandBy::Axiom(axiom) => format!("axiom {:?}", axiom),
    }
}

fn render_tree_node(node: &TreeNode) -> String {
    match node {
        TreeNode::Success(s)
        | TreeNode::ErrorPropagate(s)
        | TreeNode::ErrorCause(s)
        | TreeNode::Pending(s) => s.clone(),
    }
}
