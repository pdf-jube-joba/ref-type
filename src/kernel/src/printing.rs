use std::fmt::{Debug, Display};

use crate::exp::{Derivation, Node, Prove, ProveGoal, SortInfer, TypeCheck, TypeInfer, Var};

impl Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{:p}]", self.name(), self.ptr())
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl Display for crate::exp::Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            crate::exp::Sort::Prop => write!(f, "\\Prop"),
            crate::exp::Sort::PropKind => write!(f, "\\PropKind"),
            crate::exp::Sort::Set(i) => write!(f, "\\Set({})", i),
            crate::exp::Sort::SetKind(i) => write!(f, "\\SetKind({})", i),
            crate::exp::Sort::Univ => write!(f, "\\Univ"),
            crate::exp::Sort::UnivKind => write!(f, "\\UnivKind"),
        }
    }
}

impl Display for crate::exp::Exp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            crate::exp::Exp::Sort(sort) => write!(f, "{}", sort),
            crate::exp::Exp::Var(var) => write!(f, "{}", var),
            crate::exp::Exp::Prod { var, ty, body } => write!(f, "({}: {}) -> {}", var, ty, body),
            crate::exp::Exp::Lam { var, ty, body } => write!(f, "({}: {}) => {}", var, ty, body),
            crate::exp::Exp::App { func, arg } => write!(f, "({}) ({})", func, arg),
            crate::exp::Exp::IndType {
                indty: ty,
                parameters,
            } => write!(
                f,
                "{:p}({})",
                ty,
                parameters
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            crate::exp::Exp::IndCtor {
                indty: ty,
                parameters,
                idx,
            } => write!(
                f,
                "{:p}.{}({})",
                ty,
                idx,
                parameters
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            crate::exp::Exp::IndElim {
                indty: ty,
                elim,
                return_type,
                sort,
                cases,
            } => {
                write!(
                    f,
                    "elim {:p} {} : {} in {} with ({})",
                    ty,
                    elim,
                    return_type,
                    sort,
                    cases
                        .iter()
                        .map(|c| format!("{}", c))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            crate::exp::Exp::Cast { exp, to } => {
                write!(f, "{} as {} ", exp, to,)
            }
            crate::exp::Exp::ProveLater { prop } => {
                write!(f, "proof({})", prop)
            }
            crate::exp::Exp::ProveHere { exp, goals } => {
                write!(
                    f,
                    "proof_here {} with ({})",
                    exp,
                    goals
                        .iter()
                        .map(|g| format!("{}", g))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            crate::exp::Exp::ProofTermRaw { command } => match command.as_ref() {
                crate::exp::ProveCommandBy::Construct { proof_term } => {
                    write!(f, "construct {}", proof_term)
                }
                crate::exp::ProveCommandBy::ExactElem { elem, ty } => {
                    write!(f, "exact {} : {}", elem, ty)
                }
                crate::exp::ProveCommandBy::SubsetElim {
                    elem,
                    subset,
                    superset,
                } => {
                    write!(f, "subset_elim {} in {} ⊆ {}", elem, subset, superset)
                }
                crate::exp::ProveCommandBy::IdRefl { elem } => {
                    write!(f, "id_refl {} ", elem)
                }
                crate::exp::ProveCommandBy::IdElim {
                    left: elem1,
                    right: elem2,
                    ty,
                    var,
                    predicate,
                } => {
                    write!(
                        f,
                        "id_elim {} = {} with ({}: {}) => {}",
                        elem1, elem2, var, ty, predicate
                    )
                }
                crate::exp::ProveCommandBy::TakeEq {
                    func,
                    domain,
                    codomain,
                    elem,
                } => {
                    write!(
                        f,
                        "take_eq {}({}) in {} -> {} ",
                        func, elem, domain, codomain
                    )
                }
                crate::exp::ProveCommandBy::Axiom(axiom) => {
                    write!(f, "axiom {:?}", axiom)
                }
            },
            crate::exp::Exp::PowerSet { set } => {
                write!(f, "Pow({})", set)
            }
            crate::exp::Exp::SubSet {
                var,
                set,
                predicate,
            } => {
                write!(f, "{{ {}: {} | {} }}", var, set, predicate)
            }
            crate::exp::Exp::Pred {
                superset,
                subset,
                element,
            } => {
                write!(f, "{} ∈ {} ⊆ {}", element, subset, superset)
            }
            crate::exp::Exp::TypeLift { superset, subset } => {
                write!(f, "TypeLift({}, {})", superset, subset)
            }
            crate::exp::Exp::Equal { left, right } => {
                write!(f, "{} = {}", left, right)
            }
            crate::exp::Exp::Exists { set } => {
                write!(f, "∃ {}", set)
            }
            crate::exp::Exp::Take {
                map,
                domain,
                codomain,
            } => {
                write!(f, "Take({}, {}, {})", map, domain, codomain)
            }
        }
    }
}

impl Display for crate::exp::Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ctx_str = self
            .vec()
            .iter()
            .map(|(var, ty)| format!("{}: {}", var, ty))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "[{}]", ctx_str)
    }
}

impl Display for ProveGoal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ProveGoal {
            extended_ctx,
            goal_prop,
            proof_term,
        } = self;
        write!(f, "[..  {} |- {}: {}]", extended_ctx, proof_term, goal_prop)
    }
}

impl Display for Prove {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Prove { ctx, prop } = self;
        write!(
            f,
            "[{} |= {}]",
            ctx,
            prop.as_ref()
                .map(|p| format!("{}", p))
                .unwrap_or("???".to_string())
        )
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::TypeCheck(TypeCheck { ctx, term, ty, res }) => {
                write!(
                    f,
                    "[{} |- {} : {}] check ... {}",
                    ctx,
                    term,
                    ty,
                    if *res { "Success" } else { "Fail" },
                )
            }
            Node::TypeInfer(TypeInfer { ctx, term, ty }) => {
                write!(
                    f,
                    "[{} |- {} : {}] infer",
                    ctx,
                    term,
                    ty.as_ref()
                        .map(|t| format!("{}", t))
                        .unwrap_or("???".to_string())
                )
            }
            Node::SortInfer(SortInfer { ctx, ty, sort }) => {
                write!(
                    f,
                    "[{} |- {} : {}] sort infer",
                    ctx,
                    ty,
                    sort.as_ref()
                        .map(|t| format!("{}", t))
                        .unwrap_or("???".to_string())
                )
            }
            Node::Prove(prove) => {
                write!(f, "{}", prove)
            }
        }
    }
}

pub struct StringTree(String, Vec<StringTree>);

fn map_derivation(der: &Derivation) -> StringTree {
    match der {
        Derivation::Derivation {
            conclusion,
            premises,
            rule,
            meta,
        } => {
            match meta {
                crate::exp::Meta::Usual(string) => StringTree(
                    format!("{} by {} [{}]", conclusion, rule, string),
                    premises.iter().map(map_derivation).collect(),
                ),
                crate::exp::Meta::Through(string) => {
                    // premises.len() == 1 and we print this with meta info
                    let first = premises.first().unwrap();
                    let mut sttree = map_derivation(first);
                    sttree.0 = format!("{} through [{}]", sttree.0, string);
                    sttree
                }
                crate::exp::Meta::Fail(string) => StringTree(
                    format!("{} failed by {} [{}]", conclusion, rule, string),
                    premises.iter().map(map_derivation).collect(),
                ),
            }
        }
        Derivation::UnSolved(provable) => StringTree(format!("Unproved: {}", provable), vec![]),
        Derivation::Solved { target, num } => {
            StringTree(format!("Proved: {} at {:p}", target, num), vec![])
        }
        Derivation::SolveFailed { target, num } => {
            StringTree(format!("ProveFailed: {} at {:p}", target, num), vec![])
        }
        Derivation::Prove { tree, proved, num } => StringTree(
            format!("Proving: {} at {:p}", proved, num),
            vec![map_derivation(tree)],
        ),
    }
}

fn fmt_tree(f: &mut std::fmt::Formatter<'_>, tree: &StringTree, indent: usize) -> std::fmt::Result {
    for _ in 0..indent {
        write!(f, "  ")?;
    }
    writeln!(f, "{}", tree.0)?;
    for child in &tree.1 {
        fmt_tree(f, child, indent + 1)?;
    }
    Ok(())
}

impl Display for Derivation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tree = map_derivation(self);
        fmt_tree(f, &tree, 0)
    }
}
