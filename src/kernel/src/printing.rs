use std::fmt::{Debug, Display};

use crate::exp::{Derivation, ProveGoal, TypeJudge, Var};

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
            crate::exp::Exp::IndType { ty, parameters } => write!(
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
                ty,
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
                ty,
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
            crate::exp::Exp::Cast { exp, to, withgoals } => {
                write!(
                    f,
                    "{} as {} by {}",
                    exp,
                    to,
                    withgoals
                        .iter()
                        .map(
                            |ProveGoal {
                                 extended_ctx,
                                 goal_prop,
                                 proof_term,
                             }| format!(
                                "[{extended_ctx:?}: {goal_prop} := {proof_term}]"
                            )
                        )
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            crate::exp::Exp::ProveLater { prop } => {
                write!(f, "proof({})", prop)
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
                    elem1,
                    elem2,
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
            .0
            .iter()
            .map(|(var, ty)| format!("{}: {}", var, ty))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "[{}]", ctx_str)
    }
}

impl Display for TypeJudge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} |- {} : {}", self.ctx, self.term, self.ty)
    }
}

impl Display for crate::exp::Provable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} |= {}", self.ctx, self.prop)
    }
}

impl Display for crate::exp::FailJudge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Failed to judge: {}", self.0)
    }
}

pub struct StringTree(String, Vec<StringTree>);

fn map_derivation(der: &Derivation) -> StringTree {
    match der {
        Derivation::TypeDerive {
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
            }
        }
        Derivation::PropDerive {
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
            }
        }
        Derivation::FailDerive {
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
            }
        }
        Derivation::UnProved(provable) => StringTree(format!("Unproved: {}", provable), vec![]),
        Derivation::Proved { target, num } => {
            StringTree(format!("Proved: {} at {:p}", target, num), vec![])
        }
        Derivation::ProveFailed { target, num } => {
            StringTree(format!("ProveFailed: {} at {:p}", target, num), vec![])
        }
        Derivation::Proving { prop, der, num } => StringTree(
            format!("Proving: {} at {:p}", prop, num),
            vec![map_derivation(der)],
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
