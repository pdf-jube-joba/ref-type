use std::fmt::{Debug, Display};

use crate::exp::{Derivation, Judgement, TypeJudge, Var};

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
            crate::exp::Sort::Set(i) => write!(f, "Set({})", i),
            crate::exp::Sort::Prop => write!(f, "Prop"),
            crate::exp::Sort::PropKind => write!(f, "PropKind"),
            crate::exp::Sort::Type => write!(f, "Type"),
            crate::exp::Sort::TypeKind => write!(f, "TypeKind"),
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
                write!(f, "{} as {}", exp, to)
            }
            crate::exp::Exp::ProveLater { prop } => {
                write!(f, "proof({})", prop)
            }
            crate::exp::Exp::ProofTermRaw { command } => {
                // write!(f, "{}", term)
                todo!()
            }
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

impl Display for Judgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Judgement::Type(type_judge) => write!(f, "{}", type_judge),
            Judgement::Provable(provable) => write!(f, "{}", provable),
            Judgement::FailJudge(fail_judge) => write!(f, "{}", fail_judge),
        }
    }
}

pub struct StringTree(String, Vec<StringTree>);

fn map_derivation(der: &Derivation) -> StringTree {
    // StringTree(
    //     match &der.meta {
    //         crate::exp::Meta::Usual(string) => {
    //             format!("{} by {} [{}]", der.conclusion, der.rule, string)
    //         }
    //         crate::exp::Meta::Through(string) => {
    //             // der.premises.len() == 1 and we print this with meta info
    //             let first = der.premises.first().unwrap();
    //             let mut sttree = map_derivation(first);
    //             sttree.0 = format!("{} through [{string}]", sttree.0);
    //             return sttree;
    //         }
    //         crate::exp::Meta::Stop => {
    //             format!("{} by {} [stopped]", der.conclusion, der.rule)
    //         }
    //     },
    //     der.premises.iter().map(map_derivation).collect(),
    // )
    todo!()
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
