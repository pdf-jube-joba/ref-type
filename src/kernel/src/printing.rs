use std::fmt::{Debug, Display};

use crate::exp::{ProveCommandBy, ProveGoal, Var};

impl Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{}[{:p}]", self.as_str(), self.ptr())
        } else {
            write!(f, "{}\x1b[2m[{:p}]\x1b[0m", self.as_str(), self.ptr())
        }
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
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
                indspec: ty,
                parameters,
            } => write!(
                f,
                "{}{{{}}}",
                ty.names.0,
                parameters
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            crate::exp::Exp::IndCtor {
                indspec: ty,
                parameters,
                idx,
            } => write!(
                f,
                "{}.{}{{{}}}",
                ty.names.0,
                ty.names.1.get(*idx).unwrap(),
                parameters
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            crate::exp::Exp::IndElim {
                indspec: ty,
                elim,
                return_type,
                cases,
            } => {
                write!(
                    f,
                    "elim {} \\in {} \\return {} with {{{}}}",
                    elim,
                    ty.names.0,
                    return_type,
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
            crate::exp::Exp::ProofTermRaw { command } => {
                write!(f, "proof_term({})", command)
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
                write!(f, "\\exists {}", set)
            }
            crate::exp::Exp::Take { map } => {
                write!(f, "\\Take {}", map)
            }
        }
    }
}

impl Display for ProveCommandBy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            crate::exp::ProveCommandBy::Construct(proof_term) => {
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
        }
    }
}

fn print_ctx(ctx: &crate::exp::Context) -> String {
    ctx.iter()
        .map(|(var, ty)| format!("{}: {}", var, ty))
        .collect::<Vec<_>>()
        .join(", ")
}

impl Display for ProveGoal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ProveGoal {
            extended_ctx,
            goal_prop,
            command,
        } = self;
        write!(
            f,
            "[..  {} |= {} by {}]",
            print_ctx(extended_ctx),
            goal_prop,
            command,
        )
    }
}

pub enum Node {
    Success(String),
    ErrorPropagate(String),
    ErrorCause(String),
    Pending(String),
}

pub struct StringTree {
    pub head: Node,
    pub children: Vec<StringTree>,
}

// pub fn map_derivation(der: &DerivationSuccess) -> StringTree {
//     match der {
//         Derivation::DerivationSuccess {
//             conclusion,
//             premises,
//             rule,
//             meta,
//         } => {
//             match meta {
//                 crate::exp::Meta::Usual(string) => StringTree {
//                     head: Node::Success(format!("{} by {} [{}]", conclusion, rule, string)),
//                     children: premises.iter().map(map_derivation).collect(),
//                 },
//                 crate::exp::Meta::Through(string) => {
//                     // premises.len() == 1 and we print this with meta info
//                     let first = premises.first().unwrap();
//                     let mut sttree = map_derivation(first);
//                     sttree.head = Node::Success(format!(
//                         "{} through [{}]",
//                         match &sttree.head {
//                             Node::Success(s) => s,
//                             Node::Error(s) => s,
//                             Node::Pending(s) => s,
//                         },
//                         string
//                     ));
//                     sttree
//                 }
//             }
//         }
//         Derivation::DerivationFail {
//             conclusion,
//             premises,
//             rule,
//             meta,
//         } => {
//             match meta {
//                 crate::exp::Meta::Usual(string) => StringTree {
//                     head: Node::Error(format!("{} by {} [{}]", conclusion, rule, string)),
//                     children: premises.iter().map(map_derivation).collect(),
//                 },
//                 crate::exp::Meta::Through(string) => {
//                     // premises.len() == 1 and we print this with meta info
//                     let first = premises.first().unwrap();
//                     let mut sttree = map_derivation(first);
//                     sttree.head = Node::Error(format!(
//                         "{} through [{}]",
//                         match &sttree.head {
//                             Node::Success(s) => s,
//                             Node::Error(s) => s,
//                             Node::Pending(s) => s,
//                         },
//                         string
//                     ));
//                     sttree
//                 }
//             }
//         }
//         Derivation::GoalGenerated {
//             proposition,
//             solvetree,
//         } => {
//             let head = match solvetree {
//                 Some(rc) => Node::Success(format!("{proposition}[Solve by {:p}]", rc.as_ref())),
//                 None => Node::Pending(format!("{proposition}[Not yet solved]")),
//             };
//             StringTree {
//                 head,
//                 children: vec![],
//             }
//         }
//         Derivation::SolveSuccess(proof_tree) => {
//             let ProofTree {
//                 conclusion,
//                 premises,
//                 rule,
//                 meta,
//             } = proof_tree.as_ref();
//             match meta {
//                 crate::exp::Meta::Usual(string) => StringTree {
//                     head: Node::Success(format!("{} by {} [{}]", conclusion, rule, string)),
//                     children: premises.iter().map(map_derivation).collect(),
//                 },
//                 crate::exp::Meta::Through(string) => {
//                     // premises.len() == 1 and we print this with meta info
//                     let first = premises.first().unwrap();
//                     let mut sttree = map_derivation(first);
//                     sttree.head = Node::Success(format!(
//                         "{} through [{}]",
//                         match &sttree.head {
//                             Node::Success(s) => s,
//                             Node::Error(s) => s,
//                             Node::Pending(s) => s,
//                         },
//                         string
//                     ));
//                     sttree
//                 }
//             }
//         }
//         Derivation::SolveFail {
//             conclusion,
//             premises,
//             rule,
//             meta,
//         } => {
//             match meta {
//                 crate::exp::Meta::Usual(string) => StringTree {
//                     head: Node::Error(format!("{} by {} [{}]", conclusion, rule, string)),
//                     children: premises.iter().map(map_derivation).collect(),
//                 },
//                 crate::exp::Meta::Through(string) => {
//                     // premises.len() == 1 and we print this with meta info
//                     let first = premises.first().unwrap();
//                     let mut sttree = map_derivation(first);
//                     sttree.head = Node::Error(format!(
//                         "{} through [{}]",
//                         match &sttree.head {
//                             Node::Success(s) => s,
//                             Node::Error(s) => s,
//                             Node::Pending(s) => s,
//                         },
//                         string
//                     ));
//                     sttree
//                 }
//             }
//         }
//     }
// }

// fn fmt_tree(f: &mut std::fmt::Formatter<'_>, tree: &StringTree, indent: usize) -> std::fmt::Result {
//     for _ in 0..indent {
//         write!(f, "  ")?;
//     }
//     writeln!(
//         f,
//         "{}",
//         match &tree.head {
//             Node::Success(s) => format!("\x1b[32m{}\x1b[0m", s),
//             Node::Error(s) => format!("\x1b[31m{}\x1b[0m", s),
//             Node::Pending(s) => format!("\x1b[33m{}\x1b[0m", s),
//         }
//     )?;
//     for child in &tree.children {
//         fmt_tree(f, child, indent + 1)?;
//     }
//     Ok(())
// }

// impl Display for Derivation {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         let tree = map_derivation(self);
//         fmt_tree(f, &tree, 0)
//     }
// }
