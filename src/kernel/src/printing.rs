use std::fmt::{Debug, Display};

use crate::exp::{
    DefinedConstant, DerivationBase, DerivationFail, DerivationSuccess, FailHead, FailKind, GoalGenerated, ProveCommandBy, ProveGoal, SuccessHead, Var
};

// Convert the lower 32 bits of a pointer to a base62 string of fixed length 6.
// 62^6 = 56_800_235_584 > 2^32 = 4_294_967_296
fn ptr_lower32bit_base62_fixed(ptr: *const ()) -> String {
    const BASE62: &[u8; 62] = b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

    let mut n = (ptr as usize & 0xFFFF_FFFF) as u32;

    let mut buf = [0u8; 6];
    let mut i = 6;

    while n > 0 && i > 0 {
        i -= 1;
        buf[i] = BASE62[(n % 62) as usize];
        n /= 62;
    }

    while i > 0 {
        i -= 1;
        buf[i] = BASE62[0]; // '0'
    }

    String::from_utf8(buf.to_vec()).unwrap()
}

fn print_ptr<T>(ptr: *const T) -> String {
    ptr_lower32bit_base62_fixed(ptr as *const ())
}

fn print_rc_ptr<T>(rc: &std::rc::Rc<T>) -> String {
    ptr_lower32bit_base62_fixed(std::rc::Rc::as_ptr(rc) as *const ())
}

impl Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{}[{:p}]", self.as_str(), self.ptr())
        } else {
            write!(
                f,
                "{}\x1b[2m[{}]\x1b[0m",
                self.as_str(),
                print_ptr(self.ptr())
            )
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

impl Display for DefinedConstant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[: {} := {}]",
            self.ty,
            self.body
        )
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
            crate::exp::Exp::DefinedConstant(rc) => {
                write!(f, "{}{}", print_rc_ptr(rc), rc)
            }
            crate::exp::Exp::IndType {
                indspec,
                parameters,
            } => write!(
                f,
                "{}[{}]",
                print_rc_ptr(indspec),
                parameters
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            crate::exp::Exp::IndCtor {
                indspec,
                parameters,
                idx,
            } => write!(
                f,
                "{}.{}[{}]",
                print_rc_ptr(indspec),
                idx,
                parameters
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            crate::exp::Exp::IndElim {
                indspec,
                elim,
                return_type,
                cases,
            } => {
                write!(
                    f,
                    "elim {} \\in {} \\return {} with {{{}}}",
                    elim,
                    print_rc_ptr(indspec),
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

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Success(s) => write!(f, "\x1b[32m{}\x1b[0m", s),
            Node::ErrorPropagate(s) => write!(f, "\x1b[31m{}\x1b[0m", s),
            Node::ErrorCause(s) => write!(f, "\x1b[31;1m{}\x1b[0m", s),
            Node::Pending(s) => write!(f, "\x1b[33m{}\x1b[0m", s),
        }
    }
}

pub struct StringTree {
    pub head: Node,
    pub children: Vec<StringTree>,
}

pub fn map_derivation_success(derivation: &DerivationSuccess) -> StringTree {
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
        let StringTree { head, children } = map_derivation_success(&premises[0]);
        StringTree {
            head: Node::Success(format!("{} through {}[{}]", head, rule, phase)),
            children,
        }
    } else {
        let head = match head {
            SuccessHead::TypeJudgement { ctx, term, ty } => Node::Success(format!(
                "[{} |- {} : {}] {} [{}]",
                print_ctx(ctx),
                term,
                ty,
                rule,
                phase
            )),
            SuccessHead::ProofJudgement { ctx, prop } => Node::Success(format!(
                "[{} |= {}] {} [{}]",
                print_ctx(ctx),
                prop,
                rule,
                phase
            )),
            SuccessHead::WellFormednessInductive { ctx, indspec } => Node::Success(format!(
                "[{} |- wf_inductive {}]",
                print_ctx(ctx),
                print_rc_ptr(indspec),
            )),
            SuccessHead::Solve(derivation_success) => {
                let head = map_derivation_success(derivation_success);
                return StringTree {
                    head: Node::Success(format!("Solve goal{:p}", *derivation_success)),
                    children: vec![head],
                };
            }
        };
        let mut v = vec![];
        for premise in premises {
            v.push(map_derivation_success(premise));
        }
        for goal in generated_goals {
            let GoalGenerated {
                ctx,
                proposition,
                solvetree,
            } = goal;
            let head = match solvetree {
                Some(rc) => Node::Success(format!(
                    "!Solved[{} |= {}] via {:p}",
                    print_ctx(ctx),
                    proposition,
                    *rc
                )),
                None => Node::Pending(format!("!UnSolved[{} |= {}]", print_ctx(ctx), proposition)),
            };
            v.push(StringTree {
                head,
                children: vec![],
            });
        }
        StringTree { head, children: v }
    }
}

fn fmt_tree(f: &mut std::fmt::Formatter<'_>, tree: &StringTree, indent: usize) -> std::fmt::Result {
    for _ in 0..indent {
        write!(f, "  ")?;
    }
    writeln!(f, "{}", &tree.head)?;
    for child in &tree.children {
        fmt_tree(f, child, indent + 1)?;
    }
    Ok(())
}

impl Display for DerivationSuccess {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tree = map_derivation_success(self);
        fmt_tree(f, &tree, 0)
    }
}

pub fn map_derivation_fail(derivation: &DerivationFail) -> StringTree {
    let DerivationFail { base, head, kind } = derivation;

    let DerivationBase {
        premises,
        rule,
        phase,
    } = base.as_ref();

    let render = |node: Node, premises: &Vec<DerivationSuccess>, extra_child: Option<StringTree>| {
        let mut children = premises.iter().map(map_derivation_success).collect::<Vec<_>>();
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
            let head = match head {
                FailHead::TypeJudgement { ctx, term, ty } => Node::ErrorCause(format!(
                    "[{} |- {} : {}]{{{cause}}} {} [{}]",
                    print_ctx(ctx),
                    term,
                    match ty {
                        Some(ty) => ty.to_string(),
                        None => "<?>".to_string(),
                    },
                    rule,
                    phase
                )),
                FailHead::ProofJudgement { ctx, prop } => Node::ErrorCause(format!(
                    "[{} |= {}]{{{cause}}} {} [{}]",
                    print_ctx(ctx),
                    match prop {
                        Some(prop) => prop.to_string(),
                        None => "<?>".to_string(),
                    },
                    rule,
                    phase
                )),
                FailHead::WellFormednessInductive { ctx, indspec } => Node::ErrorCause(format!(
                    "[{} |- wf_inductive {}] {} [{}]",
                    print_ctx(ctx),
                    print_rc_ptr(indspec),
                    rule,
                    phase
                )),
                FailHead::Solve(derivation_success) => {
                    let tree = map_derivation_success(derivation_success);
                    let head = format!("solved but something wrong{:p}", *derivation_success);
                    return StringTree {
                        head: Node::ErrorCause(head),
                        children: vec![tree],
                    };
                }
            };
            render(head, premises, None)
        }
        FailKind::Propagate { fail, expect } => {
            let head = match head {
                FailHead::TypeJudgement { ctx, term, ty } => Node::ErrorPropagate(format!(
                    "[{} |- {} : {}]{{{expect}}} {} [{}]",
                    print_ctx(ctx),
                    term,
                    match ty {
                        Some(ty) => ty.to_string(),
                        None => "<?>".to_string(),
                    },
                    rule,
                    phase
                )),
                FailHead::ProofJudgement { ctx, prop } => Node::ErrorPropagate(format!(
                    "[{} |= {}]{{{expect}}} {} [{}]",
                    print_ctx(ctx),
                    match prop {
                        Some(prop) => prop.to_string(),
                        None => "<?>".to_string(),
                    },
                    rule,
                    phase
                )),
                FailHead::WellFormednessInductive { ctx, indspec } => Node::ErrorPropagate(format!(
                    "[{} |- wf_inductive {}] {} [{}]",
                    print_ctx(ctx),
                    print_rc_ptr(indspec),
                    rule,
                    phase
                )),
                FailHead::Solve(derivation_success) => {
                    let tree = map_derivation_success(derivation_success);
                    let head = format!("solved but something wrong{:p}", *derivation_success);
                    return StringTree {
                        head: Node::ErrorPropagate(head),
                        children: vec![tree],
                    };
                }
            };
            render(head, premises, Some(map_derivation_fail(fail)))
        }
    }
}

impl Display for DerivationFail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let tree = map_derivation_fail(self);
        fmt_tree(f, &tree, 0)
    }
}
