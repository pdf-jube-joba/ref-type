use std::fmt::Display;

use crate::{
    app,
    computation::{
        lambda_calculus::{alpha_eq, reduce, subst},
        typing::type_check,
    },
    environment::{derivation_tree::*, global_context::*, tree_node::*},
    prod,
    syntax::ast::{Exp, Sort, Var},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialDerivationTreeProof {
    pub head: ProvableJudgement,
    pub child: Vec<DerChild>,
    pub label: UserSelect,
}

impl PartialDerivationTreeProof {
    pub fn head(&self) -> &ProvableJudgement {
        &self.head
    }
    pub fn get_goals(&self) -> Vec<ProvableJudgement> {
        self.child.iter().flat_map(|c| c.get_goals()).collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UserSelect {
    // G |- e: t
    // G |= t
    Exact {
        proof: Exp,
    },
    // G |- t: b, G |- b: Power(a)
    // G |= Pred(a, b) t
    SubSetPred {
        term: Exp,
        subset: Exp,
        superset: Exp,
    },
    // G |- a: SET, G |- t1: a, G |- t2: a, G |- p: a -> PROP, G |= p t1
    // G |= p t2
    LeibnizEq {
        set: Exp,
        term1: Exp,
        term2: Exp,
        predicate: Exp,
    },
    // G |- a: SET, G |- b: Power(a), G |- t1: b, G |- t2: b, G |= t1 =(b) t2
    // G |= t1 =(a) t2
    EqualIntoSuper {
        set: Exp,
        term1: Exp,
        term2: Exp,
        superset: Exp,
    },
    // G |- a: SET, G |- b: Power(a), G |- t1: b, G |- t2: b, G |= t1 =(a) t2
    // G |= t1 =(b) t2
    EqualIntoSub {
        set: Exp,
        term1: Exp,
        term2: Exp,
        subset: Exp,
    },
    // G |- e: t, G |- t: SET
    // G |= exists t
    ExistExact {
        non_empty: Option<Exp>,
        element: Exp,
    },
    // G |- (take x: t. m): M, G |- e: t
    // G |= (take x: t. m) =_(M) m[x := e]
    EqualTake {
        take_var: Var,
        take_type: Exp,
        term: Exp,
        all: Exp,
        replace: Exp,
    },
    Applied {
        other: OtherSelect,
    },
}

impl Display for UserSelect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            UserSelect::Exact { proof } => format!("Exact: {proof}"),
            UserSelect::SubSetPred {
                term,
                subset,
                superset,
            } => format!("SubSetPred: {term} {subset} {superset}"),
            UserSelect::LeibnizEq {
                set,
                term1,
                term2,
                predicate,
            } => format!("LeibnizEq: {set} {term1} {term2} {predicate}"),
            UserSelect::EqualIntoSuper {
                set,
                term1,
                term2,
                superset,
            } => format!("EqualIntoSuper: {set} {term1} {term2} {superset}"),
            UserSelect::EqualIntoSub {
                set,
                term1,
                term2,
                subset,
            } => format!("EqualIntoSub: {set} {term1} {term2} {subset}"),
            UserSelect::ExistExact { non_empty, element } => {
                format!(
                    "ExistExact: {element} in {}",
                    if let Some(non_empty) = non_empty {
                        format!("{non_empty}")
                    } else {
                        "x".to_string()
                    }
                )
            }
            UserSelect::EqualTake {
                take_var,
                take_type,
                term,
                all,
                replace,
            } => format!("EqualTake: {take_var} {all} {take_type} {term} {replace}"),
            UserSelect::Applied { other } => format!("{other}"),
        };
        write!(f, "{s}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrProofTree {
    FailTree { fail_tree: DerivationFailed },
    FailCondition { condition: ErrOnCondition },
    NotAlphaEq,
    NotReduceble,
    NotAppropriateForm(String),
}

impl From<DerivationFailed> for ErrProofTree {
    fn from(value: DerivationFailed) -> Self {
        ErrProofTree::FailTree { fail_tree: value }
    }
}

impl From<ErrOnCondition> for ErrProofTree {
    fn from(value: ErrOnCondition) -> Self {
        ErrProofTree::FailCondition { condition: value }
    }
}

// G |= t を作る
pub fn proof_tree(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    proposition: Exp,
    user_label: UserSelect,
) -> Result<PartialDerivationTreeProof, ErrProofTree> {
    if let UserSelect::Applied { other } = user_label {
        return deformation_proof_tree(gcxt, cxt, proposition, other);
    }
    let head = ProvableJudgement {
        context: cxt.clone(),
        proposition: proposition.clone(),
    };
    let mut child: Vec<DerChild> = vec![];
    match &user_label {
        UserSelect::Exact { proof } => {
            let ok = type_check(gcxt, cxt.clone(), proof.clone(), proposition.clone())?;
            child.push(ok.into());
        }
        UserSelect::SubSetPred {
            term,
            subset,
            superset,
        } => {
            let predicate = Exp::pred_of_element(superset.clone(), subset.clone(), term.clone());
            if !alpha_eq(&proposition, &predicate) {
                return Err(ErrProofTree::NotAlphaEq);
            }

            let ok = type_check(gcxt, cxt.clone(), term.clone(), subset.clone())?;
            child.push(ok.into());

            let ok = type_check(
                gcxt,
                cxt.clone(),
                subset.clone(),
                Exp::Pow(Box::new(superset.clone())),
            )?;
            child.push(ok.into());
        }
        UserSelect::LeibnizEq {
            set,
            term1,
            term2,
            predicate,
        } => {
            // G |- set: SET, G |- term1: set, G |- term2: set, G |- p: set -> PROP, G |= p term1
            // G |= p term2

            let prop = app!(predicate.clone(), term2.clone());
            if !alpha_eq(&prop, &proposition) {
                return Err(ErrProofTree::NotAlphaEq);
            }

            // G |- set: SET
            let ok = type_check(gcxt, cxt.clone(), set.clone(), Sort::Set.into())?;
            child.push(ok.into());

            // G |- term1: set
            let ok = type_check(gcxt, cxt.clone(), term1.clone(), set.clone())?;
            child.push(ok.into());

            // G |- term2: set
            let ok = type_check(gcxt, cxt.clone(), term2.clone(), set.clone())?;
            child.push(ok.into());

            // G |- p: a -> PROP
            let ok = type_check(
                gcxt,
                cxt.clone(),
                predicate.clone(),
                prod! {Var::Unused, set.clone(), Sort::Prop.into()},
            )?;
            child.push(ok.into());

            // G |= p t1
            child.push(
                ProvableJudgement {
                    context: cxt.clone(),
                    proposition: app!(predicate.clone(), term1.clone()),
                }
                .into(),
            );
        }
        UserSelect::EqualIntoSuper {
            set,
            term1,
            term2,
            superset,
        } => {
            // G |- superset: SET, G |- set: Power(superset), G |- t1: set, G |- t2: set, G |= t1 =(set) t2
            // G |= t1 =(superset) t2

            let prop = Exp::id(superset.clone(), term1.clone(), term2.clone());
            if !alpha_eq(&prop, &proposition) {
                return Err(ErrProofTree::NotAlphaEq);
            }

            // G |- superset: SET
            let ok = type_check(gcxt, cxt.clone(), superset.clone(), Sort::Set.into())?;
            child.push(ok.into());

            // G |- set: Pow(superset)
            let ok = type_check(
                gcxt,
                cxt.clone(),
                set.clone(),
                Exp::Pow(Box::new(superset.clone())),
            )?;
            child.push(ok.into());

            // G |- t1: set
            let ok = type_check(gcxt, cxt.clone(), term1.clone(), set.clone())?;
            child.push(ok.into());

            // G |- t2: set
            let ok = type_check(gcxt, cxt.clone(), term2.clone(), set.clone())?;
            child.push(ok.into());

            // G |= t1 =(superset) t2
            child.push(
                ProvableJudgement {
                    context: cxt.clone(),
                    proposition: Exp::id(set.clone(), term1.clone(), term2.clone()),
                }
                .into(),
            );
        }
        UserSelect::EqualIntoSub {
            set,
            term1,
            term2,
            subset,
        } => {
            // G |- set: SET, G |- subset: Power(set), G |- t1: subset, G |- t2: subset, G |= t1 =(set) t2
            // G |= t1 =(subset) t2
            let prop = Exp::id(subset.clone(), term1.clone(), term2.clone());
            if !alpha_eq(&prop, &proposition) {
                return Err(ErrProofTree::NotAlphaEq);
            }

            // G |- set: SET
            let ok = type_check(gcxt, cxt.clone(), set.clone(), Sort::Set.into())?;
            child.push(ok.into());

            // G |- subset: Pow(set)
            let ok = type_check(
                gcxt,
                cxt.clone(),
                subset.clone(),
                Exp::Pow(Box::new(set.clone())),
            )?;
            child.push(ok.into());

            // G |- t1: set
            let ok = type_check(gcxt, cxt.clone(), term1.clone(), set.clone())?;
            child.push(ok.into());

            // G |- t2: set
            let ok = type_check(gcxt, cxt.clone(), term2.clone(), set.clone())?;
            child.push(ok.into());

            // G |= t1 =(subset) t2
            child.push(
                ProvableJudgement {
                    context: cxt.clone(),
                    proposition: Exp::id(set.clone(), term1.clone(), term2.clone()),
                }
                .into(),
            );
        }
        UserSelect::ExistExact { non_empty, element } => match non_empty {
            Some(non_empty) => {
                let prop = Exp::Exists(Box::new(non_empty.clone()));
                if !alpha_eq(&prop, &proposition) {
                    return Err(ErrProofTree::NotAlphaEq);
                }

                let ok = type_check(gcxt, cxt.clone(), element.clone(), non_empty.clone())?;
                child.push(ok.into());
            }
            None => {
                let Exp::Exists(set) = proposition else {
                    return Err(ErrProofTree::NotAppropriateForm(format!(
                        "not form exists but {proposition}"
                    )));
                };

                // G |- element: set
                let set = *set;
                let ok = type_check(gcxt, cxt.clone(), element.clone(), set.clone())?;
                child.push(ok.into());
            }
        },
        UserSelect::EqualTake {
            take_var,
            take_type,
            term,
            all,
            replace,
        } => {
            // G |- (take x: t. m): M, G |- e: t
            // G |= (take x: t. m) =_(M) m[x := e]

            let take = Exp::take(take_var.clone(), take_type.clone(), term.clone());
            let prop = Exp::id(
                all.clone(),
                take.clone(),
                subst(term.clone(), take_var, replace),
            );
            if !alpha_eq(&prop, &proposition) {
                return Err(ErrProofTree::NotAlphaEq);
            }

            // G |- (take x: t. m): M
            let ok = type_check(gcxt, cxt.clone(), take.clone(), all.clone())?;
            child.push(ok.into());

            // G |- replace: M
            let ok = type_check(gcxt, cxt.clone(), replace.clone(), take_type.clone())?;
            child.push(ok.into());
        }
        UserSelect::Applied { other: _ } => unreachable!(),
    }
    Ok(PartialDerivationTreeProof {
        head,
        child,
        label: user_label,
    })
}

// composition of others
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OtherSelect {
    // G |= T, T ~ T'
    // => G |= T'
    // by G |= T => G |- Proof(T): T => G |- Proof(T): T' => G |= T'
    Reduction { reduced: Option<Exp> },
}

impl Display for OtherSelect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OtherSelect::Reduction { reduced } => write!(
                f,
                "Reduce {}",
                if let Some(a) = reduced {
                    format!("{a}")
                } else {
                    "".to_string()
                }
            ),
        }
    }
}

fn deformation_proof_tree(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    proposition: Exp,
    other_select: OtherSelect,
) -> Result<PartialDerivationTreeProof, ErrProofTree> {
    let head = ProvableJudgement {
        context: cxt.clone(),
        proposition: proposition.clone(),
    };
    let mut child: Vec<DerChild> = vec![];

    match other_select.clone() {
        OtherSelect::Reduction { reduced } => {
            // G |= T, T ~ T'
            // => G |= T'
            // by G |= T => G |- Proof(T): T => G |- Proof(T): T' => G |= T'
            match reduced {
                Some(expected) => {
                    // G |- expected: PROP
                    let ok = type_check(gcxt, cxt.clone(), expected.clone(), Sort::Prop.into())?;
                    child.push(ok.into());

                    // expected =~ proposition
                    let ok = Condition::convertible(gcxt, expected.clone(), proposition.clone())?;
                    child.push(ok.into());

                    // G |= expected
                    let new_proposition = ProvableJudgement {
                        context: cxt.clone(),
                        proposition: expected,
                    };
                    child.push(new_proposition.into());
                }
                None => {
                    // just reduce (once) proposition
                    let Some(new_proposition) = reduce(gcxt, proposition.clone()) else {
                        return Err(ErrProofTree::NotReduceble);
                    };

                    let ok =
                        Condition::convertible(gcxt, new_proposition.clone(), proposition.clone())
                            .unwrap(); // it should be ok
                    child.push(ok.into());

                    let new_proposition = ProvableJudgement {
                        context: cxt.clone(),
                        proposition: new_proposition,
                    };
                    child.push(new_proposition.into());
                }
            }
        }
    }

    Ok(PartialDerivationTreeProof {
        head,
        child,
        label: UserSelect::Applied {
            other: other_select,
        },
    })
}
