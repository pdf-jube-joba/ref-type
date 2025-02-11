use crate::{
    ast::{Exp, Var},
    environment::{derivation_tree::*, global_context::*, tree_node::*},
    lambda_calculus::alpha_eq,
    typing::type_check,
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
        self.child.iter().map(|c| c.get_goals()).flatten().collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UserSelect {
    Exact {
        proof: Exp,
    }, // G |- e: t => G |= t
    SubSetPred {
        term: Exp,
        subset: Exp,
        superset: Exp,
    }, // G |- t: B, G |- B: cal(A) => G |= Pred(A, B) t
    LeibnizEq {
        set: Exp,
        term1: Exp,
        term2: Exp,
        predicate: Exp,
    },
    EqualIntoSuper {
        set: Exp,
        term1: Exp,
        term2: Exp,
        superset: Exp,
    },
    EqualIntoSub {
        set: Exp,
        term1: Exp,
        term2: Exp,
        subset: Exp,
    },
    ExistExact {
        non_empty: Exp,
    },
    EqualTake {
        take_var: Var,
        take_type: Exp,
        term: Exp,
        replace: Exp,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrProofTree {
    FailTree {
        err: String,
        fail_tree: DerivationFailed,
    },
    NotAlphaEq,
}

// G |= t を作る
pub fn proof_tree(
    gcxt: &GlobalContext,
    mut cxt: LocalContext,
    proposition: Exp,
    user_label: UserSelect,
) -> Result<PartialDerivationTreeProof, ErrProofTree> {
    let head = ProvableJudgement {
        context: cxt.clone(),
        proposition: proposition.clone(),
    };
    match &user_label {
        UserSelect::Exact { proof } => {
            let ok = match type_check(gcxt, cxt.clone(), proof.clone(), proposition.clone()) {
                Ok(ok) => ok,
                Err(err) => {
                    return Err(ErrProofTree::FailTree {
                        err: format!("{cxt} |- {proof}: {proposition}"),
                        fail_tree: err,
                    });
                }
            };
            Ok(PartialDerivationTreeProof {
                head,
                label: user_label,
                child: vec![ok.into()],
            })
        }
        UserSelect::SubSetPred {
            term,
            subset,
            superset,
        } => {
            let predicate = Exp::pred_of_element(superset.clone(), subset.clone(), term.clone());
            if alpha_eq(&proposition, &predicate) {
                let tree1 = match type_check(gcxt, cxt.clone(), term.clone(), subset.clone()) {
                    Ok(ok) => ok,
                    Err(err) => {
                        return Err(ErrProofTree::FailTree {
                            err: format!("{cxt} |- {term}: {subset}"),
                            fail_tree: err,
                        });
                    }
                };
                let tree2 = match type_check(
                    gcxt,
                    cxt.clone(),
                    subset.clone(),
                    Exp::Pow(Box::new(superset.clone())),
                ) {
                    Ok(ok) => ok,
                    Err(err) => {
                        return Err(ErrProofTree::FailTree {
                            err: format!("{cxt} |- {subset}: {superset}"),
                            fail_tree: err,
                        });
                    }
                };
                Ok(PartialDerivationTreeProof {
                    head,
                    child: vec![tree1.into(), tree2.into()],
                    label: user_label,
                })
            } else {
                Err(ErrProofTree::NotAlphaEq)
            }
        }
        UserSelect::LeibnizEq {
            set,
            term1,
            term2,
            predicate,
        } => todo!(),
        UserSelect::EqualIntoSuper {
            set,
            term1,
            term2,
            superset,
        } => todo!(),
        UserSelect::EqualIntoSub {
            set,
            term1,
            term2,
            subset,
        } => todo!(),
        UserSelect::ExistExact { non_empty } => todo!(),
        UserSelect::EqualTake {
            take_var,
            take_type,
            term,
            replace,
        } => todo!(),
    }
}
