use crate::utils;
use std::fmt::Display;

use super::ast::{inductives::*, *};
use crate::core::command::*;
use pest::{error, iterators::Pair, Parser};
use pest_derive::Parser;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParserError {
    Parse(Box<error::Error<Rule>>),
    Other(String),
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ParserError::Parse(error) => format!("{error}"),
            ParserError::Other(err) => err.to_string(),
        };
        write!(f, "{}", s)
    }
}

impl From<Box<error::Error<Rule>>> for ParserError {
    fn from(value: Box<error::Error<Rule>>) -> Self {
        ParserError::Parse(value)
    }
}

impl From<error::Error<Rule>> for ParserError {
    fn from(value: error::Error<Rule>) -> Self {
        ParserError::Parse(Box::new(value))
    }
}

impl From<String> for ParserError {
    fn from(value: String) -> Self {
        ParserError::Other(value)
    }
}

#[derive(Default, Parser)]
#[grammar = "syntax/common.pest"]
#[grammar = "syntax/exp.pest"]
#[grammar = "syntax/proving.pest"]
#[grammar = "syntax/program.pest"]
pub struct MyParser;

impl MyParser {
    pub fn parse_exp(&mut self, code: &str) -> Result<Exp, ParserError> {
        let mut p = MyParser::parse(Rule::expression, code)?;
        let e = parse_exp::take_expression(p.next().unwrap())?;
        Ok(e)
    }
    pub fn parse_command(&mut self, code: &str) -> Result<CommandAll, ParserError> {
        let mut p = MyParser::parse(Rule::command, code)?;
        let e = parse_command::take_command(p.next().unwrap())?;
        Ok(e)
    }
}

mod parse_exp {
    use super::*;
    type Res<E> = Result<E, Box<error::Error<Rule>>>;

    pub(crate) fn take_sort(pair: Pair<Rule>) -> Res<Sort> {
        debug_assert_eq!(pair.as_rule(), Rule::sort);
        let ps = pair.into_inner();
        let p = ps.peek().unwrap();
        let sort = match p.as_rule() {
            Rule::sort_set => Sort::Set,
            Rule::sort_prop => Sort::Prop,
            Rule::sort_type => Sort::Type,
            Rule::sort_univ => {
                let p = p.into_inner().next().unwrap();
                let n: usize = p.as_str().parse().unwrap();
                Sort::Univ(n)
            }
            _ => unreachable!("sort の中に変なのがある"),
        };
        Ok(sort)
    }

    pub(crate) fn take_variable(pair: Pair<Rule>) -> Res<Var> {
        debug_assert_eq!(pair.as_rule(), Rule::variable);
        Ok(pair.as_str().into())
    }

    pub(crate) fn take_name(pair: Pair<Rule>) -> Res<String> {
        debug_assert_eq!(pair.as_rule(), Rule::name);
        Ok(pair.as_str().to_string())
    }

    pub(crate) fn take_expression(pair: Pair<Rule>) -> Res<Exp> {
        debug_assert_eq!(pair.as_rule(), Rule::expression);
        let mut v = vec![];
        for p in pair.into_inner() {
            match p.as_rule() {
                Rule::pre_arrows => {
                    let mut p = p.into_inner();
                    let e = p.next().unwrap();
                    let (x, a) = match e.as_rule() {
                        // true
                        Rule::smalls => (Var::Unused, utils::assoc_apply_vec(take_smalls(e)?)),
                        // false
                        Rule::var_annot => take_var_annnot(e)?,
                        _ => unreachable!("pre_arrow"),
                    };
                    let b = {
                        let e = p.next().unwrap();
                        let e = e.into_inner().next().unwrap();
                        match e.as_rule() {
                            Rule::prod => true,
                            Rule::lamd => false,
                            _ => unreachable!("delimitor"),
                        }
                    };
                    v.push((x, a, b));
                }
                Rule::smalls => {
                    let mut e = utils::assoc_apply_vec(take_smalls(p)?);
                    while let Some((x, a, b)) = v.pop() {
                        if b {
                            // prod
                            e = Exp::prod(x, a, e);
                        } else {
                            // lambda
                            e = Exp::lambda(x, a, e);
                        }
                    }
                    return Ok(e);
                }
                _ => unreachable!("take expression"),
            }
        }
        unreachable!("end of take expression")
    }

    pub(crate) fn take_smalls(pair: Pair<Rule>) -> Res<Vec<Exp>> {
        debug_assert_eq!(pair.as_rule(), Rule::smalls);
        let mut v = vec![];
        for p in pair.into_inner() {
            v.push(take_small(p)?);
        }
        Ok(v)
    }

    pub(crate) fn take_small(pair: Pair<Rule>) -> Res<Exp> {
        debug_assert_eq!(pair.as_rule(), Rule::small);
        let p = pair.into_inner().next().unwrap();
        match p.as_rule() {
            Rule::sort => Ok(Exp::Sort(take_sort(p)?)),
            Rule::app => {
                let mut p = p.into_inner();
                let first_exp = take_expression(p.next().unwrap())?;
                let others: Vec<_> = p.map(|p| take_expression(p)).collect::<Result<_, _>>()?;
                Ok(utils::assoc_apply(first_exp, others))
            }
            Rule::proof => {
                let mut p = p.into_inner();
                let e = take_expression(p.next().unwrap())?;
                Ok(Exp::Proof(Box::new(e)))
            }
            Rule::subset => {
                let mut p = p.into_inner();
                let (x, a) = take_var_annnot(p.next().unwrap())?;
                let e = take_expression(p.next().unwrap())?;
                Ok(Exp::Sub(x, Box::new(a), Box::new(e)))
            }
            Rule::powerset => {
                let mut p = p.into_inner();
                let e = take_expression(p.next().unwrap())?;
                Ok(Exp::Pow(Box::new(e)))
            }
            Rule::predicate => {
                let mut p = p.into_inner();
                let e1 = take_expression(p.next().unwrap())?;
                let e2 = take_expression(p.next().unwrap())?;
                Ok(Exp::Pred(Box::new(e1), Box::new(e2)))
            }
            Rule::ind_name => {
                let mut p = p.into_inner();
                let e = take_name(p.next().unwrap())?;
                Ok(Exp::IndTypeType {
                    ind_type_name: e.into(),
                })
            }
            Rule::ind_constructor => {
                let mut p = p.into_inner();
                let e1 = take_name(p.next().unwrap())?;
                let e2 = take_name(p.next().unwrap())?;
                Ok(Exp::IndTypeCst {
                    ind_type_name: e1.into(),
                    constructor_name: e2.into(),
                })
            }
            Rule::ind_elim => {
                let mut p = p.into_inner();
                let ind_name = take_name(p.next().unwrap())?;
                let matched = take_expression(p.next().unwrap())?;
                let return_type = take_expression(p.next().unwrap())?;
                let mut cases = vec![];
                while p.peek().is_some() {
                    let name = take_name(p.next().unwrap())?;
                    let exp = take_expression(p.next().unwrap())?;
                    cases.push((name.into(), exp));
                }
                Ok(Exp::IndTypeElim {
                    ind_type_name: ind_name.into(),
                    eliminated_exp: Box::new(matched),
                    return_type: Box::new(return_type),
                    cases,
                })
            }
            Rule::identity => {
                let mut p = p.into_inner();
                let e = take_expression(p.next().unwrap())?;
                let e1 = take_expression(p.next().unwrap())?;
                let e2 = take_expression(p.next().unwrap())?;
                Ok(Exp::Id(Box::new(e), Box::new(e1), Box::new(e2)))
            }
            Rule::identity_refl => {
                let mut p = p.into_inner();
                let e = take_expression(p.next().unwrap())?;
                let e1 = take_expression(p.next().unwrap())?;
                Ok(Exp::Refl(Box::new(e), Box::new(e1)))
            }
            Rule::exists => {
                let mut p = p.into_inner();
                let e = take_expression(p.next().unwrap())?;
                Ok(Exp::Exists(Box::new(e)))
            }
            Rule::take_operator => {
                let mut p = p.into_inner();
                let (x, a) = take_var_annnot(p.next().unwrap())?;
                let b = take_expression(p.next().unwrap())?;
                Ok(Exp::Take(x, Box::new(a), Box::new(b)))
            }
            Rule::variable => Ok(Exp::Var(take_variable(p)?)),
            _ => unreachable!("take small"),
        }
    }

    pub(crate) fn take_var_annnot(pair: Pair<Rule>) -> Res<(Var, Exp)> {
        debug_assert_eq!(pair.as_rule(), Rule::var_annot);
        let mut ps = pair.into_inner();
        let v = {
            let p = ps.next().unwrap();
            if p.as_rule() == Rule::unused_variable {
                Var::Unused
            } else {
                take_variable(p)?
            }
        };

        let e = {
            let p = ps.next().unwrap();
            take_expression(p)?
        };

        Ok((v, e))
    }

    mod tests {
        use super::*;
        use crate::{app, lam, prod, var};
        fn parse(code: &str) -> Res<Exp> {
            let mut p = MyParser::parse(Rule::expression, code)?;
            take_expression(p.next().unwrap())
        }
        #[test]
        fn a() {
            assert_eq!(parse("a").unwrap(), var! {"a"});
            assert_eq!(parse("ab").unwrap(), var! {"ab"});
            assert_eq!(parse("a b").unwrap(), app! { var!{"a"}, var!{"b"}});
            assert_eq!(
                parse("a b c d").unwrap(),
                app! { var!{"a"}, var!{"b"}, var!{"c"}, var!{"d"}}
            );

            assert_eq!(
                parse("a -> b").unwrap(),
                prod!(Var::Unused, var! {"a"}, var! {"b"})
            );

            assert_eq!(
                parse("(x: a) -> b").unwrap(),
                prod!("x".into(), var! {"a"}, var! {"b"})
            );

            assert_eq!(
                parse("(x: a) |-> b").unwrap(),
                lam!("x".into(), var! {"a"}, var! {"b"})
            );

            assert_eq!(
                parse("a1 a2 |-> (x: b1 b2) -> c1 c2").unwrap(),
                lam!(
                    Var::Unused,
                    app! {var!{"a1"}, var!{"a2"}},
                    prod! {"x".into(), app!{var!{"b1"}, var!{"b2"}}, app!(var!{"c1"}, var!{"c2"})}
                )
            );
        }

        #[test]
        fn comment() {
            MyParser::parse(Rule::COMMENT, "/* a1 */").unwrap();
            parse("a1 /* */ a2").unwrap();
            parse("a1 /*a**b**/ a2").unwrap();
            let e = parse("/* */ x /* test test ; */").unwrap();
            println!("{e}")
        }
    }
}

pub mod parse_proof {
    use super::*;
    use crate::computation::proving::{OtherSelect, UserSelect};
    use crate::syntax::parse::parse_exp::take_expression;

    pub(crate) fn parse_user_select(
        pair: Pair<Rule>,
    ) -> Result<UserSelect, Box<error::Error<Rule>>> {
        debug_assert_eq!(pair.as_rule(), Rule::PROOF_base);
        let mut ps = pair.into_inner();
        // let _ = ps.next().unwrap();
        let user_select = ps.next().unwrap();
        match user_select.as_rule() {
            Rule::exact_by_term => {
                let mut ps = user_select.into_inner();
                let proof = take_expression(ps.next().unwrap())?;
                Ok(UserSelect::Exact { proof })
            }
            Rule::subset_elim_prop => {
                let mut ps = user_select.into_inner();
                let term = take_expression(ps.next().unwrap())?;
                let subset = take_expression(ps.next().unwrap())?;
                let superset = take_expression(ps.next().unwrap())?;
                Ok(UserSelect::SubSetPred {
                    term,
                    subset,
                    superset,
                })
            }
            Rule::leibniz_eq => {
                let mut ps = user_select.into_inner();
                let term1 = take_expression(ps.next().unwrap())?;
                let term2 = take_expression(ps.next().unwrap())?;
                let set = take_expression(ps.next().unwrap())?;
                let predicate = take_expression(ps.next().unwrap())?;
                Ok(UserSelect::LeibnizEq {
                    set,
                    term1,
                    term2,
                    predicate,
                })
            }
            Rule::equal_into_super => {
                let mut ps = user_select.into_inner();
                let term1 = take_expression(ps.next().unwrap())?;
                let term2 = take_expression(ps.next().unwrap())?;
                let set = take_expression(ps.next().unwrap())?;
                let superset = take_expression(ps.next().unwrap())?;
                Ok(UserSelect::EqualIntoSuper {
                    set,
                    term1,
                    term2,
                    superset,
                })
            }
            Rule::equal_into_sub => {
                let mut ps = user_select.into_inner();
                let term1 = take_expression(ps.next().unwrap())?;
                let term2 = take_expression(ps.next().unwrap())?;
                let set = take_expression(ps.next().unwrap())?;
                let subset = take_expression(ps.next().unwrap())?;
                Ok(UserSelect::EqualIntoSub {
                    set,
                    term1,
                    term2,
                    subset,
                })
            }
            Rule::exist_refine => {
                let mut ps = user_select.into_inner();
                let element = take_expression(ps.next().unwrap())?;
                if ps.peek().is_some() {
                    let non_empty = take_expression(ps.next().unwrap())?;
                    Ok(UserSelect::ExistExact {
                        non_empty: Some(non_empty),
                        element,
                    })
                } else {
                    Ok(UserSelect::ExistExact {
                        non_empty: None,
                        element,
                    })
                }
            }
            _ => unreachable!("proof base"),
        }
    }
    pub(crate) fn parse_proof(pair: Pair<Rule>) -> Result<CommandAll, Box<error::Error<Rule>>> {
        debug_assert_eq!(pair.as_rule(), Rule::PROOF);
        let mut ps = pair.into_inner();
        // let _ = ps.next().unwrap();
        let user_select = ps.next().unwrap();
        match user_select.as_rule() {
            Rule::ADMIT => Ok(CommandAll::Admit),
            Rule::ADMIT_ALL => Ok(CommandAll::AdmitAll),
            Rule::PROOF_base => {
                let user_select = parse_user_select(user_select)?;
                Ok(CommandAll::ProveGoal { user_select })
            }
            Rule::applied_rule => {
                let other = take_applied_rule(user_select)?;
                Ok(CommandAll::ProveGoal {
                    user_select: UserSelect::Applied { other },
                })
            }
            _ => unreachable!(),
        }
    }

    fn take_applied_rule(pair: Pair<Rule>) -> Result<OtherSelect, Box<error::Error<Rule>>> {
        assert_eq!(pair.as_rule(), Rule::applied_rule);
        let pair = pair.into_inner().next().unwrap();
        match pair.as_rule() {
            Rule::reduce => {
                let mut ps = pair.into_inner();
                if ps.peek().is_some() {
                    let e = take_expression(ps.next().unwrap())?;
                    Ok(OtherSelect::Reduction { reduced: Some(e) })
                } else {
                    Ok(OtherSelect::Reduction { reduced: None })
                }
            }
            _ => unreachable!("applied rule"),
        }
    }
}

pub mod parse_command {
    use crate::{
        syntax::parse::parse_command::new_inductive_type_definition::take_new_inductive,
        syntax::printing::TreeConfig,
    };

    use super::parse_exp::take_expression;
    use super::*;
    type Res<E> = Result<E, Box<error::Error<Rule>>>;
    // use crate::interpreter::*;
    use parse_command::{
        // command::{Check, NewAssumption, NewDefinition, NewInductive, ParseCommand},
        parse_exp::{take_var_annnot, take_variable},
    };

    pub(crate) fn take_tree_config(pair: Pair<Rule>) -> Res<TreeConfig> {
        assert_eq!(pair.as_rule(), Rule::command_CONFIG);
        match pair.as_str() {
            "GOALS" => Ok(TreeConfig::OnlyGoals),
            "SUCCS" => Ok(TreeConfig::SuccTree),
            "ALL" => Ok(TreeConfig::AllCase),
            _ => unreachable!(""),
        }
    }
    pub(crate) fn take_command(pair: Pair<Rule>) -> Res<CommandAll> {
        debug_assert_eq!(pair.as_rule(), Rule::command);
        let mut ps = pair.into_inner();
        let pair = ps.next().unwrap();
        match pair.as_rule() {
            Rule::command_parse => {
                let mut ps = pair.into_inner();
                let e = take_expression(ps.next().unwrap())?;
                Ok(CommandAll::ParseCommand { exp: e })
            }
            Rule::lambda_calculus_command => Ok(take_lambda_command(pair)?),
            Rule::typing_command => Ok(take_typing_command(pair)?),
            Rule::new_command => Ok(take_new_command(pair)?),
            Rule::show_command => Ok(take_show_command(pair)?),
            Rule::PROOF => {
                let proof_command = parse_proof::parse_proof(pair)?;
                Ok(proof_command)
            }
            _ => todo!("command not defined"),
        }
    }

    pub(crate) fn take_show_command(pair: Pair<Rule>) -> Res<CommandAll> {
        debug_assert_eq!(pair.as_rule(), Rule::show_command);
        let mut ps = pair.into_inner();
        let pair = ps.next().unwrap();
        match pair.as_rule() {
            Rule::show_goal => Ok(CommandAll::ShowGoal {}),
            _ => unreachable!("show command"),
        }
    }

    pub(crate) fn take_lambda_command(pair: Pair<Rule>) -> Res<CommandAll> {
        debug_assert_eq!(pair.as_rule(), Rule::lambda_calculus_command);
        let mut ps = pair.into_inner();

        let pair = ps.next().unwrap();

        match pair.as_rule() {
            Rule::command_subst => {
                let mut ps = pair.into_inner();
                let e1 = take_expression(ps.next().unwrap())?;
                let x = take_variable(ps.next().unwrap())?;
                let e2 = take_expression(ps.next().unwrap())?;
                Ok(CommandAll::SubstCommand { e1, x, e2 })
            }
            Rule::command_alpha_eq => {
                let mut ps = pair.into_inner();
                let succ_flag = if ps.peek().unwrap().as_rule() != Rule::FAIL {
                    true
                } else {
                    ps.next().unwrap();
                    false
                };
                let e1 = take_expression(ps.next().unwrap())?;
                let e2 = take_expression(ps.next().unwrap())?;
                Ok(CommandAll::AlphaEq { e1, e2, succ_flag })
            }
            Rule::command_reduction => {
                let mut ps = pair.into_inner();
                let e = take_expression(ps.next().unwrap())?;
                Ok(CommandAll::Reduce { e })
            }
            Rule::command_top_reduction => {
                let mut ps = pair.into_inner();
                let e = take_expression(ps.next().unwrap())?;
                Ok(CommandAll::TopReduce { e })
            }
            Rule::command_normalize => {
                let mut ps = pair.into_inner();
                let b = if ps.peek().unwrap().as_rule() == Rule::normalize_opt {
                    ps.next();
                    true
                } else {
                    false
                };
                let e = take_expression(ps.next().unwrap())?;
                Ok(CommandAll::Normalize { e, process: b })
            }
            Rule::command_beta_equiv => {
                let mut ps = pair.into_inner();
                let succ_flag = if ps.peek().unwrap().as_rule() != Rule::FAIL {
                    true
                } else {
                    ps.next().unwrap();
                    false
                };
                let e1 = take_expression(ps.next().unwrap())?;
                let e2 = take_expression(ps.next().unwrap())?;
                Ok(CommandAll::BetaEq { e1, e2, succ_flag })
            }
            _ => unreachable!("lambda command"),
        }
    }

    pub(crate) fn take_typing_command(pair: Pair<Rule>) -> Res<CommandAll> {
        debug_assert_eq!(pair.as_rule(), Rule::typing_command);
        let mut ps = pair.into_inner();

        let pair = ps.next().unwrap();

        let res: CommandAll = match pair.as_rule() {
            Rule::command_check => {
                let mut ps = pair.into_inner();
                let config = if ps.peek().unwrap().as_rule() == Rule::command_CONFIG {
                    take_tree_config(ps.next().unwrap())?
                } else {
                    TreeConfig::default()
                };
                let e1 = take_expression(ps.next().unwrap())?;
                let e2 = take_expression(ps.next().unwrap())?;
                CommandAll::Check { e1, e2, config }
            }
            Rule::command_infer => {
                let mut ps = pair.into_inner();
                let config = if ps.peek().unwrap().as_rule() == Rule::command_CONFIG {
                    take_tree_config(ps.next().unwrap())?
                } else {
                    TreeConfig::default()
                };
                let e = take_expression(ps.next().unwrap())?;
                CommandAll::Infer { e, config }
            }
            Rule::command_theorem => {
                let mut ps = pair.into_inner();
                let config = if ps.peek().unwrap().as_rule() == Rule::command_CONFIG {
                    take_tree_config(ps.next().unwrap())?
                } else {
                    TreeConfig::default()
                };
                let e = take_expression(ps.next().unwrap())?;
                CommandAll::Theorem { e, config }
            }
            _ => unreachable!("typing command"),
        };

        Ok(res)
    }

    pub(crate) fn take_new_command(pair: Pair<Rule>) -> Res<CommandAll> {
        debug_assert_eq!(pair.as_rule(), Rule::new_command);
        let mut ps = pair.into_inner();

        let succ_flag = if ps.peek().unwrap().as_rule() != Rule::FAIL {
            true
        } else {
            ps.next().unwrap();
            false
        };

        let pair = ps.next().unwrap();

        let res: CommandAll = match pair.as_rule() {
            Rule::new_definition => {
                let (x, t, e, config) = take_new_definition(pair)?;
                CommandAll::NewDefinition { x, t, e, config }
            }
            Rule::new_assumption => {
                let (variable, expression, config) = take_new_assumption(pair)?;
                CommandAll::NewAssumption {
                    config,
                    x: variable,
                    t: expression,
                }
            }
            Rule::new_inductive => {
                let (inductive, config) = take_new_inductive(pair)?;
                CommandAll::NewInductive {
                    inddefs: inductive,
                    config,
                }
            }
            _ => unreachable!("new command"),
        };

        Ok(res)
    }

    pub(crate) fn take_new_assumption(pair: Pair<Rule>) -> Res<(Var, Exp, TreeConfig)> {
        debug_assert_eq!(pair.as_rule(), Rule::new_assumption);
        let mut ps = pair.into_inner();
        let config = if ps.peek().unwrap().as_rule() == Rule::command_CONFIG {
            take_tree_config(ps.next().unwrap())?
        } else {
            TreeConfig::default()
        };
        let variable = {
            let p = ps.next().unwrap();
            take_variable(p)?
        };
        let expression = {
            let p = ps.next().unwrap();
            take_expression(p)?
        };
        Ok((variable, expression, config))
    }

    pub(crate) fn take_new_definition(pair: Pair<Rule>) -> Res<(Var, Exp, Exp, TreeConfig)> {
        debug_assert_eq!(pair.as_rule(), Rule::new_definition);
        let mut ps = pair.into_inner();
        let config = if ps.peek().unwrap().as_rule() == Rule::command_CONFIG {
            take_tree_config(ps.next().unwrap())?
        } else {
            TreeConfig::default()
        };
        let variable = {
            let p = ps.next().unwrap();
            take_variable(p)?
        };
        let mut var_annots: Vec<(Var, Exp)> = vec![];
        loop {
            if ps.peek().unwrap().as_rule() == Rule::expression {
                break;
            };
            let p = ps.next().unwrap();
            let (x, e) = take_var_annnot(p)?;
            var_annots.push((x, e));
        }
        let expression1 = {
            let p = ps.next().unwrap();
            let e = take_expression(p)?;
            utils::assoc_prod(var_annots.clone(), e)
        };
        let expression2 = {
            let p = ps.next().unwrap();
            let e = take_expression(p)?;
            utils::assoc_lam(var_annots, e)
        };
        Ok((variable, expression1, expression2, config))
    }

    pub mod new_inductive_type_definition {
        use new_inductive_type_definition::parse_command::parse_exp::take_smalls;
        use parse_command::parse_exp::{take_name, take_sort};
        use parse_exp::take_small;

        use super::*;

        pub(crate) fn take_arity(pair: Pair<Rule>) -> Res<(Vec<(Var, Exp)>, Sort)> {
            debug_assert_eq!(pair.as_rule(), Rule::arity);
            let mut ps = pair.into_inner();
            let mut signature = vec![];
            loop {
                let p = ps.next().unwrap();
                if p.as_rule() == Rule::var_annot {
                    let exp = take_var_annnot(p)?;
                    signature.push(exp);
                } else {
                    let sort = take_sort(p)?;
                    return Ok((signature, sort));
                }
            }
        }

        pub(crate) fn take_terminate(pair: Pair<Rule>) -> Res<Vec<Exp>> {
            debug_assert_eq!(pair.as_rule(), Rule::constructor_terminate);
            let mut ps = pair.into_inner();
            let v = take_name(ps.next().unwrap())?;
            let mut argument = vec![Exp::Var(v.into())];
            for p in ps {
                argument.push(take_small(p)?);
            }
            Ok(argument)
        }

        pub(crate) fn take_positive(pair: Pair<Rule>) -> Res<(Vec<(Var, Exp)>, Vec<Exp>)> {
            debug_assert_eq!(pair.as_rule(), Rule::positive);
            let mut ps = pair.into_inner();
            let mut parameter = vec![];
            loop {
                let p = ps.next().unwrap();
                if p.as_rule() == Rule::var_annot {
                    let exp = take_var_annnot(p)?;
                    parameter.push(exp);
                } else {
                    let exps = take_terminate(p)?;
                    return Ok((parameter, exps));
                }
            }
        }

        pub(crate) fn take_simple(pair: Pair<Rule>) -> Res<(Var, Exp)> {
            debug_assert!(matches!(pair.as_rule(), Rule::var_annot | Rule::small));
            match pair.as_rule() {
                Rule::var_annot => take_var_annnot(pair),
                Rule::small => {
                    let e = take_small(pair)?;
                    Ok((Var::Unused, e))
                }
                _ => unreachable!("take simple"),
            }
        }

        pub(crate) fn take_constructor_definition(
            pair: Pair<Rule>,
        ) -> Res<(String, Vec<ParamCstSyntax>, Vec<Exp>)> {
            debug_assert_eq!(pair.as_rule(), Rule::constructor_definition);
            let mut ps = pair.into_inner();
            let name = take_name(ps.next().unwrap())?;
            let mut params = vec![];
            for p in ps {
                match p.as_rule() {
                    Rule::var_annot | Rule::small => {
                        let p = take_simple(p)?;
                        params.push(ParamCstSyntax::Simple(p));
                    }
                    Rule::positive => {
                        let p = take_positive(p)?;
                        params.push(ParamCstSyntax::Positive(p));
                    }
                    Rule::constructor_terminate => {
                        let end = take_terminate(p)?;
                        return Ok((name, params, end));
                    }
                    _ => unreachable!(" take cons def inner"),
                }
            }
            unreachable!(" take constructor definition")
        }

        pub(crate) fn take_new_inductive(
            pair: Pair<Rule>,
        ) -> Res<(InductiveDefinitionsSyntax, TreeConfig)> {
            debug_assert_eq!(pair.as_rule(), Rule::new_inductive);
            let mut ps = pair.into_inner();
            let config = if ps.peek().unwrap().as_rule() == Rule::command_CONFIG {
                take_tree_config(ps.next().unwrap())?
            } else {
                TreeConfig::default()
            };
            let type_name = take_name(ps.next().unwrap())?;
            let parameter = {
                let mut parameter = vec![];
                while ps.peek().unwrap().as_rule() == Rule::var_annot {
                    let xa = take_var_annnot(ps.next().unwrap())?;
                    parameter.push(xa);
                }
                parameter
            };
            let arity = take_arity(ps.next().unwrap())?;
            let constructors: Vec<_> = ps
                .map(|p| take_constructor_definition(p))
                .collect::<Result<_, _>>()?;
            Ok((
                InductiveDefinitionsSyntax {
                    parameter,
                    type_name,
                    arity,
                    constructors,
                },
                config,
            ))
        }

        #[cfg(test)]
        mod tests {
            use super::*;
            #[test]
            fn defs() {
                MyParser::parse(Rule::arity, "(a: b) -> (c: d) -> PROP").unwrap();
                let code = "Inductive Nat: PROP with
                    | Nil: A
                    ";
                match MyParser::parse(Rule::new_inductive, code) {
                    Ok(p) => {
                        let syntax = take_new_inductive(p.into_iter().next().unwrap()).unwrap();
                        println!("{syntax:?}")
                    }
                    Err(err) => {
                        println!("{err}")
                    }
                }
            }
        }
    }
}
