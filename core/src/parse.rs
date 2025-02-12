use std::fmt::Display;

use crate::ast::{inductives::*, *};
use crate::command::*;
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
            ParserError::Other(err) => format!("{err}"),
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
#[grammar = "exp.pest"] // relative to src
#[grammar = "proving.pest"]
#[grammar = "program.pest"]
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
                        Rule::smalls => (Var::Unused, take_smalls(e)?),
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
                    let mut e = take_smalls(p)?;
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

    pub(crate) fn take_smalls(pair: Pair<Rule>) -> Res<Exp> {
        debug_assert_eq!(pair.as_rule(), Rule::smalls);
        let mut p = pair.into_inner();
        let first = take_small(p.next().unwrap())?;
        let mut remains = vec![];
        for p in p {
            remains.push(take_small(p)?);
        }
        Ok(utils::assoc_apply(first, remains))
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

    #[cfg(test)]
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
    use crate::parse::parse_exp::take_expression;
    use crate::proving::UserSelect;

    use super::*;
    pub(crate) fn parse_proof(pair: Pair<Rule>) -> Result<UserSelect, Box<error::Error<Rule>>> {
        debug_assert_eq!(pair.as_rule(), Rule::PROOF);
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
            _ => unreachable!(),
        }
    }
}

pub mod parse_command {
    use crate::{
        environment::printing::TreeConfig,
        parse::parse_command::new_inductive_type_definition::take_new_inductive,
        proving::UserSelect,
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
                Ok(CommandAll::ParseCommand { exp: e }.into())
            }
            Rule::lambda_calculus_command => Ok(take_lambda_command(pair)?),
            Rule::typing_command => Ok(take_typing_command(pair)?),
            Rule::new_command => Ok(take_new_command(pair)?),
            Rule::show_command => Ok(take_show_command(pair)?),
            Rule::PROOF => {
                let user_select = parse_proof::parse_proof(pair)?;
                Ok(CommandAll::ProveGoal { user_select }.into())
            }
            _ => todo!("command not defined"),
        }
    }

    pub(crate) fn take_show_command(pair: Pair<Rule>) -> Res<CommandAll> {
        debug_assert_eq!(pair.as_rule(), Rule::show_command);
        let mut ps = pair.into_inner();
        let pair = ps.next().unwrap();
        match pair.as_rule() {
            Rule::show_goal => Ok(CommandAll::ShowGoal {}.into()),
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
                Ok(CommandAll::SubstCommand { e1, x, e2 }.into())
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
                Ok(CommandAll::AlphaEq { e1, e2, succ_flag }.into())
            }
            Rule::command_reduction => {
                let mut ps = pair.into_inner();
                let e = take_expression(ps.next().unwrap())?;
                Ok(CommandAll::Reduce { e }.into())
            }
            Rule::command_top_reduction => {
                let mut ps = pair.into_inner();
                let e = take_expression(ps.next().unwrap())?;
                Ok(CommandAll::TopReduce { e }.into())
            }
            Rule::command_normalize => {
                let mut ps = pair.into_inner();
                let e = take_expression(ps.next().unwrap())?;
                Ok(CommandAll::Normalize { e }.into())
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
                Ok(CommandAll::BetaEq { e1, e2, succ_flag }.into())
            }
            _ => unreachable!("lambda command"),
        }
    }

    pub(crate) fn take_typing_command(pair: Pair<Rule>) -> Res<CommandAll> {
        debug_assert_eq!(pair.as_rule(), Rule::typing_command);
        let mut ps = pair.into_inner();

        let succ_flag = if ps.peek().unwrap().as_rule() != Rule::FAIL {
            true
        } else {
            ps.next().unwrap();
            false
        };

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
                CommandAll::Check { e1, e2, config }.into()
            }
            Rule::command_infer => {
                let mut ps = pair.into_inner();
                let config = if ps.peek().unwrap().as_rule() == Rule::command_CONFIG {
                    take_tree_config(ps.next().unwrap())?
                } else {
                    TreeConfig::default()
                };
                let e = take_expression(ps.next().unwrap())?;
                CommandAll::Infer { e, config }.into()
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
                CommandAll::NewDefinition { x, t, e, config }.into()
            }
            Rule::new_assumption => {
                let (variable, expression, config) = take_new_assumption(pair)?;
                CommandAll::NewAssumption {
                    config,
                    x: variable,
                    t: expression,
                }
                .into()
            }
            Rule::new_inductive => {
                let (inductive, config) = take_new_inductive(pair)?;
                CommandAll::NewInductive {
                    inddefs: inductive,
                    config,
                }
                .into()
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
        use parse_command::parse_exp::{take_name, take_sort};
        use parse_exp::take_small;

        use super::*;

        impl Display for InductiveDefinitionsSyntax {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let InductiveDefinitionsSyntax {
                    type_name,
                    arity,
                    constructors,
                } = self;
                writeln!(f, "name: {type_name}")?;
                writeln!(
                    f,
                    "arity: {}",
                    utils::assoc_prod(arity.0.clone(), arity.1.into())
                )?;
                for (csname, params, end) in constructors {
                    write!(f, "constructor({csname}):")?;
                    for param in params {
                        write!(f, " {} ->", param)?;
                    }
                    writeln!(
                        f,
                        " {}",
                        utils::assoc_apply(end[0].clone(), end[1..].to_owned())
                    )?;
                }
                Ok(())
            }
        }

        impl Display for ParamCstSyntax {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let s = match self {
                    ParamCstSyntax::Positive((params, end)) => {
                        format!(
                            "Pos({})",
                            utils::assoc_prod(
                                params.clone(),
                                utils::assoc_apply(end[0].clone(), end[1..].to_owned())
                            )
                        )
                    }
                    ParamCstSyntax::Simple(param) => {
                        format!("Sim({}: {})", param.0, param.1)
                    }
                };
                write!(f, "{}", s)
            }
        }

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
                let e = take_expression(p)?;
                argument.push(e)
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
            let arity = take_arity(ps.next().unwrap())?;
            let constructors: Vec<_> = ps
                .map(|p| take_constructor_definition(p))
                .collect::<Result<_, _>>()?;
            Ok((
                InductiveDefinitionsSyntax {
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
