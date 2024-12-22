use pest::{
    error,
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::Parser;

use super::{inductives::*, *};

#[derive(Default, Parser)]
#[grammar = "ast.pest"] // relative to src
struct MyParser {
    global_context: GlobalContext,
}

impl MyParser {
    fn parse_code(str: &str) -> Result<ResultCommand, String> {
        todo!()
    }
}

pub fn parse_command(str: &str) -> Result<ResultCommand, String> {
    match MyParser::parse(Rule::command, str) {
        Ok(command) => {
            let p = command.into_iter();
            let p = p.peek().unwrap();
            take_command(p).map_err(|err| format!("{err:?}"))
        }
        Err(err) => Err(format!("{err:?}")),
    }
}

pub enum ResultCommand {
    Parse(Exp),
    Check(Exp, Exp, Result<(), String>),
    Infer(Exp, Result<Exp, String>),
}

pub(crate) fn take_command(pair: Pair<Rule>) -> Result<ResultCommand, error::Error<Rule>> {
    debug_assert_eq!(pair.as_rule(), Rule::command);
    let pair = pair.into_inner().peek().unwrap();
    match pair.as_rule() {
        Rule::command_parse => {
            let mut ps = pair.into_inner();
            let e = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            Ok(ResultCommand::Parse(e))
        }
        Rule::command_check => {
            let mut ps = pair.into_inner();
            let e1 = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            let e2 = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            // let r = relation::type_check(&GlobalContext::new(), e1.clone(), e2.clone());
            // Ok(ResultCommand::Check(e1, e2, r))
            todo!()
        }
        _ => todo!("command not defined"),
    }
}

type Res<E> = Result<E, error::Error<Rule>>;

pub(crate) fn take_exp(pair: Pair<Rule>) -> Res<Exp> {
    debug_assert_eq!(pair.as_rule(), Rule::expression);
    let ps = pair.into_inner();
    let p = ps.peek().unwrap();
    match p.as_rule() {
        Rule::sort => {
            let s = take_sort(p).unwrap();
            Ok(Exp::Sort(s))
        }
        Rule::dependent_prod_form => {
            let (x, e1, e2) = take_dependent_prod_form(p).unwrap();
            Ok(Exp::Prod(x, Box::new(e1), Box::new(e2)))
        }
        Rule::dependent_prod_intro => {
            let (x, e1, e2) = take_dependent_prod_intro(p).unwrap();
            Ok(Exp::Lam(x, Box::new(e1), Box::new(e2)))
        }
        Rule::dependent_prod_elim => {
            let (e1, e2) = take_dependent_prod_elim(p).unwrap();
            Ok(Exp::App(Box::new(e1), Box::new(e2)))
        }
        Rule::identifier => {
            let x = take_identifier(p).unwrap();
            Ok(Exp::Var(x))
        }
        Rule::expression_readable => {
            let ps = p.into_inner();
            let p = ps.peek().unwrap();
            take_exp(p)
        }
        _ => unreachable!(),
    }
}

pub(crate) fn take_sort(pair: Pair<Rule>) -> Res<Sort> {
    debug_assert_eq!(pair.as_rule(), Rule::sort);
    let ps = pair.into_inner();
    let p = ps.peek().unwrap();
    let sort = match p.as_rule() {
        Rule::sort_set => Sort::Set,
        Rule::sort_prop => Sort::Prop,
        Rule::sort_type => Sort::Type,
        _ => unreachable!("sort の中に変なのがある"),
    };
    Ok(sort)
}

pub(crate) fn take_identifier(pair: Pair<Rule>) -> Res<Var> {
    debug_assert_eq!(pair.as_rule(), Rule::identifier);
    Ok(pair.as_str().into())
}

pub(crate) fn take_var_annnot(pair: Pair<Rule>) -> Res<(Var, Exp)> {
    debug_assert_eq!(pair.as_rule(), Rule::var_annot);
    let mut ps = pair.into_inner();
    let v = {
        let p = ps.next().unwrap();
        take_identifier(p)?
    };

    let e = {
        let p = ps.next().unwrap();
        take_exp(p)?
    };

    Ok((v, e))
}

pub(crate) fn take_dependent_prod_form(pair: Pair<Rule>) -> Res<(Var, Exp, Exp)> {
    debug_assert_eq!(pair.as_rule(), Rule::dependent_prod_form);
    let mut ps = pair.into_inner();
    let (v, e) = {
        let p = ps.next().unwrap();
        take_var_annnot(p)?
    };

    let e2 = {
        let p = ps.next().unwrap();
        take_exp(p)?
    };

    Ok((v, e, e2))
}

pub(crate) fn take_dependent_prod_intro(pair: Pair<Rule>) -> Res<(Var, Exp, Exp)> {
    debug_assert_eq!(pair.as_rule(), Rule::dependent_prod_intro);
    let mut ps = pair.into_inner();
    let (v, e) = {
        let p = ps.next().unwrap();
        take_var_annnot(p)?
    };

    let e2 = {
        let p = ps.next().unwrap();
        take_exp(p)?
    };

    Ok((v, e, e2))
}

pub(crate) fn take_dependent_prod_elim(pair: Pair<Rule>) -> Res<(Exp, Exp)> {
    debug_assert_eq!(pair.as_rule(), Rule::dependent_prod_elim);
    let mut ps = pair.into_inner();
    let e1 = {
        let p = ps.next().unwrap();
        take_exp(p)?
    };
    let e2 = {
        let p = ps.next().unwrap();
        take_exp(p)?
    };
    Ok((e1, e2))
}

pub(crate) fn take_arity(pair: Pair<Rule>) -> Res<Arity> {
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
            let arity = Arity::new(signature, sort);
            return Ok(arity.unwrap()); // あとでちゃんとエラー分ける
        }
    }
}

pub(crate) fn take_terminate(pair: Pair<Rule>) -> Res<(Var, Vec<Exp>)> {
    debug_assert_eq!(pair.as_rule(), Rule::constructor_terminate);
    let mut ps = pair.into_inner();
    let v = {
        let p = ps.next().unwrap();
        take_identifier(p)?
    };
    let mut argument = vec![];
    for p in ps {
        let e = take_exp(p)?;
        argument.push(e)
    }
    Ok((v, argument))
}

pub(crate) fn take_positive(pair: Pair<Rule>) -> Res<Positive> {
    debug_assert_eq!(pair.as_rule(), Rule::positive);
    let mut ps = pair.into_inner();
    let mut signature = vec![];
    loop {
        let p = ps.next().unwrap();
        if p.as_rule() == Rule::var_annot {
            let exp = take_var_annnot(p)?;
            signature.push(exp);
        } else {
            let (variable, exps) = take_terminate(p)?;
            return Ok(Positive {
                parameter: signature,
                variable,
                exps,
            });
        }
    }
}

pub(crate) fn take_constructor_rec(pair: Pair<Rule>) -> Res<ConstructorType> {
    debug_assert_eq!(pair.as_rule(), Rule::constructor_rec);
    let mut ps = pair.into_inner();
    let p = ps.next().unwrap();
    match p.as_rule() {
        Rule::constructor_terminate => {
            let terminate = take_terminate(p)?;
            Ok(ConstructorType::End(terminate.0, terminate.1))
        }
        Rule::constructor_non_occur => {
            let mut ps = p.into_inner();
            let (v, a) = take_var_annnot(ps.next().unwrap())?;
            let rem = take_constructor_rec(ps.next().unwrap())?;
            Ok(ConstructorType::Map((v, a), Box::new(rem)))
        }
        Rule::constructor_positive_occur => {
            let mut ps = p.into_inner();
            let positive = take_positive(ps.next().unwrap())?;
            let rem = take_constructor_rec(ps.next().unwrap())?;
            Ok(ConstructorType::PosToCst(positive, Box::new(rem)))
        }
        _ => unreachable!("constructor_rec 中"),
    }
}

pub(crate) fn take_new_inductive(pair: Pair<Rule>) -> Res<(IndTypeDefs, String, Vec<String>)> {
    debug_assert_eq!(pair.as_rule(), Rule::new_inductive);
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parse_test() {
        let var = "xyz";
        let ps = MyParser::parse(Rule::identifier, var).unwrap();
        let p = ps.peek().unwrap();
        let v = parse::take_identifier(p).unwrap();
        assert_eq!(v, Var::from(var.to_string()));
    }
}
