use pest::{
    error,
    iterators::{Pair, Pairs},
    Parser,
};
use pest_derive::Parser;

use super::*;
#[derive(Parser)]
#[grammar = "ast.pest"] // relative to src
struct MyParser;

pub fn parse_command(str: &str) -> Result<ResultCommand, String> {
    match MyParser::parse(Rule::command, str) {
        Ok(command) => {
            let p = command.into_iter();
            let p = p.peek().unwrap();
            take_command(p)
        }
        Err(err) => Err(format!("{err:?}")),
    }
}

pub enum ResultCommand {
    Parse(Exp),
    Check(Exp, Exp, Result<(), String>),
    Infer(Exp, Result<Exp, String>),
}

pub(crate) fn take_command(pair: Pair<Rule>) -> Result<ResultCommand, String> {
    debug_assert_eq!(pair.as_rule(), Rule::command);
    let pair = pair.into_inner().peek().unwrap();
    match pair.as_rule() {
        Rule::command_parse => {
            let mut ps = pair.into_inner();
            let p = ps.next().unwrap();
            match take_exp(p) {
                Ok(exp) => Ok(ResultCommand::Parse(exp)),
                Err(err) => Err(format!("{err:?}")),
            }
        }
        _ => unreachable!(),
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
