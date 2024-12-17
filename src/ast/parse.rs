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

pub fn parse_str(str: &str) -> Result<Exp, String> {
    match MyParser::parse(Rule::expression, str) {
        Ok(exp) => {
            let Some(pair) = exp.peek() else {
                return Err("no pair found".to_string());
            };
            let result = take_exp(pair);
            match result {
                Ok(exp) => Ok(exp),
                Err(err) => Err(format!("{err}")),
            }
        }
        Err(err) => Err(format!("{err}")),
    }
}

type Res<E> = Result<E, error::Error<Rule>>;

pub(crate) fn take_exp(pair: Pair<Rule>) -> Res<Exp> {
    todo!()
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
