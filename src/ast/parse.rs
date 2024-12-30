use either::Either;
use pest::{error, iterators::Pair, Parser};
use pest_derive::Parser;

use super::{inductives::*, *};

#[derive(Default, Parser)]
#[grammar = "ast.pest"] // relative to src
pub struct MyParser;

type Res<E> = Result<E, error::Error<Rule>>;

impl MyParser {
    pub fn parse_command(
        &self,
        code: &str,
    ) -> Result<either::Either<Command, NewCommand>, error::Error<Rule>> {
        let mut r = MyParser::parse(Rule::command, code)?;
        take_command(r.next().unwrap())
    }
}

pub fn add_ind(gcxt: &mut GlobalContext, ind: InductiveDefinitionsSyntax) -> Result<(), String> {
    let InductiveDefinitionsSyntax {
        type_name,
        variable,
        arity: AritySyntax { signature, sort },
        constructors,
    } = ind;

    let mut csnames = vec![];
    let mut cstypes = vec![];

    for (n, t) in constructors {
        let (cstype, v) = t.into_constructor_type()?;
        if v != variable {
            return Err(format!("name {n} is not of type {variable:?} but {v:?}"));
        }
        csnames.push(n);
        cstypes.push(cstype)
    }

    let defs = IndTypeDefs::new(variable, (signature, sort), cstypes)?;
    gcxt.push_newind(type_name, csnames, defs)
}

pub enum Command {
    Parse(Exp),
    Check(Exp, Exp),
    Infer(Exp),
    AlphaEq(Exp, Exp),
    TopReduce(Exp),
    Reduce(Exp),
    Normalize(Exp),
    BetaEq(Exp, Exp)
}

pub enum NewCommand {
    Definition(Var, Exp, Exp),
    Assumption(Var, Exp),
    Inductive(InductiveDefinitionsSyntax),
}

pub(crate) fn take_command(pair: Pair<Rule>) -> Res<Either<Command, NewCommand>> {
    debug_assert_eq!(pair.as_rule(), Rule::command);
    let pair = pair.into_inner().peek().unwrap();
    match pair.as_rule() {
        Rule::command_parse => {
            let mut ps = pair.into_inner();
            let e = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            Ok(Either::Left(Command::Parse(e)))
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
            Ok(Either::Left(Command::Check(e1, e2)))
        }
        Rule::command_infer => {
            let mut ps = pair.into_inner();
            let e = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            Ok(Either::Left(Command::Infer(e)))
        }
        Rule::command_alpha_eq => {
            let mut ps = pair.into_inner();
            let e1 = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            let e2 = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            Ok(Either::Left(Command::AlphaEq(e1, e2)))
        }
        Rule::command_top_reduction => {
            let mut ps = pair.into_inner();
            let e = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            Ok(Either::Left(Command::TopReduce(e)))
        }
        Rule::command_normalize => {
            let mut ps = pair.into_inner();
            let e = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            Ok(Either::Left(Command::Normalize(e)))
        }
        Rule::command_beta_equiv => {
            let mut ps = pair.into_inner();
            let e1 = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            let e2 = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            Ok(Either::Left(Command::BetaEq(e1, e2)))
        }
        Rule::new_definition => {
            let a = take_new_definition(pair)?;
            Ok(Either::Right(NewCommand::Definition(a.0, a.1, a.2)))
        }
        Rule::new_assumption => {
            let a = take_new_assumption(pair)?;
            Ok(Either::Right(NewCommand::Assumption(a.0, a.1)))
        }
        Rule::new_inductive => {
            let a = take_new_inductive(pair)?;
            Ok(Either::Right(NewCommand::Inductive(a)))
        }
        _ => todo!("command not defined"),
    }
}

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

pub(crate) struct AritySyntax {
    signature: Vec<(Var, Exp)>,
    sort: Sort,
}

impl AritySyntax {
    fn to_arity(self) -> Result<Arity, String> {
        Arity::new(self.signature, self.sort)
    }
}

pub(crate) fn take_arity(pair: Pair<Rule>) -> Res<AritySyntax> {
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
            return Ok(AritySyntax { signature, sort });
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

pub(crate) struct PositiveSyntax {
    parameter: Vec<(Var, Exp)>,
    variable: Var,
    exps: Vec<Exp>,
}

impl PositiveSyntax {
    fn into_pos(self) -> Result<Positive, String> {
        Positive::new(self.variable, self.parameter, self.exps)
    }
}

pub(crate) fn take_positive(pair: Pair<Rule>) -> Res<PositiveSyntax> {
    debug_assert_eq!(pair.as_rule(), Rule::positive);
    let mut ps = pair.into_inner();
    let mut parameter = vec![];
    loop {
        let p = ps.next().unwrap();
        if p.as_rule() == Rule::var_annot {
            let exp = take_var_annnot(p)?;
            parameter.push(exp);
        } else {
            let (variable, exps) = take_terminate(p)?;
            return Ok(PositiveSyntax {
                parameter,
                variable,
                exps,
            });
        }
    }
}

pub(crate) struct ConstructorSyntax {
    end: (Var, Vec<Exp>),
    params: Vec<ParamCstSyntax>,
}

impl ConstructorSyntax {
    fn into_constructor_type(self) -> Result<(ConstructorType, Var), String> {
        let ConstructorSyntax { end, params } = self;
        let params: Vec<ParamCst> = params
            .into_iter()
            .map(|s| s.into_paramcst())
            .collect::<Result<_, _>>()?;
        ConstructorType::new_constructor(end, params)
    }
}

pub(crate) enum ParamCstSyntax {
    Positive(PositiveSyntax),
    Simple((Var, Exp)),
}

impl ParamCstSyntax {
    fn into_paramcst(self) -> Result<ParamCst, String> {
        match self {
            ParamCstSyntax::Positive(positive_syntax) => {
                Ok(ParamCst::Positive(positive_syntax.into_pos()?))
            }
            ParamCstSyntax::Simple(s) => Ok(ParamCst::Simple(s)),
        }
    }
}

pub(crate) fn take_constructor_rec(pair: Pair<Rule>) -> Res<ConstructorSyntax> {
    debug_assert_eq!(pair.as_rule(), Rule::constructor_rec);
    let mut ps = pair.into_inner();
    let p = ps.next().unwrap();
    match p.as_rule() {
        Rule::constructor_terminate => {
            let terminate = take_terminate(p)?;
            Ok(ConstructorSyntax {
                end: (terminate.0, terminate.1),
                params: vec![],
            })
        }
        Rule::constructor_non_occur => {
            let mut ps = p.into_inner();
            let (v, a) = take_var_annnot(ps.next().unwrap())?;
            let ConstructorSyntax { end, mut params } = take_constructor_rec(ps.next().unwrap())?;
            params.push(ParamCstSyntax::Simple((v, a)));
            Ok(ConstructorSyntax { end, params })
        }
        Rule::constructor_positive_occur => {
            let mut ps = p.into_inner();
            let positive = take_positive(ps.next().unwrap())?;
            let ConstructorSyntax { end, mut params } = take_constructor_rec(ps.next().unwrap())?;
            params.push(ParamCstSyntax::Positive(positive));
            Ok(ConstructorSyntax { end, params })
        }
        _ => unreachable!("constructor_rec 中"),
    }
}

pub(crate) fn take_constructor_definition(pair: Pair<Rule>) -> Res<(String, ConstructorSyntax)> {
    debug_assert_eq!(pair.as_rule(), Rule::constructor_definition);
    let mut ps = pair.into_inner();
    let constructor_name = {
        let p = ps.next().unwrap();
        take_constructor_name(p)?
    };
    let constructor_type = {
        let p = ps.next().unwrap();
        take_constructor_rec(p)?
    };
    Ok((constructor_name, constructor_type))
}

pub(crate) fn take_type_name(pair: Pair<Rule>) -> Res<String> {
    debug_assert_eq!(pair.as_rule(), Rule::type_name);
    let mut ps = pair.into_inner();
    let p = ps.next().unwrap();
    let name = p.as_str();
    Ok(name.to_string())
}

pub(crate) fn take_constructor_name(pair: Pair<Rule>) -> Res<String> {
    debug_assert_eq!(pair.as_rule(), Rule::constructor_name);
    let mut ps = pair.into_inner();
    let p = ps.next().unwrap();
    let name = p.as_str();
    Ok(name.to_string())
}

pub struct InductiveDefinitionsSyntax {
    type_name: String,
    variable: Var,
    arity: AritySyntax,
    constructors: Vec<(String, ConstructorSyntax)>,
}

pub(crate) fn take_new_inductive(pair: Pair<Rule>) -> Res<InductiveDefinitionsSyntax> {
    debug_assert_eq!(pair.as_rule(), Rule::new_inductive);
    let mut ps = pair.into_inner();
    let type_name = {
        let p = ps.next().unwrap();
        take_type_name(p)?
    };
    let variable = {
        let p = ps.next().unwrap();
        take_identifier(p)?
    };
    let arity = {
        let p = ps.next().unwrap();
        take_arity(p)?
    };
    let mut constructors = vec![];
    for p in ps {
        let (constructor_name, construcor_syntax) = take_constructor_definition(p)?;
        constructors.push((constructor_name, construcor_syntax));
    }
    let defs = InductiveDefinitionsSyntax {
        type_name,
        variable,
        arity,
        constructors,
    };
    Ok(defs)
}

pub(crate) fn take_new_assumption(pair: Pair<Rule>) -> Res<(Var, Exp)> {
    todo!()
}

pub(crate) fn take_new_definition(pair: Pair<Rule>) -> Res<(Var, Exp, Exp)> {
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
