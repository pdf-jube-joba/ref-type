use crate::ast::{inductives::*, *};
use crate::relation::GlobalContext;
use either::Either;
use pest::{error, iterators::Pair, Parser};
use pest_derive::Parser;

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
    pub fn parse_exp(&self, code: &str) -> Result<Exp, error::Error<Rule>> {
        let mut r = MyParser::parse(Rule::expression, code)?;
        Ok(take_exp(r.next().unwrap()).unwrap())
    }
    pub fn parse_ind(&self, code: &str) -> Result<InductiveDefinitionsSyntax, error::Error<Rule>> {
        let mut r = MyParser::parse(Rule::expression, code)?;
        Ok(take_new_inductive(r.next().unwrap()).unwrap())
    }
}

impl TryFrom<InductiveDefinitionsSyntax> for IndTypeDefs {
    type Error = String;
    fn try_from(value: InductiveDefinitionsSyntax) -> Result<Self, Self::Error> {
        let InductiveDefinitionsSyntax {
            type_name,
            arity: AritySyntax { signature, sort },
            constructors,
        } = value;

        let variable: Var = type_name.as_str().into();

        let mut cs_name_type = vec![];

        for (n, t) in constructors {
            let ConstructorSyntax { end, params } = t;

            let mut new_params = vec![];

            for param in params {
                let param = match param {
                    ParamCstSyntax::Positive(positive_syntax) => {
                        let PositiveSyntax { parameter, exps } = positive_syntax;
                        let positive = Positive::new(variable.clone(), parameter, exps)?;
                        ParamCst::Positive(positive)
                    }
                    ParamCstSyntax::Simple(simple) => ParamCst::Simple(simple),
                };
                new_params.push(param)
            }

            let cstype = ConstructorType::new_constructor((variable.clone(), end), new_params)?.0;

            cs_name_type.push((n, cstype));
        }

        IndTypeDefs::new(type_name, variable, (signature, sort), cs_name_type)
    }
}

pub enum Command {
    Parse(Exp),
    Check(Exp, Exp),
    Infer(Exp),
    Subst(Exp, Var, Exp),
    AlphaEq(Exp, Exp),
    TopReduce(Exp),
    Reduce(Exp),
    Normalize(Exp),
    BetaEq(Exp, Exp),
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
        Rule::command_subst => {
            let mut ps = pair.into_inner();
            let e1 = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            let x = {
                let p = ps.next().unwrap();
                take_identifier(p)?
            };
            let e2 = {
                let p = ps.next().unwrap();
                take_exp(p)?
            };
            Ok(Either::Left(Command::Subst(e1, x, e2)))
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
            Ok(utils::assoc_apply(e1, e2))
        }
        Rule::variable => {
            let x = take_identifier(p).unwrap();
            Ok(Exp::Var(x))
        }
        Rule::inductive_type => {
            let n = take_inductive_type(p)?;
            Ok(Exp::IndTypeType {
                ind_type_name: n.into(),
            })
        }
        Rule::inductive_constructor => {
            let (n, c) = take_inductive_constructor(p)?;
            Ok(Exp::IndTypeCst {
                ind_type_name: n.into(),
                constructor_name: c.into(),
            })
        }
        Rule::inductive_eliminator => {
            let (n, c, q, cases) = take_inductive_eliminator(p)?;
            Ok(Exp::IndTypeElim {
                ind_type_name: n.into(),
                eliminated_exp: Box::new(c),
                return_type: Box::new(q),
                cases,
            })
        }
        Rule::expression_readable => {
            let ps = p.into_inner();
            let p = ps.peek().unwrap();
            take_exp(p)
        }
        _ => {
            panic!("{}", p.as_str())
        }
    }
}

pub(crate) fn take_sort(pair: Pair<Rule>) -> Res<Sort> {
    debug_assert_eq!(pair.as_rule(), Rule::sort);
    let ps = pair.into_inner();
    let p = ps.peek().unwrap();
    let sort = match p.as_rule() {
        Rule::sort_set => Sort::Set,
        Rule::sort_prop => Sort::Prop,
        Rule::sort_univ => Sort::Univ,
        Rule::sort_type => Sort::Type,
        _ => unreachable!("sort の中に変なのがある"),
    };
    Ok(sort)
}

pub(crate) fn take_identifier(pair: Pair<Rule>) -> Res<Var> {
    match pair.as_rule() {
        Rule::variable => Ok(pair.as_str().into()),
        Rule::unused_variable => Ok(Var::Unused),
        _ => unreachable!("identifier expected"),
    }
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

pub(crate) fn take_dependent_prod_elim(pair: Pair<Rule>) -> Res<(Exp, Vec<Exp>)> {
    debug_assert_eq!(pair.as_rule(), Rule::dependent_prod_elim);
    let mut ps = pair.into_inner();
    let e1 = {
        let p = ps.next().unwrap();
        take_exp(p)?
    };
    let v = ps.map(|p| take_exp(p)).collect::<Result<_, _>>()?;
    // let e2 = {
    //     let p = ps.next().unwrap();
    //     take_exp(p)?
    // };
    Ok((e1, v))
}

pub(crate) fn take_inductive_type(pair: Pair<Rule>) -> Res<String> {
    debug_assert_eq!(pair.as_rule(), Rule::inductive_type);
    let mut ps = pair.into_inner();
    let n = {
        let p = ps.next().unwrap();
        take_type_name(p)?
    };
    Ok(n)
}

pub(crate) fn take_inductive_constructor(pair: Pair<Rule>) -> Res<(String, String)> {
    debug_assert_eq!(pair.as_rule(), Rule::inductive_constructor);
    let mut ps = pair.into_inner();
    let n = {
        let p = ps.next().unwrap();
        take_type_name(p)?
    };
    let c = {
        let p = ps.next().unwrap();
        take_constructor_name(p)?
    };
    Ok((n, c))
}

pub(crate) fn take_inductive_eliminator(
    pair: Pair<Rule>,
) -> Res<(TypeName, Exp, Exp, Vec<(ConstructorName, Exp)>)> {
    debug_assert_eq!(pair.as_rule(), Rule::inductive_eliminator);
    let mut ps = pair.into_inner();
    let n = {
        let p = ps.next().unwrap();
        take_type_name(p)?
    };
    let c = {
        let p = ps.next().unwrap();
        take_exp(p)?
    };
    let q = {
        let p = ps.next().unwrap();
        take_exp(p)?
    };
    let cases = {
        let mut cases = vec![];
        while ps.peek().is_some() {
            let n = take_constructor_name(ps.next().unwrap())?;
            let e = take_exp(ps.next().unwrap())?;
            cases.push((n.into(), e));
        }
        cases
    };
    Ok((n.into(), c, q, cases))
}

#[derive(Debug, Clone, PartialEq)]
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

pub(crate) fn take_terminate(pair: Pair<Rule>, type_name: &str) -> Res<Vec<Exp>> {
    debug_assert_eq!(pair.as_rule(), Rule::constructor_terminate);
    let mut ps = pair.into_inner();
    let v = {
        let p = ps.next().unwrap();
        take_type_name(p)?
    };
    if v.as_str() != type_name {
        panic!("")
    }
    let mut argument = vec![];
    for p in ps {
        let e = take_exp(p)?;
        argument.push(e)
    }
    Ok(argument)
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct PositiveSyntax {
    parameter: Vec<(Var, Exp)>,
    exps: Vec<Exp>,
}

pub(crate) fn take_positive(pair: Pair<Rule>, type_name: &str) -> Res<PositiveSyntax> {
    debug_assert_eq!(pair.as_rule(), Rule::positive);
    let mut ps = pair.into_inner();
    let mut parameter = vec![];
    loop {
        let p = ps.next().unwrap();
        if p.as_rule() == Rule::var_annot {
            let exp = take_var_annnot(p)?;
            parameter.push(exp);
        } else {
            let exps = take_terminate(p, type_name)?;
            return Ok(PositiveSyntax { parameter, exps });
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ConstructorSyntax {
    end: Vec<Exp>,
    params: Vec<ParamCstSyntax>,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ParamCstSyntax {
    Positive(PositiveSyntax),
    Simple((Var, Exp)),
}

pub(crate) fn take_constructor_rec(pair: Pair<Rule>, type_name: &str) -> Res<ConstructorSyntax> {
    debug_assert_eq!(pair.as_rule(), Rule::constructor_rec);
    let mut ps = pair.into_inner();
    let p = ps.next().unwrap();
    match p.as_rule() {
        Rule::constructor_terminate => {
            let end = take_terminate(p, type_name)?;
            Ok(ConstructorSyntax {
                end,
                params: vec![],
            })
        }
        Rule::constructor_non_occur => {
            let mut ps = p.into_inner();
            let (v, a) = take_var_annnot(ps.next().unwrap())?;
            let ConstructorSyntax { end, mut params } =
                take_constructor_rec(ps.next().unwrap(), type_name)?;
            params.reverse();
            params.push(ParamCstSyntax::Simple((v, a)));
            params.reverse();
            Ok(ConstructorSyntax { end, params })
        }
        Rule::constructor_positive_occur => {
            let mut ps = p.into_inner();
            let positive = take_positive(ps.next().unwrap(), type_name)?;
            let ConstructorSyntax { end, mut params } =
                take_constructor_rec(ps.next().unwrap(), type_name)?;
            params.reverse();
            params.push(ParamCstSyntax::Positive(positive));
            params.reverse();
            Ok(ConstructorSyntax { end, params })
        }
        _ => unreachable!("constructor_rec 中"),
    }
}

pub(crate) fn take_constructor_definition(
    pair: Pair<Rule>,
    type_name: &str,
) -> Res<(String, ConstructorSyntax)> {
    debug_assert_eq!(pair.as_rule(), Rule::constructor_definition);
    let mut ps = pair.into_inner();
    let constructor_name = {
        let p = ps.next().unwrap();
        take_constructor_name(p)?
    };
    let constructor_type = {
        let p = ps.next().unwrap();
        take_constructor_rec(p, type_name)?
    };
    Ok((constructor_name, constructor_type))
}

pub(crate) fn take_type_name(pair: Pair<Rule>) -> Res<String> {
    debug_assert_eq!(pair.as_rule(), Rule::type_name);
    Ok(pair.as_str().to_string())
}

pub(crate) fn take_constructor_name(pair: Pair<Rule>) -> Res<String> {
    debug_assert_eq!(pair.as_rule(), Rule::constructor_name);
    Ok(pair.as_str().to_string())
}

#[derive(Debug, Clone, PartialEq)]
pub struct InductiveDefinitionsSyntax {
    type_name: String,
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
    let arity = {
        let p = ps.next().unwrap();
        take_arity(p)?
    };
    let mut constructors = vec![];
    for p in ps {
        let (constructor_name, construcor_syntax) =
            take_constructor_definition(p, type_name.as_str())?;
        constructors.push((constructor_name, construcor_syntax));
    }
    let defs = InductiveDefinitionsSyntax {
        type_name,
        arity,
        constructors,
    };
    Ok(defs)
}

pub(crate) fn take_new_assumption(pair: Pair<Rule>) -> Res<(Var, Exp)> {
    debug_assert_eq!(pair.as_rule(), Rule::new_assumption);
    let mut ps = pair.into_inner();
    let variable = {
        let p = ps.next().unwrap();
        take_identifier(p)?
    };
    let expression = {
        let p = ps.next().unwrap();
        take_exp(p)?
    };
    Ok((variable, expression))
}

pub(crate) fn take_new_definition(pair: Pair<Rule>) -> Res<(Var, Exp, Exp)> {
    debug_assert_eq!(pair.as_rule(), Rule::new_definition);
    let mut ps = pair.into_inner();
    let variable = {
        let p = ps.next().unwrap();
        take_identifier(p)?
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
        let e = take_exp(p)?;
        utils::assoc_prod(var_annots.clone(), e)
    };
    let expression2 = {
        let p = ps.next().unwrap();
        let e = take_exp(p)?;
        utils::assoc_lam(var_annots, e)
    };
    Ok((variable, expression1, expression2))
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     #[test]
//     fn parse_test() {
//         let var = "xyz";
//         let ps = MyParser::parse(Rule::variable, var).unwrap();
//         let p = ps.peek().unwrap();
//         let v = parse::take_identifier(p).unwrap();
//         assert_eq!(v, Var::from(var.to_string()));
//     }
//     fn take_parse(pair: Pair<Rule>) -> Exp {
//         debug_assert_eq!(pair.as_rule(), Rule::command);
//         let mut ps = pair.into_inner();
//         let pair = ps.next().unwrap();
//         debug_assert_eq!(pair.as_rule(), Rule::command_parse);
//         let mut ps = pair.into_inner();
//         let p = ps.next().unwrap();
//         take_exp(p).unwrap()
//     }
//     #[test]
//     fn i() {
//         let code = "(Nat)";
//         if let Err(err) = MyParser::parse(Rule::expression, code) {
//             panic!("{}", err);
//         };

//         let code = "Nat::Succ";
//         if let Err(err) = MyParser::parse(Rule::expression, code) {
//             panic!("{}", err);
//         };

//         if let Err(err) = MyParser::parse(Rule::inductive_constructor, code) {
//             panic!("{}", err);
//         };

//         // let code = "(Nat#Succ)";
//         // if let Err(err) = MyParser::parse(Rule::expression, code) {
//         //     panic!("{}", err);
//         // };

//         // let code = "Parse (Nat);";
//         // if let Err(err) = MyParser::parse(Rule::command, code) {
//         // };

//         // let code = "Parse (Nat::Succ);";
//         // if let Err(err) = MyParser::parse(Rule::command, code) {
//         //     panic!("{}", err);
//         // };
//     }
// }
