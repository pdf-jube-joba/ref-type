use crate::ast::{inductives::*, *};
use crate::relation::GlobalContext;
use either::Either;
use pest::{error, iterators::Pair, Parser};
use pest_derive::Parser;

pub use parse_command::{
    new_inductive_type_definition::{
        check_inductive_syntax, InductiveDefinitionsSyntax, ParamCstSyntax,
    },
    Command, NewCommand,
};

pub enum ParserError {
    Parse(Box<error::Error<Rule>>),
    Other(String),
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
#[grammar = "program.pest"]
pub struct MyParser;

impl MyParser {
    pub fn parse_exp(&mut self, code: &str) -> Result<Exp, ParserError> {
        let mut p = MyParser::parse(Rule::expression, code)?;
        let e = parse_exp::take_expression(p.next().unwrap())?;
        Ok(e)
    }
    pub fn parse_command(
        &mut self,
        code: &str,
    ) -> Result<Either<Command, NewCommand>, ParserError> {
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
            Rule::sort_univ => Sort::Univ,
            Rule::sort_type => Sort::Type,
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
                while p.next().is_some() {
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
            Rule::variable => Ok(Exp::Var(take_variable(p)?)),
            _ => unreachable!("take small"),
        }
    }

    pub(crate) fn take_var_annnot(pair: Pair<Rule>) -> Res<(Var, Exp)> {
        debug_assert_eq!(pair.as_rule(), Rule::var_annot);
        let mut ps = pair.into_inner();
        let v = {
            let p = ps.next().unwrap();
            take_variable(p)?
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
        }
    }
}

mod parse_command {
    use crate::parse::parse_command::new_inductive_type_definition::take_new_inductive;

    use super::parse_exp::take_expression;
    use super::*;
    type Res<E> = Result<E, Box<error::Error<Rule>>>;
    use parse_command::parse_exp::{take_var_annnot, take_variable};

    #[derive(Debug, Clone, PartialEq, Eq)]
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

    #[derive(Debug, Clone, PartialEq, Eq)]
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
                let e = take_expression(ps.next().unwrap())?;
                Ok(Either::Left(Command::Parse(e)))
            }
            Rule::command_check => {
                let mut ps = pair.into_inner();
                let e1 = take_expression(ps.next().unwrap())?;
                let e2 = take_expression(ps.next().unwrap())?;
                Ok(Either::Left(Command::Check(e1, e2)))
            }
            Rule::command_infer => {
                let mut ps = pair.into_inner();
                let e = take_expression(ps.next().unwrap())?;
                Ok(Either::Left(Command::Infer(e)))
            }
            Rule::command_subst => {
                let mut ps = pair.into_inner();
                let e1 = take_expression(ps.next().unwrap())?;
                let x = take_variable(ps.next().unwrap())?;
                let e2 = take_expression(ps.next().unwrap())?;
                Ok(Either::Left(Command::Subst(e1, x, e2)))
            }
            Rule::command_alpha_eq => {
                let mut ps = pair.into_inner();
                let e1 = take_expression(ps.next().unwrap())?;
                let e2 = take_expression(ps.next().unwrap())?;
                Ok(Either::Left(Command::AlphaEq(e1, e2)))
            }
            Rule::command_top_reduction => {
                let mut ps = pair.into_inner();
                let e = take_expression(ps.next().unwrap())?;
                Ok(Either::Left(Command::TopReduce(e)))
            }
            Rule::command_normalize => {
                let mut ps = pair.into_inner();
                let e = take_expression(ps.next().unwrap())?;
                Ok(Either::Left(Command::Normalize(e)))
            }
            Rule::command_beta_equiv => {
                let mut ps = pair.into_inner();
                let e1 = take_expression(ps.next().unwrap())?;
                let e2 = take_expression(ps.next().unwrap())?;
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

    pub(crate) fn take_new_assumption(pair: Pair<Rule>) -> Res<(Var, Exp)> {
        debug_assert_eq!(pair.as_rule(), Rule::new_assumption);
        let mut ps = pair.into_inner();
        let variable = {
            let p = ps.next().unwrap();
            take_variable(p)?
        };
        let expression = {
            let p = ps.next().unwrap();
            take_expression(p)?
        };
        Ok((variable, expression))
    }

    pub(crate) fn take_new_definition(pair: Pair<Rule>) -> Res<(Var, Exp, Exp)> {
        debug_assert_eq!(pair.as_rule(), Rule::new_definition);
        let mut ps = pair.into_inner();
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
        Ok((variable, expression1, expression2))
    }

    pub mod new_inductive_type_definition {
        use parse_command::parse_exp::{take_name, take_sort};

        use super::*;

        #[derive(Debug, Clone, PartialEq, Eq)]
        pub struct InductiveDefinitionsSyntax {
            type_name: String,
            arity: (Vec<(Var, Exp)>, Sort),
            constructors: Vec<(String, Vec<ParamCstSyntax>, Vec<Exp>)>,
        }

        #[derive(Debug, Clone, PartialEq, Eq)]
        pub enum ParamCstSyntax {
            Positive((Vec<(Var, Exp)>, Vec<Exp>)),
            Simple((Var, Exp)),
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
            debug_assert!(matches!(pair.as_rule(), Rule::var_annot | Rule::expression));
            match pair.as_rule() {
                Rule::var_annot => take_var_annnot(pair),
                Rule::expression => {
                    let e = take_expression(pair)?;
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
                    Rule::var_annot | Rule::expression => {
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

        pub(crate) fn take_new_inductive(pair: Pair<Rule>) -> Res<InductiveDefinitionsSyntax> {
            debug_assert_eq!(pair.as_rule(), Rule::new_inductive);
            let mut ps = pair.into_inner();
            let type_name = take_name(ps.next().unwrap())?;
            let arity = take_arity(ps.next().unwrap())?;
            let constructors: Vec<_> = ps
                .map(|p| take_constructor_definition(p))
                .collect::<Result<_, _>>()?;
            Ok(InductiveDefinitionsSyntax {
                type_name,
                arity,
                constructors,
            })
        }

        pub fn check_inductive_syntax(
            InductiveDefinitionsSyntax {
                type_name,
                arity: (signature, sort),
                constructors,
            }: InductiveDefinitionsSyntax,
        ) -> Result<IndTypeDefs, String> {
            let type_name_variable: Var = type_name.as_str().into();

            let mut cs_name_type = vec![];

            for (cs_name, params, end) in constructors {
                let mut new_params = vec![];

                for param in params {
                    let param = match param {
                        ParamCstSyntax::Positive((parameter, mut exps)) => {
                            if exps[0] != type_name_variable.clone().into() {
                                return Err(format!("{exps:?} "));
                            }
                            exps.remove(0);
                            let positive =
                                Positive::new(type_name_variable.clone(), parameter, exps)?;
                            ParamCst::Positive(positive)
                        }
                        ParamCstSyntax::Simple(simple) => ParamCst::Simple(simple),
                    };
                    new_params.push(param)
                }

                let cstype = ConstructorType::new_constructor(
                    (type_name_variable.clone(), end),
                    new_params,
                )?
                .0;

                cs_name_type.push((cs_name, cstype));
            }

            IndTypeDefs::new(
                type_name,
                type_name_variable,
                (signature, sort),
                cs_name_type,
            )
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
