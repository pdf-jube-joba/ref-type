use colored::{ColoredString, Colorize};
use either::Either;
use std::io::BufRead;

use ref_type::{
    ast::{
        self,
        inductives::IndTypeDefs,
        parse::{self, Command, InductiveDefinitionsSyntax, NewCommand},
        Exp, Sort,
    },
    lambda_calculus::{self, subst},
    relation::{self, printing, ResIndDefs},
};

fn main() {
    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();

    let mut gcxt = relation::GlobalContext::default();

    loop {
        let buf: String = {
            let mut buf = vec![];
            stdin.read_until(b';', &mut buf).unwrap();
            let s = String::from_utf8(buf).unwrap();
            s.trim().to_string()
        };

        if buf.is_empty() {
            break;
        }

        println!("-----");

        let parser = ast::parse::MyParser;

        let command = match parser.parse_command(&buf) {
            Ok(command) => command,
            Err(err) => {
                println!("{err}");
                break;
            }
        };

        match command {
            Either::Left(Command::Parse(exp)) => {
                println!("Parse: {exp}");
            }
            Either::Left(Command::Check(e1, e2)) => {
                println!("Check: ({e1}): ({e2})");
                let tree = relation::type_check(&gcxt, relation::LocalContext::default(), e1, e2);
                match tree {
                    Ok(der_tree) => {
                        println!("{}", "SUCC".blue());
                        print!("{}", printing::print_tree_type_check(der_tree));
                    }
                    Err(err) => {
                        println!("{}", "FAIl".red());
                        print!("{}", printing::print_fail_tree(err));
                    }
                }
            }
            Either::Left(Command::Infer(e1)) => {
                println!("Infer: ({e1})");
                match relation::type_infer(&gcxt, relation::LocalContext::default(), e1) {
                    Ok(tree) => {
                        let head = tree.head.clone();
                        println!("{} infered type ... {}", "SUCC".blue(), head);
                        println!("{}", printing::print_tree_type_check(tree));
                    }
                    Err(err) => {
                        println!("{}", "FAIl".red());
                        println!("{}", printing::print_fail_tree(err))
                    }
                };
            }
            Either::Left(Command::Subst(e1, x, e2)) => {
                println!("subst: {e1}[{x} := {e2}]");
                let e = subst(e1, &x, &e2);
                println!(" => {}", e)
            }
            Either::Left(Command::AlphaEq(e1, e2)) => {
                if lambda_calculus::alpha_eq(&e1, &e2) {
                    println!("alphaeq {}: {e1} =~ {e2}", "SUCCESS".blue());
                } else {
                    println!("alphaeq {}: {e1} =~ {e2}", "FAIL".red());
                };
            }
            Either::Left(Command::TopReduce(term)) => {
                println!("top reduction: {term}");
                match lambda_calculus::top_reduction(&gcxt, term) {
                    None => println!(" => x"),
                    Some(e) => println!(" => {e}"),
                };
            }
            Either::Left(Command::Reduce(term)) => {
                println!("reduce: {term}");
                match lambda_calculus::reduce(&gcxt, term) {
                    None => println!(" => x"),
                    Some(e) => println!(" => {e}"),
                };
            }
            Either::Left(Command::Normalize(term)) => {
                println!("normalize: {term}");
                let a = lambda_calculus::normalize_seq(&gcxt, term);
                for a in a {
                    println!(" => {a}");
                }
            }
            Either::Left(Command::BetaEq(e1, e2)) => {
                if lambda_calculus::beta_equiv(&gcxt, e1.clone(), e2.clone()) {
                    println!("betaeq {}: {e1} =~ {e2}", "SUCCESS".blue());
                } else {
                    println!("betaeq {}: {e1} =~ {e2}", "FAIL".red())
                }
            }
            Either::Right(NewCommand::Assumption(x, a)) => {
                match gcxt.push_new_assum((x.clone(), a.clone())) {
                    Ok((der_tree, sort)) => {
                        println!("{} {x}: {a} ... sort {sort}", "SUCC".blue());
                        println!("{}", printing::print_tree_type_check(der_tree));
                    }
                    Err(err) => {
                        println!("{} {x}: {a}", "FAIL".red());
                        println!("{}", printing::print_fail_tree(err));
                    }
                }
            }
            Either::Right(NewCommand::Definition(x, a, t)) => {
                match gcxt.push_new_defs((x.clone(), a.clone(), t.clone())) {
                    Ok(der_tree) => {
                        println!("{} {x}: {a} := {t}", "SUCC".blue());
                        println!("{}", printing::print_tree_type_check(der_tree));
                    }
                    Err(err) => {
                        println!("{} {x}: {a} := {t}", "FAIL".red());
                        println!("{}", printing::print_fail_tree(err));
                    }
                }
            }
            Either::Right(NewCommand::Inductive(inddefs)) => {
                println!("{inddefs:?}");
                let inddefs: Result<IndTypeDefs, _> = inddefs.try_into();
                let inddefs = match inddefs {
                    Ok(inddefs) => inddefs,
                    Err(_) => todo!(),
                };
                let res = gcxt.push_new_ind(inddefs.clone());
                let ResIndDefs {
                    single,
                    arity_well_formed,
                    constructor_well_formed,
                } = res;
                if !single {
                    println!("already defined");
                    continue;
                }
                let arity_well_formed = arity_well_formed.unwrap();
                match arity_well_formed {
                    Ok(tree) => {
                        let arity: Exp = inddefs.arity().clone().into();
                        println!("{} arity:{}", "SUCC".blue(), arity);
                        println!("{}", printing::print_tree_type_check(tree));
                    }
                    Err(err) => {
                        let arity: Exp = inddefs.arity().clone().into();
                        println!("{} arity:{}", "FAIL".red(), arity);
                        println!("{}", printing::print_fail_tree(err));
                        continue;
                    }
                }
                let constructor_well_formed = constructor_well_formed.unwrap();
                for (i, (cname, c)) in inddefs.constructors().iter().enumerate() {
                    let c_exp: Exp = c.clone().into();
                    let c_well_formed = constructor_well_formed[i].clone();
                    match c_well_formed {
                        Ok(tree) => {
                            println!("{} name:{cname} exp:{c_exp}", "SUCC".blue());
                            println!("{}", printing::print_tree_type_check(tree));
                            let elim_type: Exp =
                                c.eliminator_type(Exp::Var("Q".into()), Exp::Var("c".into()));
                            println!("  elim type:{elim_type}");
                            let recursor: Exp =
                                c.recursor(Exp::Var("F".into()), Exp::Var("f".into()));
                            println!("  elim term:{recursor}");

                            let e = gcxt
                                .induction_principal(inddefs.name(), Sort::Prop)
                                .unwrap();
                            println!("  induction principal: {e}")
                        }
                        Err(tree) => {
                            println!("{} name:{cname} exp:{c_exp}", "FAIL".red());
                            println!("{}", printing::print_fail_tree(tree));
                        }
                    }
                }
            }
        }
    }
}
