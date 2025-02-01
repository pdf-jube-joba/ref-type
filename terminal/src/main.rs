use colored::{ColoredString, Colorize};
use either::Either;
use std::io::BufRead;

use core::{
    ast::{self, inductives::IndTypeDefs, Exp, Sort},
    lambda_calculus::{self, subst},
    parse::{self, *},
    relation::{self, printing, ResIndDefsOk},
};

fn succ_or_fail(succ_or_fail: bool, flag: bool) -> ColoredString {
    match (succ_or_fail, flag) {
        (true, true) => "SUCC".blue(),
        (true, false) => "SUCC".red(),
        (false, true) => "FAIL".red(),
        (false, false) => "FAIL".blue(),
    }
}

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

        let mut parser = parse::MyParser;

        let (command, flag) = match parser.parse_command(&buf) {
            Ok((command, flag)) => (command, flag),
            Err(err) => {
                println!("{err}");
                std::process::exit(1);
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
                        println!("{}", succ_or_fail(true, flag));
                        printing::print_tree(&der_tree);
                    }
                    Err(err) => {
                        println!("{}", succ_or_fail(false, flag));
                        printing::print_fail_tree(&err);
                    }
                }
            }
            Either::Left(Command::Infer(e1)) => {
                println!("Infer: ({e1})");
                match relation::type_infer(&gcxt, relation::LocalContext::default(), e1) {
                    Ok(tree) => {
                        let head = tree.head.clone();
                        println!("{}", succ_or_fail(true, flag));
                        println!("{}", head);
                        printing::print_tree(&tree);
                    }
                    Err(err) => {
                        println!("{}", succ_or_fail(false, flag));
                        printing::print_fail_tree(&err)
                    }
                };
            }
            Either::Left(Command::Subst(e1, x, e2)) => {
                println!("subst: {e1}[{x} := {e2}]");
                let e = subst(e1, &x, &e2);
                println!(" => {}", e)
            }
            Either::Left(Command::AlphaEq(e1, e2)) => {
                println!("alphaeq: {e1} =~ {e2}");
                if lambda_calculus::alpha_eq(&e1, &e2) {
                    println!("{}", succ_or_fail(true, flag));
                } else {
                    println!("{}", succ_or_fail(false, flag));
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
                println!("betaeq: {e1} =~ {e2}");
                if lambda_calculus::beta_equiv(&gcxt, e1.clone(), e2.clone()) {
                    println!("{}", succ_or_fail(true, flag));
                } else {
                    println!("{}", succ_or_fail(false, flag));
                }
            }
            Either::Right(NewCommand::Assumption(x, a)) => {
                println!("Assum {x}: {a}");
                match gcxt.push_new_assum((x.clone(), a.clone())) {
                    Ok((der_tree, sort)) => {
                        println!("{}", succ_or_fail(true, flag));
                        println!("sort {sort}");
                        printing::print_tree(&der_tree);
                    }
                    Err(err) => {
                        println!("{}", succ_or_fail(false, flag));
                        printing::print_fail_tree(&err);
                    }
                }
            }
            Either::Right(NewCommand::Definition(x, a, t)) => {
                println!("Def {x}: {a} := {t}");
                match gcxt.push_new_defs((x.clone(), a.clone(), t.clone())) {
                    Ok(der_tree) => {
                        println!("{}", succ_or_fail(true, flag));
                        printing::print_tree(&der_tree);
                    }
                    Err(err) => {
                        println!("{}", succ_or_fail(false, flag));
                        printing::print_fail_tree(&err);
                    }
                }
            }
            Either::Right(NewCommand::Inductive(inddefs)) => {
                println!("Inddefs \n {inddefs}");
                // inddefs syntax
                let inddefs = match check_inductive_syntax(inddefs) {
                    Ok(inddefs) => inddefs,
                    Err(err) => {
                        println!("{} on inductive definition", succ_or_fail(false, flag));
                        println!("{err}");
                        continue;
                    }
                };
                let arity: Exp = inddefs.arity().clone().into();

                match gcxt.push_new_ind(inddefs.clone()) {
                    Err(err) => match err {
                        relation::ResIndDefsError::AlreadyDefinedType => {
                            println!("{} already defined", succ_or_fail(false, flag));
                        }
                        relation::ResIndDefsError::ArityNotWellformed(tree) => {
                            println!(
                                "{} arity not well-formed: {arity}",
                                succ_or_fail(false, flag)
                            );
                            printing::print_fail_tree(&tree);
                        }
                        relation::ResIndDefsError::ConstructorNotWellFormed(cs) => {
                            println!("{} constructor well-formed", succ_or_fail(false, flag));
                            for c in cs {
                                match c {
                                    Ok(tree) => printing::print_tree(&tree),
                                    Err(tree) => {
                                        printing::print_fail_tree(&tree);
                                    }
                                }
                            }
                        }
                    },
                    Ok(ResIndDefsOk {
                        arity_well_formed,
                        constructor_wellformed,
                    }) => {
                        println!("{} accepted", succ_or_fail(true, flag));
                        printing::print_tree(&arity_well_formed);
                        for c in constructor_wellformed {
                            printing::print_tree(&c);
                        }
                    }
                };
            }
        }
    }
}
