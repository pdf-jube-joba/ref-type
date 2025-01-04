use colored::Colorize;
use either::Either;
use std::io::BufRead;

use ref_type::{
    ast::{
        self,
        parse::{self, Command, InductiveDefinitionsSyntax, NewCommand},
        Exp,
    },
    relation::{self, subst},
};

fn main() {
    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();

    let mut gcxt = ast::GlobalContext::default();

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
                let tree = relation::type_check(&gcxt, relation::Context::default(), e1, e2);
                let res = match tree.result_of_tree() {
                    relation::StatePartialTree::Fail => "FAIL!".red(),
                    relation::StatePartialTree::Wait(vec) => format!("GOALS..{:?}", vec).blue(),
                };
                println!("{}\n{}", res, tree.pretty_print(1));
            }
            Either::Left(Command::Infer(e1)) => {
                println!("Infer: ({e1})");
                let (tree, res) = relation::type_infer(&gcxt, relation::Context::default(), e1);
                let res_tree = match tree.result_of_tree() {
                    relation::StatePartialTree::Fail => "FAIL!".red(),
                    relation::StatePartialTree::Wait(vec) => format!("GOALS..{:?}", vec).blue(),
                };
                println!(
                    "type: {:?}\n result: {}\n{}",
                    res,
                    res_tree,
                    tree.pretty_print(0)
                );
            }
            Either::Left(Command::Subst(e1, x, e2)) => {
                println!("subst: {e1}[{x} := {e2}]");
                let e = subst(e1, &x, &e2);
                println!(" => {}", e)
            }
            Either::Left(Command::AlphaEq(e1, e2)) => {
                if relation::alpha_eq(&e1, &e2) {
                    println!("alphaeq {}: {e1} =~ {e2}", "SUCCESS".blue());
                } else {
                    println!("alphaeq {}: {e1} =~ {e2}", "FAIL".red());
                };
            }
            Either::Left(Command::TopReduce(term)) => {
                println!("top reduction: {term}");
                match relation::top_reduction(&gcxt, term) {
                    None => println!(" => x"),
                    Some(e) => println!(" => {e}"),
                };
            }
            Either::Left(Command::Reduce(term)) => {
                println!("reduce: {term}");
                match relation::reduce(&gcxt, term) {
                    None => println!(" => x"),
                    Some(e) => println!(" => {e}"),
                };
            }
            Either::Left(Command::Normalize(term)) => {
                println!("normalize: {term}");
                let a = relation::normalize_seq(&gcxt, term);
                for a in a {
                    println!(" => {a}");
                }
            }
            Either::Left(Command::BetaEq(e1, e2)) => {
                if relation::beta_equiv(&gcxt, e1.clone(), e2.clone()) {
                    println!("betaeq {}: {e1} =~ {e2}", "SUCCESS".blue());
                } else {
                    println!("betaeq {}: {e1} =~ {e2}", "FAIL".red())
                }
            }
            Either::Right(NewCommand::Assumption(x, a)) => {
                let (der_tree, res) = gcxt.push_new_assum((x, a));
                match res {
                    Ok(_) => {
                        println!("{}", "new assum SUCC".blue());
                    }
                    Err(err) => {
                        println!("{} {}", "new assum FAIL".red(), err);
                    }
                }
                println!("{}", der_tree.pretty_print(0));
            }
            Either::Right(NewCommand::Definition(x, a, t)) => {
                let (der_tree, res) = gcxt.push_new_defs((x, a, t));
                match res {
                    Ok(_) => {
                        println!("{}", "new def SUCC".blue());
                    }
                    Err(err) => {
                        println!("{} {}", "new def FAIL".red(), err);
                    }
                }
                println!("{}", der_tree.pretty_print(0));
            }
            Either::Right(NewCommand::Inductive(inddefs)) => {
                println!("{inddefs:?}");
                match parse::add_ind(&mut gcxt, inddefs) {
                    Ok(inddefs) => {
                        let arity: Exp = inddefs.arity().clone().into();
                        println!("{}", format!("SUCC").blue());
                        println!("  arity: {arity}");
                        println!("  constructors:");
                        for c in inddefs.constructors() {
                            let c_exp: Exp = c.clone().into();
                            let elim_type: Exp =
                                c.eliminator_type(Exp::Var("Q".into()), Exp::Var("c".into()));
                            let recursor: Exp =
                                c.recursor(Exp::Var("F".into()), Exp::Var("f".into()));
                            println!("  {} with type:{} recursor: {}", c_exp, elim_type, recursor);
                        }
                    }
                    Err(err) => {
                        println!("{}", format!("FAIL: {}", err).red());
                    }
                }
            }
        }
    }
}
