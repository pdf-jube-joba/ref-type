use colored::{ColoredString, Colorize};
use either::Either;
use std::io::BufRead;

use core::{
    ast::{self, inductives::IndTypeDefs, Exp, Sort},
    context::{self, printing, ResIndDefsOk},
    interpreter::{self, *},
    lambda_calculus::{self, subst},
    parse::{self, *},
};

mod command;

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

    let mut interpreter = interpreter::Interpreter::new(context::GlobalContext::default());

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

        let command = match parser.parse_command(&buf) {
            Ok(command) => command,
            Err(err) => {
                println!("{err}");
                std::process::exit(1);
            }
        };

        match command {
            Command::Parse(exp) => println!("Parse: {exp}"),
            Command::LambdaCommand(lambda_command) => {
                match &lambda_command {
                    LambdaCommand::Subst(exp, var, exp1) => {
                        println!("Subst: {exp}[{var} := {exp1}]")
                    }
                    LambdaCommand::AlphaEq(exp, exp1, b) => println!("AlphaEq: {exp} =~ {exp1}"),
                    LambdaCommand::Reduce(exp) => println!("Reduce: {exp}"),
                    LambdaCommand::TopReduce(exp) => println!("TopReduce: {exp}"),
                    LambdaCommand::Normalize(exp) => println!("Normalize: {exp}"),
                    LambdaCommand::BetaEq(exp, exp1, b) => println!("BetaEq: {exp} =~ {exp1}"),
                }
                let res = interpreter.lambda_command(lambda_command);
                match res {
                    LambdaCommandResult::Subst(exp) => {}
                    LambdaCommandResult::AlphaEq(bool) => {}
                    LambdaCommandResult::BetaEq(res) => {}
                    LambdaCommandResult::TopReduce(res) => {}
                    LambdaCommandResult::Reduce(res) => {}
                    LambdaCommandResult::Normalize(res) => {}
                }
            }
            Command::TypingCommand(typing_command, _, tree_config) => todo!(),
            Command::NewCommand(new_command, _, tree_config) => todo!(),
            // Either::Left(Command::Parse(exp)) => {
            //     println!("Parse: {exp}");
            // }
            // Either::Left(Command::Check(e1, e2, config)) => {
            //     println!("Check: ({e1}): ({e2})");
            //     let tree = gcxt.type_check(e1, e2);
            //     match tree {
            //         Ok(der_tree) => {
            //             println!("{}", succ_or_fail(true, flag));
            //             printing::print_tree(&der_tree, &config);
            //         }
            //         Err(err) => {
            //             println!("{}", succ_or_fail(false, flag));
            //             printing::print_fail_tree(&err, &config);
            //         }
            //     }
            // }
            // Either::Left(Command::Infer(e1, config)) => {
            //     println!("Infer: ({e1})");
            //     let result = gcxt.type_infer(e1);
            //     match result {
            //         Ok(tree) => {
            //             let head = tree.head.clone();
            //             println!("{}", succ_or_fail(true, flag));
            //             println!("{}", head);
            //             printing::print_tree(&tree, &config);
            //         }
            //         Err(err) => {
            //             println!("{}", succ_or_fail(false, flag));
            //             printing::print_fail_tree(&err, &config);
            //         }
            //     };
            // }
            // Either::Left(Command::Subst(e1, x, e2)) => {
            //     println!("subst: {e1}[{x} := {e2}]");
            //     let e = subst(e1, &x, &e2);
            //     println!(" => {}", e)
            // }
            // Either::Left(Command::AlphaEq(e1, e2)) => {
            //     println!("alphaeq: {e1} =~ {e2}");
            //     if lambda_calculus::alpha_eq(&e1, &e2) {
            //         println!("{}", succ_or_fail(true, flag));
            //     } else {
            //         println!("{}", succ_or_fail(false, flag));
            //     };
            // }
            // Either::Left(Command::TopReduce(term)) => {
            //     println!("top reduction: {term}");
            //     match lambda_calculus::top_reduction(&gcxt, term) {
            //         None => println!(" => x"),
            //         Some(e) => println!(" => {e}"),
            //     };
            // }
            // Either::Left(Command::Reduce(term)) => {
            //     println!("reduce: {term}");
            //     match lambda_calculus::reduce(&gcxt, term) {
            //         None => println!(" => x"),
            //         Some(e) => println!(" => {e}"),
            //     };
            // }
            // Either::Left(Command::Normalize(term)) => {
            //     println!("normalize: {term}");
            //     let a = lambda_calculus::normalize_seq(&gcxt, term);
            //     for a in a {
            //         println!(" => {a}");
            //     }
            // }
            // Either::Left(Command::BetaEq(e1, e2)) => {
            //     println!("betaeq: {e1} =~ {e2}");
            //     if lambda_calculus::beta_equiv(&gcxt, e1.clone(), e2.clone()) {
            //         println!("{}", succ_or_fail(true, flag));
            //     } else {
            //         println!("{}", succ_or_fail(false, flag));
            //     }
            // }
            // Either::Right(NewCommand::Assumption(x, a, config)) => {
            //     println!("Assum {x}: {a}");
            //     match gcxt.push_new_assum((x.clone(), a.clone())) {
            //         Ok((der_tree, sort)) => {
            //             println!("{}", succ_or_fail(true, flag));
            //             println!("sort {sort}");
            //             printing::print_tree(&der_tree, &config);
            //         }
            //         Err(err) => {
            //             println!("{}", succ_or_fail(false, flag));
            //             printing::print_fail_tree(&err, &config);
            //         }
            //     }
            // }
            // Either::Right(NewCommand::Definition(x, a, t, config)) => {
            //     println!("Def {x}: {a} := {t}");
            //     match gcxt.push_new_defs((x.clone(), a.clone(), t.clone())) {
            //         Ok(der_tree) => {
            //             println!("{}", succ_or_fail(true, flag));
            //             printing::print_tree(&der_tree, &config);
            //         }
            //         Err(err) => {
            //             println!("{}", succ_or_fail(false, flag));
            //             printing::print_fail_tree(&err, &config);
            //         }
            //     }
            // }
            // Either::Right(NewCommand::Inductive(inddefs, config)) => {
            //     println!("Inddefs \n {inddefs}");
            //     // inddefs syntax
            //     let inddefs = match check_inductive_syntax(inddefs) {
            //         Ok(inddefs) => inddefs,
            //         Err(err) => {
            //             println!("{} on inductive definition", succ_or_fail(false, flag));
            //             println!("{err}");
            //             continue;
            //         }
            //     };
            //     let arity: Exp = inddefs.arity().clone().into();

            //     match gcxt.push_new_ind(inddefs.clone()) {
            //         Err(err) => match err {
            //             context::ResIndDefsError::AlreadyDefinedType => {
            //                 println!("{} already defined", succ_or_fail(false, flag));
            //             }
            //             context::ResIndDefsError::ArityNotWellformed(tree) => {
            //                 println!(
            //                     "{} arity not well-formed: {arity}",
            //                     succ_or_fail(false, flag)
            //                 );
            //                 printing::print_fail_tree(&tree, &config);
            //             }
            //             context::ResIndDefsError::ConstructorNotWellFormed(cs) => {
            //                 println!("{} constructor well-formed", succ_or_fail(false, flag));
            //                 for c in cs {
            //                     match c {
            //                         Ok(tree) => printing::print_tree(&tree, &config),
            //                         Err(tree) => {
            //                             printing::print_fail_tree(&tree, &config);
            //                         }
            //                     }
            //                 }
            //             }
            //         },
            //         Ok(ResIndDefsOk {
            //             arity_well_formed,
            //             constructor_wellformed,
            //         }) => {
            //             println!("{} accepted", succ_or_fail(true, flag));
            //             printing::print_tree(&arity_well_formed, &config);
            //             for c in constructor_wellformed {
            //                 printing::print_tree(&c, &config);
            //             }
            //         }
            //     };
            // }
        }
    }
}
