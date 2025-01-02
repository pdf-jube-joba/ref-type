use either::Either;
use std::io::BufRead;

use ref_type::{
    ast::{
        self, parse,
        parse::{Command, InductiveDefinitionsSyntax, NewCommand},
    },
    relation,
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
            continue;
        }

        let parser = ast::parse::MyParser;

        let command = match parser.parse_command(&buf) {
            Ok(command) => {
                command
            },
            Err(err) => {
                println!("{err}");
                continue;
            }
        };


        match command {
            Either::Left(Command::Parse(exp)) => {
                println!("Parse: {exp:?}");
            }
            Either::Left(Command::Check(e1, e2)) => {
                println!("Check: ({}): ({})", e1.pretty_print(), e2.pretty_print());
                let tree = relation::type_check(&gcxt, relation::Context::default(), e1, e2);
                let res = match tree.result_of_tree() {
                    relation::StatePartialTree::Fail => "FAIL!".to_string(),
                    relation::StatePartialTree::Wait(vec) => format!("GOALS..{:?}", vec),
                };
                println!("result: {}\n{}", res, tree.pretty_print(0));
            }
            Either::Left(Command::Infer(e1)) => {
                println!("Infer: ({})", e1.pretty_print());
                let (tree, res) = relation::type_infer(&gcxt, relation::Context::default(), e1);
                let res_tree = match tree.result_of_tree() {
                    relation::StatePartialTree::Fail => "FAIL!".to_string(),
                    relation::StatePartialTree::Wait(vec) => format!("GOALS..{:?}", vec),
                };
                println!(
                    "type: {:?}\n result: {}\n{}",
                    res,
                    res_tree,
                    tree.pretty_print(0)
                );
            }
            Either::Left(Command::AlphaEq(e1, e2)) => {
                if relation::alpha_eq(&e1, &e2) {
                    println!("alphaeq {e1:?} {e2:?}");
                } else {
                    println!("not alphaeq {e1:?} {e2:?}");
                };
            }
            Either::Left(Command::TopReduce(term)) => {
                println!("input: {term:?}");
                let a = relation::top_reduction(&gcxt, term);
                println!("output: {a:?}");
            }
            Either::Left(Command::Reduce(term)) => {
                println!("input: {term:?}");
                let a = relation::reduce(&gcxt, term);
                println!("output: {a:?}");
            }
            Either::Left(Command::Normalize(term)) => {
                println!("input: {term:?}");
                let a = relation::normalize_seq(&gcxt, term);
                println!("output:");
                for a in a {
                    println!(" {a:?}");
                }
            }
            Either::Left(Command::BetaEq(e1, e2)) => {
                println!("betaeq: {e1:?} {e2:?}");
                let a = relation::beta_equiv(&gcxt, e1, e2);
                println!("res: {a}");
            }
            Either::Right(NewCommand::Assumption(x, a)) => todo!(),
            Either::Right(NewCommand::Definition(x, a, t)) => todo!(),
            Either::Right(NewCommand::Inductive(inddefs)) => {
                if let Err(err) = parse::add_ind(&mut gcxt, inddefs) {
                    println!("err: {err:?}");
                    continue;
                }
            }
        }
    }
}
