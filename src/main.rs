use std::io::BufRead;

use ref_type::{
    ast::{self},
    relation,
};

fn main() {
    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();

    loop {
        let mut buf = String::new();
        stdin.read_line(&mut buf).unwrap();

        if buf.is_empty() {
            return;
        }

        let parser = ast::parse::MyParser;

        match parser.parse_command(&buf) {
            Ok(command) => match command {
                ast::parse::Command::Parse(exp) => {
                    println!("Parse: {exp:?}");
                }
                ast::parse::Command::Check(e1, e2) => {
                    println!("Check: ({}): ({})", e1.pretty_print(), e2.pretty_print());
                    let tree = relation::type_check(relation::Context::default(), e1, e2);
                    println!("{}", tree.pretty_print(0));
                }
                ast::parse::Command::Infer(e1) => {
                    println!("Infer: ({})", e1.pretty_print());
                    let (tree, res) = relation::type_infer(relation::Context::default(), e1);
                    println!("{}", tree.pretty_print(0));
                    println!("type: {:?}", res);
                }
            },
            Err(err) => {
                println!("{err:?}")
            }
        }
    }

    // let res = ast::parse::parse_code(&buf);
    // let exp = match res {
    //     Ok(exp) => exp,
    //     Err(err) => {
    //         println!("{err}");
    //         return;
    //     }
    // };
    // println!("parse ok \n: {exp:?}");
}
