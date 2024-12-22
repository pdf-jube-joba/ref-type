use std::io::BufRead;

use ref_type::ast::{self};

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
                    println!("Check: {e1:?}: {e2:?}")
                }
                ast::parse::Command::Infer(_) => todo!(),
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
