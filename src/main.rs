use std::io::{BufRead, Read};

use ref_type::ast::{self, parse::parse_command};

fn main() {
    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();

    loop {
        let mut buf = String::new();
        stdin.read_line(&mut buf).unwrap();

        if buf.is_empty() {
            return;
        }

        match parse_command(&buf) {
            Ok(command) => match command {
                ast::parse::ResultCommand::Parse(exp) => {
                    println!("Parsed: {exp:?}");
                },
                ast::parse::ResultCommand::Check(e1, e2, r) => {
                    
                },
                ast::parse::ResultCommand::Infer(_, _) => todo!(),
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
