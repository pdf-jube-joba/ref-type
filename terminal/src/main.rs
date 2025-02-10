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

        println!("{command}");

        let res = interpreter.command(command);

        println!("{res}");

    }
}
