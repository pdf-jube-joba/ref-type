use colored::Colorize;
use core::{environment::interpreter::Interpreter, parse::MyParser};
use std::io::BufRead;

mod command;

pub fn indent(str: String) -> String {
    str.lines()
        .map(|line| format!("> {}", line))
        .collect::<Vec<String>>()
        .join("\n")
}

fn main() {
    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();

    let mut interpreter = Interpreter::new();

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

        match interpreter.now_state() {
            core::environment::interpreter::StateInterpreter::NoGoal => {
                println!("---command---")
            }
            core::environment::interpreter::StateInterpreter::Goals(_) => {
                println!("---goals---")
            }
        }

        let mut parser = MyParser;

        let command = match parser.parse_command(&buf) {
            Ok(command) => command,
            Err(err) => {
                println!("{err}");
                std::process::exit(1);
            }
        };

        println!("{command}");

        let res = interpreter.command(command);
        match res {
            Ok(ok) => {
                println!("{}", "SUCC".blue());
                println!("{}", indent(ok.to_string()));
            }
            Err(err) => {
                println!("{}", "FAIL".red());
                println!("{}", indent(err.to_string()));
            }
        }
    }
}
