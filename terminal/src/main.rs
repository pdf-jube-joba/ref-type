use colored::Colorize;
use core::{
    core::checker::{Interpreter, StateInterpreter},
    syntax::parse::MyParser,
};
use std::io::BufRead;

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

    println!("===start of input===");

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
            StateInterpreter::NoGoal => {
                println!("---command---")
            }
            StateInterpreter::Goals(goal) => {
                let first = goal.first_proposition().unwrap();
                println!("---goal:{}---", first)
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
                std::process::exit(1);
            }
        }
    }

    match interpreter.now_state() {
        StateInterpreter::NoGoal => {
            println!("---command---")
        }
        StateInterpreter::Goals(goal) => {
            let first = goal.first_proposition().unwrap();
            println!("---goal:{}---", first)
        }
    }

    println!("===end of input===")
}
