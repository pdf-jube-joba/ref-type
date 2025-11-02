use std::fmt::Display;

use kernel::exp::Sort;
use lalrpop_util::lalrpop_mod;

use crate::{
    syntax::{self, Identifier, MacroToken},
    utils,
};

lalrpop_mod!(program);

pub fn str_parse_exp(input: &str) -> Result<syntax::SExp, String> {
    todo!()
}

pub fn str_parse_modules(input: &str) -> Result<Vec<syntax::Module>, String> {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn atomlike_test() {
        fn print_and_unwrap(input: &'static str) {
            let toks = str_parse_exp(input);
            match (&toks) {
                Ok(atomlike) => {
                    println!("Parsed SExp: {:?} => {:?}", input, atomlike);
                }
                Err(err) => {
                    panic!("Error: {}", err);
                }
            }
        }
        print_and_unwrap(r"x");
        print_and_unwrap(r"x y");
        print_and_unwrap(r"x | y");
        print_and_unwrap(r"x (y z)");
        print_and_unwrap(r"(x y) z");
        print_and_unwrap(r"X -> Y");
        print_and_unwrap(r"(x: X) -> Y");
        print_and_unwrap(r"(x: X) => y");
        print_and_unwrap(r"(x: X) -> Y => z");
        print_and_unwrap(r"(x: X) => y h -> z");
    }
}
