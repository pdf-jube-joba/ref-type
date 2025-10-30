use lalrpop_util::lalrpop_mod;

use crate::syntax;

lalrpop_mod!(program);

pub fn parse_exp(input: &str) -> Result<syntax::SExp, String> {
    match program::SExpAllParser::new().parse(input) {
        Ok(exp) => Ok(exp),
        Err(err) => Err(format!("Parse error: {}", err)),
    }
}

pub fn parse_modules(input: &str) -> Result<Vec<syntax::Module>, String> {
    match program::ModuleRepsParser::new().parse(input) {
        Ok(module) => Ok(module),
        Err(err) => Err(format!("Parse error: {}", err)),
    }
}

#[test]
fn parse_exp_test() {
    fn print_and_unwrap(input: &'static str) {
        match parse_exp(input) {
            Ok(exp) => {
                println!("Parsed expression: {:?}", exp);
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
    print_and_unwrap(r"(x: X) -> (y: Y) -> z");
    print_and_unwrap(r"(x: X | P) -> (y: Y) -> z");
}
