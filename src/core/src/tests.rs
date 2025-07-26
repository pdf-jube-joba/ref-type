// use relation::alpha_eq;

// use super::*;
// use super::{ast::parse, relation::subst};

// #[test]
// fn subst_test() {
//     let myparser = parse::MyParser;

//     let data: Vec<(&str, &str)> = vec![
//         ("Subst x[x := z] ;", "z"),
//         ("Subst y[x := z] ;", "y"),
//         ("Subst (\\x: PROP. x)[x := y] ;", "\\x: PROP. x"),
//         ("Subst (\\x: PROP. x)[z := y] ;", "\\x: PROP. x "),
//         ("Subst (\\x: PROP. y)[y := z] ;", "\\x: PROP. z "),
//         ("Subst (\\x: PROP. y)[y := x] ;", "\\x0: PROP. x "),
//         (
//             "Subst \\x: PROP. ( (\\y: PROP. (x y z)) (\\x: PROP. (x y z)) ) [x := t] ;",
//             "\\x: PROP. ( (\\y: PROP. (x y z)) (\\x: PROP. (x y z)) )",
//         ),
//         (
//             "Subst \\x: PROP. ( (\\y: PROP. (x y z)) (\\x: PROP. (x y z)) ) [y := t] ;",
//             "\\x: PROP. ( (\\y: PROP. (x y z)) (\\x: PROP. (x t z)) )",
//         ),
//         (
//             "Subst \\x: PROP. ( (\\y: PROP. (x y z)) (\\x: PROP. (x y z)) ) [z := t] ;",
//             "\\x: PROP. ( (\\y: PROP. (x y t)) (\\x: PROP. (x y t)) )",
//         ),
//         (
//             "Subst \\x: PROP. ( (\\y: PROP. (x y z)) (\\x: PROP. (x y z)) ) [z := x] ;",
//             "\\x0: PROP. ( (\\y: PROP. (x0 y x)) (\\x1: PROP. (x1 y x)) )",
//         ),
//         (
//             "Subst \\x: PROP. ( (\\y: PROP. (x y z)) (\\x: PROP. (x y z)) ) [y := x] ;",
//             "\\x0: PROP. ( (\\y: PROP. (x0 y z)) (\\x1: PROP. (x1 x z)) )",
//         ),
//     ];

//     for (input, expect) in data {
//         let Ok(either::Either::Left(parse::Command::Subst(e1, x, e2))) =
//             myparser.parse_command(input)
//         else {
//             panic!("")
//         };
//         let expect = myparser.parse_exp(expect).unwrap();
//         let result = subst(e1, &x, &e2);
//         assert!(alpha_eq(&result, &expect))
//     }
// }
