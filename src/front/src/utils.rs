use crate::syntax::{Exp, Var};

#[macro_export]
macro_rules! sort {
    (SET($n: literal)) => {
        $crate::syntax::Exp::Sort($crate::syntax::Sort::Set($n))
    };
    (UNIV) => {
        $crate::syntax::Exp::Sort($crate::syntax::Sort::Univ)
    };
    (PROP) => {
        $crate::syntax::Exp::Sort($crate::syntax::Sort::Prop)
    };
}

#[macro_export]
macro_rules! var {
    ($v: literal) => {{ { $crate::syntax::Exp::Var($v) } }};
}

// (a v[0] ... v[k])
pub fn assoc_apply(mut a: Exp, v: Vec<Exp>) -> Exp {
    for v in v {
        a = Exp::App {
            func: Box::new(a),
            arg: Box::new(v),
        }
    }
    a
}

// (v[0] ... v[k])
// panic if v is empty
pub fn assoc_apply_vec(mut v: Vec<Exp>) -> Exp {
    let rem = v.split_off(1);
    assoc_apply(v.pop().unwrap(), rem)
}

// // (x[0]: t[0]) -> ... (x[k]: t[k]) -> e
// pub fn assoc_prod(mut v: Vec<(Var, Exp)>, mut e: Exp) -> Exp {
//     while let Some(bind) = v.pop() {
//         e = Exp::Prod(bind, Box::new(e));
//     }
//     e
// }

// // (x[0]: t[0]). ... (x[k]: t[k]). e
// pub fn assoc_lam(mut v: Vec<Bind>, mut e: Exp) -> Exp {
//     while let Some(bind) = v.pop() {
//         e = Exp::Lam(bind, Box::new(e));
//     }
//     e
// }

// // e = (((...((e1 e2) e3) ... e(n-1) ) e(n) ) |-> (e1, [e2, ..., en])
// pub fn decompose_to_app_exps(mut e: Exp) -> (Exp, Vec<Exp>) {
//     let mut v = vec![];
//     while let Exp::App(t1, t2) = e {
//         v.push(*t2);
//         e = *t1;
//     }
//     v.reverse();
//     (e, v)
// }

// pub fn decompose_to_prod_exps(mut e: Exp) -> (Vec<(Var, Exp)>, Exp) {
//     let mut v = vec![];
//     while let Exp::Prod(Bind { var: x, ty: a }, b) = e {
//         v.push((x, *a));
//         e = *b;
//     }
//     (v, e)
// }

// pub fn decompose_to_lam_exps(mut e: Exp) -> (Vec<(Var, Exp)>, Exp) {
//     let mut v = vec![];
//     while let Exp::Lam(Bind { var: x, ty: a }, b) = e {
//         v.push((x, *a));
//         e = *b;
//     }
//     (v, e)
// }

#[cfg(test)]
mod tests {
    #[test]
    fn macro_expand() {
        let _ = sort!(SET(0));
        let _ = sort!(UNIV);
        let _ = sort!(PROP);
    }
}
