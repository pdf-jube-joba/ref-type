use crate::syntax::ast::{Exp, Var};

#[macro_export]
macro_rules! var {
    ($v: expr) => {{
        {
            Exp::Var($v.into())
        }
    }};
}

#[macro_export]
macro_rules! lam {
    ($x: expr, $a: expr, $b: expr) => {{
        $crate::syntax::ast::Exp::Lam($x, Box::new($a), Box::new($b))
    }};
}

#[macro_export]
macro_rules! prod {
    ($x: expr, $a: expr, $b: expr) => {{
        $crate::syntax::ast::Exp::Prod($x, Box::new($a), Box::new($b))
    }};
}

#[macro_export]
macro_rules! app {
        ($e: expr, $($x: expr),* ) => {{
            #[allow(unused_mut)]
            let mut e: Exp = $e;
            $(
                e = Exp::App(Box::new(e), Box::new($x));
            )*
            e
        }};
    }

#[macro_export]
macro_rules! sort_set {
    () => {
        Exp::Sort(Sort::Set)
    };
}

// (a v[0] ... v[k])
pub fn assoc_apply(mut a: Exp, v: Vec<Exp>) -> Exp {
    for v in v {
        a = Exp::App(Box::new(a), Box::new(v))
    }
    a
}

// (x[0]: t[0]) -> ... (x[k]: t[k]) -> e
pub fn assoc_prod(mut v: Vec<(Var, Exp)>, mut e: Exp) -> Exp {
    while let Some((x, a)) = v.pop() {
        e = Exp::Prod(x, Box::new(a), Box::new(e));
    }
    e
}

// \ x[0]: t[0]). ... (x[k]: t[k]). e
pub fn assoc_lam(mut v: Vec<(Var, Exp)>, mut e: Exp) -> Exp {
    while let Some((x, a)) = v.pop() {
        e = Exp::Lam(x, Box::new(a), Box::new(e));
    }
    e
}

// e = (((...((e1 e2) e3) ... e(n-1) ) e(n) ) |-> (e1, [e2, ..., en])
pub fn decompose_to_app_exps(mut e: Exp) -> (Exp, Vec<Exp>) {
    let mut v = vec![];
    while let Exp::App(t1, t2) = e {
        v.push(*t2);
        e = *t1;
    }
    v.reverse();
    (e, v)
}

pub fn decompose_to_prod_exps(mut e: Exp) -> (Vec<(Var, Exp)>, Exp) {
    let mut v = vec![];
    while let Exp::Prod(x, a, b) = e {
        v.push((x, *a));
        e = *b;
    }
    (v, e)
}

pub fn decompose_to_lam_exps(mut e: Exp) -> (Vec<(Var, Exp)>, Exp) {
    let mut v = vec![];
    while let Exp::Lam(x, a, b) = e {
        v.push((x, *a));
        e = *b;
    }
    (v, e)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn macros() {
        assert_eq!(var! {"a"}, Exp::Var("a".into()));
        assert_eq!(
            lam! { "a".into(), var!{"b"}, var!{"c"} },
            Exp::Lam(
                "a".into(),
                Box::new(Exp::Var("b".into())),
                Box::new(Exp::Var("c".into()))
            )
        );
        assert_eq!(
            prod!("a".into(), var! {"b"}, var! {"c"}),
            Exp::Prod(
                "a".into(),
                Box::new(Exp::Var("b".into())),
                Box::new(Exp::Var("c".into()))
            )
        );
        assert_eq!(app!(var! {"a"},), Exp::Var("a".into()));
        assert_eq!(
            app!(var! {"a"}, var! {"b"}, var! {"c"}),
            Exp::App(
                Box::new(Exp::App(
                    Box::new(Exp::Var("a".into())),
                    Box::new(Exp::Var("b".into()))
                )),
                Box::new(Exp::Var("c".into()))
            )
        );
    }
}
