use crate::syntax::{Bind, Exp, Var};

#[macro_export]
macro_rules! sort {
    (SET($n: literal)) => {
        $crate::syntax::Exp::Sort($crate::syntax::Sort::Set($n))
    };
    (UNIV($n: literal)) => {
        $crate::syntax::Exp::Sort($crate::syntax::Sort::Univ($n))
    };
    (PROP) => {
        $crate::syntax::Exp::Sort($crate::syntax::Sort::Prop)
    };
}

#[macro_export]
macro_rules! bind {
    ($x: expr, $a: expr) => {{
        let var: $crate::syntax::Var = $x.into();
        $crate::syntax::Bind::new(var, $a)
    }};
}

#[macro_export]
macro_rules! var {
    ($v: expr) => {{ { $crate::syntax::Exp::Var($v.into()) } }};
}

#[macro_export]
macro_rules! prod {
    ($x: expr, $a: expr, $b: expr) => {{ $crate::syntax::Exp::Prod(bind!($x, $a), Box::new($b)) }};
}

#[macro_export]
macro_rules! lam {
    ($x: expr, $a: expr, $b: expr) => {{
        let bd = bind!($x, $a);
        $crate::syntax::Exp::Lam(bd, Box::new($b))
    }};
}

#[macro_export]
macro_rules! app {
    ($e: expr, $($x: expr),* ) => {{
        #[allow(unused_mut)]
        let mut e: $crate::syntax::Exp = $e;
        $(
            e = $crate::syntax::Exp::App(Box::new(e), Box::new($x));
        )*
        e
    }};
}

#[macro_export]
macro_rules! indtype {
    ($n: expr$ (, $vals:expr)* $(,)?) => {
        $crate::syntax::Exp::IndType {
            ind_type_name: $n.into(),
            parameters: vec![$($vals),*],
        }
    };
}

#[macro_export]
macro_rules! indcst {
    ($n: expr, $c: expr $(, $vals:expr)* $(,)?) => {
        $crate::syntax::Exp::IndCst {
            ind_type_name: $n.into(),
            constructor_name: $c.into(),
            parameters: vec![$($vals),*],
        }
    };
}

#[macro_export]
macro_rules! proof {
    ($n: expr) => {
        $crate::syntax::Exp::Proof(Box::new($n))
    };
}

#[macro_export]
macro_rules! power {
    ($n: expr) => {
        $crate::syntax::Exp::Pow(Box::new($n))
    };
}

#[macro_export]
macro_rules! subset {
    ($x: expr, $a: expr, $p: expr) => {
        $crate::syntax::Exp::Sub(bind!($x, $a), Box::new($p))
    };
}

#[macro_export]
macro_rules! pred {
    ($a: expr, $b: expr, $t: expr) => {
        $crate::syntax::Exp::Pred(Box::new($a), Box::new($b), Box::new($t))
    };
}

#[macro_export]
macro_rules! id {
    ($a: expr, $b: expr) => {
        $crate::syntax::Exp::Id(Box::new($a), Box::new($b))
    };
}

#[macro_export]
macro_rules! exists {
    ($a: expr) => {
        $crate::syntax::Exp::Exists(Box::new($a))
    };
}

#[macro_export]
macro_rules! take {
    ($x: expr, $t: expr, $a: expr) => {
        $crate::syntax::Exp::Take(bind!($x, $a), Box::new($a))
    };
}

// (a v[0] ... v[k])
pub fn assoc_apply(mut a: Exp, v: Vec<Exp>) -> Exp {
    for v in v {
        a = Exp::App(Box::new(a), Box::new(v))
    }
    a
}

pub fn assoc_apply_vec(mut v: Vec<Exp>) -> Exp {
    let rem = v.split_off(1);
    assoc_apply(v.pop().unwrap(), rem)
}

// (x[0]: t[0]) -> ... (x[k]: t[k]) -> e
pub fn assoc_prod(mut v: Vec<Bind>, mut e: Exp) -> Exp {
    while let Some(bind) = v.pop() {
        e = Exp::Prod(bind, Box::new(e));
    }
    e
}

// \ x[0]: t[0]). ... (x[k]: t[k]). e
pub fn assoc_lam(mut v: Vec<Bind>, mut e: Exp) -> Exp {
    while let Some(bind) = v.pop() {
        e = Exp::Lam(bind, Box::new(e));
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
    while let Exp::Prod(Bind { var: x, ty: a }, b) = e {
        v.push((x, *a));
        e = *b;
    }
    (v, e)
}

pub fn decompose_to_lam_exps(mut e: Exp) -> (Vec<(Var, Exp)>, Exp) {
    let mut v = vec![];
    while let Exp::Lam(Bind { var: x, ty: a }, b) = e {
        v.push((x, *a));
        e = *b;
    }
    (v, e)
}

#[cfg(test)]
mod tests {
    #[test]
    fn macro_expand() {
        let _ = sort!(SET(0));
        let _ = sort!(UNIV(1));
        let _ = sort!(PROP);
        let _ = var!("x");
        let _ = lam!("x", var!("A"), var!("x"));
        let _ = prod!("x", var!("A"), var!("x"));
        let _ = app!(var!("f"), var!("x"), var!("y"), var!("z"));
        let _ = indtype!("Nat");
        let _ = indcst!("Nat", "zero");
        let _ = indtype!("Vec", var!("A"), var!("n"));
        let _ = indcst!("Vec", "nil", var!("A"));
        let _ = proof!(var!("p"));
        let _ = power!(var!("A"));
        let _ = subset!("x", var!("A"), var!("p"));
        let _ = pred!(var!("a"), var!("b"), var!("T"));
        let _ = id!(var!("a"), var!("b"));
        let _ = exists!(var!("A"));
        let _ = take!("x", var!("T"), var!("A"));
    }
}
