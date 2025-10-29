use super::exp::*;

pub fn assoc_apply(mut a: Exp, v: Vec<Exp>) -> Exp {
    for arg in v {
        a = Exp::App {
            func: a.into(),
            arg: arg.into(),
        };
    }
    a
}

pub fn assoc_lam(v: Vec<(Var, Exp)>, mut body: Exp) -> Exp {
    for (var, ty) in v.into_iter().rev() {
        body = Exp::Lam {
            var,
            ty: ty.into(),
            body: body.into(),
        };
    }
    body
}

pub fn assoc_prod(v: Vec<(Var, Exp)>, mut body: Exp) -> Exp {
    for (var, ty) in v.into_iter().rev() {
        body = Exp::Prod {
            var,
            ty: ty.into(),
            body: body.into(),
        };
    }
    body
}

pub fn decompose_app(mut e: Exp) -> (Exp, Vec<Exp>) {
    let mut args = vec![];
    while let Exp::App { func, arg } = e {
        args.push(*arg);
        e = *func;
    }
    args.reverse();
    (e, args)
}

pub fn decompose_app_ref(e: &Exp) -> (&Exp, Vec<&Exp>) {
    let mut args = vec![];
    let mut e = e;
    while let Exp::App { func, arg } = e {
        args.push(arg.as_ref());
        e = func.as_ref();
    }
    args.reverse();
    (e, args)
}

pub fn decompose_prod(mut e: Exp) -> (Vec<(Var, Exp)>, Exp) {
    let mut vars = vec![];
    while let Exp::Prod { var, ty, body } = e {
        vars.push((var, *ty));
        e = *body;
    }
    vars.reverse();
    (vars, e)
}

pub fn decompose_prod_ref(e: &Exp) -> (Vec<(&Var, &Exp)>, &Exp) {
    let mut vars = vec![];
    let mut e = e;
    while let Exp::Prod { var, ty, body } = e {
        vars.push((var, ty.as_ref()));
        e = body.as_ref();
    }
    vars.reverse();
    (vars, e)
}

#[macro_export]
macro_rules! var {
    ($name:expr) => {
        $crate::exp::Var::new($name)
    };
}

#[macro_export]
macro_rules! var_exp {
    ($name:expr) => {
        $crate::exp::Exp::Var(Var::new($name))
    };
}

#[macro_export]
macro_rules! app {
    // named: func, arg（この順）
    ( func: $f:expr , arg: $a:expr $(,)? ) => {
        $crate::exp::Exp::App {
            func: $f.into(),
            arg: $a.into(),
        }
    };
    // named: arg, func（逆順）
    ( arg: $a:expr , func: $f:expr $(,)? ) => {
        $crate::exp::Exp::App {
            func: $f.into(),
            arg: $a.into(),
        }
    };
    // 位置引数版
    ( $f:expr , $a:expr ) => {
        $crate::exp::Exp::App {
            func: $f.into(),
            arg: $a.into(),
        }
    };
}

#[macro_export]
macro_rules! lam {
    ( var: $v:expr , ty: $t:expr , body: $b:expr $(,)? ) => {
        $crate::exp::Exp::Lam {
            var: $v,
            ty: $t.into(),
            body: $b.into(),
        }
    };
    ( $v:expr, $t:expr, $b:expr) => {
        $crate::exp::Exp::Lam {
            var: $v,
            ty: $t.into(),
            body: $b.into(),
        }
    };
}

#[macro_export]
macro_rules! prod {
    ( var: $v:expr , ty: $t:expr , body: $b:expr $(,)? ) => {
        $crate::exp::Exp::Prod {
            var: $v,
            ty: $t.into(),
            body: $b.into(),
        }
    };
    ( $v:expr, $t:expr, $b:expr) => {
        $crate::exp::Exp::Prod {
            var: $v,
            ty: $t.into(),
            body: $b.into(),
        }
    };
}

#[macro_export]
macro_rules! goal {
    ( $ctx:expr ; $prop:expr => $proof:expr) => {
        $crate::exp::ProveGoal {
            extended_ctx: ($ctx).into(),
            goal_prop: $prop,
            proof_term: $proof,
        }
    };
}

#[macro_export]
macro_rules! prooflater {
    ($p:expr) => {
        $crate::exp::Exp::ProveLater { prop: $p.into() }
    };
}

pub use {app, goal, lam, prod, prooflater, var, var_exp};

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_macros() {
        var!("x");
        var!("y");
        var!("z");
        app! { func: var_exp!("f"), arg: var_exp!("x") };
        app! { arg: var_exp!("x"), func: var_exp!("f") };
        app! { var_exp!("f"), var_exp!("x") };
        app! { Box::new(var_exp!("f")), var_exp!("x") };
        lam! { var: var!("x"), ty: var_exp!("A"), body: var_exp!("x")};
        prod! { var: var!("x"), ty: var_exp!("A"), body: var_exp!("B")};
        goal! {
            vec![(var!("A"), Exp::Sort(Sort::Prop))];
            Exp::Var(var!("A")) => var_exp!("a")
        };
    }
}
