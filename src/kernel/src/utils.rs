use super::exp::*;

pub fn assoc_apply(mut a: Exp, v: Vec<Exp>) -> Exp {
    for arg in v {
        a = Exp::App {
            func: Box::new(a),
            arg: Box::new(arg),
        };
    }
    a
}

pub fn assoc_lam(v: Vec<(Var, Exp)>, mut body: Exp) -> Exp {
    for (var, ty) in v.into_iter().rev() {
        body = Exp::Lam {
            var,
            ty: Box::new(ty),
            body: Box::new(body),
        };
    }
    body
}

pub fn assoc_prod(v: Vec<(Var, Exp)>, mut body: Exp) -> Exp {
    for (var, ty) in v.into_iter().rev() {
        body = Exp::Prod {
            var,
            ty: Box::new(ty),
            body: Box::new(body),
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
        Var::new($name)
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_macros() {
        var!("x");
        var!("y");
        var!("z");
    }
}
