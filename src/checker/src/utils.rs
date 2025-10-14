use super::coreexp::*;

#[macro_export]
macro_rules! var {
    ($name:expr) => {
        Var::new($name)
    };
}

#[macro_export]
macro_rules! sort {
    (Set( $i:literal )) => {
        Sort::Set($i)
    };
    (Prop) => {
        Sort::Prop
    };
    (Univ) => {
        Sort::Univ
    };
    (Type) => {
        Sort::Type
    };
}

pub fn assoc_apply(mut a: CoreExp, v: Vec<CoreExp>) -> CoreExp {
    for arg in v {
        a = CoreExp::App {
            func: Box::new(a),
            arg: Box::new(arg),
        };
    }
    a
}

pub fn assoc_lam(v: Vec<(Var, CoreExp)>, mut body: CoreExp) -> CoreExp {
    for (var, ty) in v.into_iter().rev() {
        body = CoreExp::Lam {
            var,
            ty: Box::new(ty),
            body: Box::new(body),
        };
    }
    body
}

pub fn assoc_prod(v: Vec<(Var, CoreExp)>, mut body: CoreExp) -> CoreExp {
    for (var, ty) in v.into_iter().rev() {
        body = CoreExp::Prod {
            var,
            ty: Box::new(ty),
            body: Box::new(body),
        };
    }
    body
}

pub fn decompose_app(mut e: CoreExp) -> (CoreExp, Vec<CoreExp>) {
    let mut args = vec![];
    while let CoreExp::App { func, arg } = e {
        args.push(*arg);
        e = *func;
    }
    args.reverse();
    (e, args)
}

pub fn decompose_app_ref(e: &CoreExp) -> (&CoreExp, Vec<&CoreExp>) {
    let mut args = vec![];
    let mut e = e;
    while let CoreExp::App { func, arg } = e {
        args.push(arg.as_ref());
        e = func.as_ref();
    }
    args.reverse();
    (e, args)
}

pub fn decompose_prod(mut e: CoreExp) -> (Vec<(Var, CoreExp)>, CoreExp) {
    let mut vars = vec![];
    while let CoreExp::Prod { var, ty, body } = e {
        vars.push((var, *ty));
        e = *body;
    }
    vars.reverse();
    (vars, e)
}

pub fn decompose_prod_ref(e: &CoreExp) -> (Vec<(&Var, &CoreExp)>, &CoreExp) {
    let mut vars = vec![];
    let mut e = e;
    while let CoreExp::Prod { var, ty, body } = e {
        vars.push((var, ty.as_ref()));
        e = body.as_ref();
    }
    vars.reverse();
    (vars, e)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_macros() {
        var!("x");
        var!("y");
        var!("z");
        assert_eq!(var!("x").name(), "x");
        // different pointer (but same name => alpha equivalent)
        assert!(!var!("x").is_eq_ptr(&var!("x")));

        assert_eq!(sort!(Set(0)), Sort::Set(0));
        assert_eq!(sort!(Set(1)), Sort::Set(1));
        assert_eq!(sort!(Prop), Sort::Prop);
        assert_eq!(sort!(Univ), Sort::Univ);
        assert_eq!(sort!(Type), Sort::Type);
    }
}
