use super::exp::*;

pub fn assoc_apply(arena: &Arena, mut func: Exp, args: Vec<Exp>) -> Exp {
    for arg in args {
        func = arena.alloc(Node::App { func, arg });
    }
    func
}

pub fn assoc_lam(arena: &Arena, binders: Vec<(Var, Exp)>, mut body: Exp) -> Exp {
    for (var, ty) in binders.into_iter().rev() {
        body = arena.alloc(Node::Lam { var, ty, body });
    }
    body
}

pub fn assoc_prod(arena: &Arena, binders: Vec<(Var, Exp)>, mut body: Exp) -> Exp {
    for (var, ty) in binders.into_iter().rev() {
        body = arena.alloc(Node::Prod { var, ty, body });
    }
    body
}

// a0 a1 ... an  ==>  (a0, [a1, ..., an])
pub fn decompose_app(arena: &Arena, mut exp: Exp) -> (Exp, Vec<Exp>) {
    let mut args = vec![];
    while let Node::App { func, arg } = arena.get(exp) {
        args.push(arg);
        exp = func;
    }
    args.reverse();
    (exp, args)
}

// (x1 : A1) ... (xn : An) -> B  ==>  ([(x1, A1), ..., (xn, An)], B)
pub fn decompose_prod(arena: &Arena, mut exp: Exp) -> (Vec<(Var, Exp)>, Exp) {
    let mut vars = vec![];
    while let Node::Prod { var, ty, body } = arena.get(exp) {
        vars.push((var, ty));
        exp = body;
    }
    (vars, exp)
}

#[macro_export]
macro_rules! var {
    ($name:expr) => {
        $crate::exp::Var::new($name)
    };
}

#[macro_export]
macro_rules! var_exp {
    ($arena:expr, $name:expr) => {
        $arena.var($name.clone())
    };
}

#[macro_export]
macro_rules! app {
    ($arena:expr, func: $func:expr, arg: $arg:expr $(,)?) => {
        $arena.alloc($crate::exp::Node::App {
            func: $func,
            arg: $arg,
        })
    };
    ($arena:expr, arg: $arg:expr, func: $func:expr $(,)?) => {
        $arena.alloc($crate::exp::Node::App {
            func: $func,
            arg: $arg,
        })
    };
    ($arena:expr, $func:expr, $arg:expr) => {
        $arena.alloc($crate::exp::Node::App {
            func: $func,
            arg: $arg,
        })
    };
}

#[macro_export]
macro_rules! lam {
    ($arena:expr, var: $var:expr, ty: $ty:expr, body: $body:expr $(,)?) => {
        $arena.alloc($crate::exp::Node::Lam {
            var: $var,
            ty: $ty,
            body: $body,
        })
    };
    ($arena:expr, $var:expr, $ty:expr, $body:expr) => {
        $arena.alloc($crate::exp::Node::Lam {
            var: $var,
            ty: $ty,
            body: $body,
        })
    };
}

#[macro_export]
macro_rules! prod {
    ($arena:expr, var: $var:expr, ty: $ty:expr, body: $body:expr $(,)?) => {
        $arena.alloc($crate::exp::Node::Prod {
            var: $var,
            ty: $ty,
            body: $body,
        })
    };
    ($arena:expr, $var:expr, $ty:expr, $body:expr) => {
        $arena.alloc($crate::exp::Node::Prod {
            var: $var,
            ty: $ty,
            body: $body,
        })
    };
}

pub use {app, lam, prod, var};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_macros_and_decompose() {
        let arena = Arena::new();
        let f = var!("f");
        let x = var!("x");
        let y = var!("y");
        let f_exp = arena.var(f.clone());
        let x_exp = arena.var(x.clone());
        let y_exp = arena.var(y.clone());
        let application = app!(&arena, app!(&arena, f_exp, x_exp), y_exp);
        let (head, args) = decompose_app(&arena, application);
        assert_eq!(arena.as_var(head).unwrap(), f);
        assert_eq!(args, vec![x_exp, y_exp]);

        let ty = arena.sort(Sort::Set(0));
        let product = prod!(&arena, x, ty, prod!(&arena, y, ty, ty));
        let (binders, body) = decompose_prod(&arena, product);
        assert_eq!(binders.len(), 2);
        assert_eq!(body, ty);
    }
}
