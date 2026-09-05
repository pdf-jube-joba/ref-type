use super::exp::*;
use crate::ids::SymbolId;

pub fn assoc_apply(arena: &Arena, mut func: Exp, args: Vec<Exp>) -> Exp {
    for arg in args {
        func = arena.alloc(ExpNode::App { func, arg });
    }
    func
}

pub fn assoc_lam(arena: &Arena, binders: Vec<(SymbolId, Exp)>, mut body: Exp) -> Exp {
    for (var, ty) in binders.into_iter().rev() {
        body = arena.alloc(ExpNode::Lam { var, ty, body });
    }
    body
}

pub fn assoc_prod(arena: &Arena, binders: Vec<(SymbolId, Exp)>, mut body: Exp) -> Exp {
    for (var, ty) in binders.into_iter().rev() {
        body = arena.alloc(ExpNode::Prod { var, ty, body });
    }
    body
}

// a0 a1 ... an  ==>  (a0, [a1, ..., an])
pub fn decompose_app(arena: &Arena, mut exp: Exp) -> (Exp, Vec<Exp>) {
    let mut args = vec![];
    while let ExpNode::App { func, arg } = arena.get(exp) {
        args.push(arg);
        exp = func;
    }
    args.reverse();
    (exp, args)
}

// (x1 : A1) ... (xn : An) -> B  ==>  ([(x1, A1), ..., (xn, An)], B)
pub fn decompose_prod(arena: &Arena, mut exp: Exp) -> (Vec<(SymbolId, Exp)>, Exp) {
    let mut vars = vec![];
    while let ExpNode::Prod { var, ty, body } = arena.get(exp) {
        vars.push((var, ty));
        exp = body;
    }
    (vars, exp)
}

#[macro_export]
macro_rules! app {
    ($arena:expr, func: $func:expr, arg: $arg:expr $(,)?) => {
        $arena.alloc($crate::exp::ExpNode::App {
            func: $func,
            arg: $arg,
        })
    };
    ($arena:expr, arg: $arg:expr, func: $func:expr $(,)?) => {
        $arena.alloc($crate::exp::ExpNode::App {
            func: $func,
            arg: $arg,
        })
    };
    ($arena:expr, $func:expr, $arg:expr) => {
        $arena.alloc($crate::exp::ExpNode::App {
            func: $func,
            arg: $arg,
        })
    };
}

#[macro_export]
macro_rules! lam {
    ($arena:expr, var: $var:expr, ty: $ty:expr, body: $body:expr $(,)?) => {
        $arena.alloc($crate::exp::ExpNode::Lam {
            var: $var,
            ty: $ty,
            body: $body,
        })
    };
    ($arena:expr, $var:expr, $ty:expr, $body:expr) => {
        $arena.alloc($crate::exp::ExpNode::Lam {
            var: $var,
            ty: $ty,
            body: $body,
        })
    };
}

#[macro_export]
macro_rules! prod {
    ($arena:expr, var: $var:expr, ty: $ty:expr, body: $body:expr $(,)?) => {
        $arena.alloc($crate::exp::ExpNode::Prod {
            var: $var,
            ty: $ty,
            body: $body,
        })
    };
    ($arena:expr, $var:expr, $ty:expr, $body:expr) => {
        $arena.alloc($crate::exp::ExpNode::Prod {
            var: $var,
            ty: $ty,
            body: $body,
        })
    };
}

pub use {app, lam, prod};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ids::{ModuleId, ModuleParamId};
    use crate::sort::Sort;

    #[test]
    fn test_macros_and_decompose() {
        let arena = Arena::new();
        let x = SymbolId(2);
        let y = SymbolId(3);
        let f_exp = arena.exp_module_param(ModuleParamId {
            module: ModuleId(0),
            position: 0,
        });
        let x_exp = arena.exp_module_param(ModuleParamId {
            module: ModuleId(0),
            position: 1,
        });
        let y_exp = arena.exp_module_param(ModuleParamId {
            module: ModuleId(0),
            position: 2,
        });
        let application = app!(&arena, app!(&arena, f_exp, x_exp), y_exp);
        let (head, args) = decompose_app(&arena, application);
        assert_eq!(arena.as_module_param(head).unwrap().position, 0);
        assert_eq!(args, vec![x_exp, y_exp]);

        let ty = arena.sort(Sort::Set(0));
        let product = prod!(&arena, x, ty, prod!(&arena, y, ty, ty));
        let (binders, body) = decompose_prod(&arena, product);
        assert_eq!(binders.len(), 2);
        assert_eq!(body, ty);
    }
}
