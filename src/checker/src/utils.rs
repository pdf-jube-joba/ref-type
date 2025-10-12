use super::coreexp::*;

pub fn assoc_apply(mut a: CoreExp, v: Vec<CoreExp>) -> CoreExp {
    for arg in v {
        a = CoreExp::App {
            func: Box::new(a),
            arg: Box::new(arg),
        };
    }
    a
}

pub fn assoc_lam(v: Vec<CoreExp>, mut body: CoreExp) -> CoreExp {
    for ty in v.into_iter().rev() {
        body = CoreExp::Lam {
            ty: Box::new(ty),
            body: Box::new(body),
        };
    }
    body
}

pub fn assoc_prod(v: Vec<CoreExp>, mut body: CoreExp) -> CoreExp {
    for ty in v.into_iter().rev() {
        body = CoreExp::Prod {
            ty: Box::new(ty),
            body: Box::new(body),
        };
    }
    body
}
