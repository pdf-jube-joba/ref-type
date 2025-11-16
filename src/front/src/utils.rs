use crate::syntax::SExp;

#[macro_export]
macro_rules! sort {
    (SET($n: literal)) => {
        $crate::syntax::SExp::Sort(kernel::exp::Sort::Set($n))
    };
    (PROP) => {
        $crate::syntax::SExp::Sort(kernel::exp::Sort::Prop)
    };
    (PROPKIND) => {
        $crate::syntax::SExp::Sort(kernel::exp::Sort::PropKind)
    };
}

#[macro_export]
macro_rules! var {
    ($v: literal) => {{ { $crate::syntax::Exp::Var($v) } }};
}

// (a v[0] ... v[k])
pub fn assoc_apply(mut a: SExp, v: Vec<SExp>) -> SExp {
    for v in v {
        a = SExp::App {
            func: Box::new(a),
            arg: Box::new(v),
            piped: false,
        }
    }
    a
}

// (a v[0] ... v[k])
pub fn assoc_apply_vec(mut v: Vec<SExp>) -> SExp {
    assert!(!v.is_empty());
    let vs = v.split_off(1);
    let mut a = v.pop().unwrap();
    for v in vs {
        a = SExp::App {
            func: Box::new(a),
            arg: Box::new(v),
            piped: false,
        }
    }
    a
}

pub fn decompose_prod(mut e: SExp) -> (Vec<crate::syntax::Bind>, SExp) {
    let mut binds = vec![];
    loop {
        match e {
            SExp::Prod { bind, body } => {
                binds.push(bind);
                e = *body;
            }
            _ => break,
        }
    }
    (binds, e)
}

#[cfg(test)]
mod tests {
    #[test]
    fn macro_expand() {
        let _ = sort!(SET(0));
        let _ = sort!(PROP);
    }
}
