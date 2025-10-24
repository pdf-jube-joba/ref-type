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

#[cfg(test)]
mod tests {
    #[test]
    fn macro_expand() {
        let _ = sort!(SET(0));
        let _ = sort!(PROP);
    }
}
