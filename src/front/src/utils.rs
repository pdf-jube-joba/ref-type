use crate::syntax::Exp;

#[macro_export]
macro_rules! sort {
    (SET($n: literal)) => {
        $crate::syntax::Exp::Sort(kernel::exp::Sort::Set($n))
    };
    (PROP) => {
        $crate::syntax::Exp::Sort(kernel::exp::Sort::Prop)
    };
    (PROPKIND) => {
        $crate::syntax::Exp::Sort(kernel::exp::Sort::PropKind)
    };
}

#[macro_export]
macro_rules! var {
    ($v: literal) => {{ { $crate::syntax::Exp::Var($v) } }};
}

// (a v[0] ... v[k])
pub fn assoc_apply(mut a: Exp, v: Vec<Exp>) -> Exp {
    for v in v {
        a = Exp::App {
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
