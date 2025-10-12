use crate::{calculus::shift, utils};

use super::coreexp::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveTypeSpecs {
    pub parameter: Vec<CoreExp>,
    pub arity: Vec<CoreExp>,
    pub constructors: Vec<ConstructorType>,
}

impl InductiveTypeSpecs {
    fn primitive_recursion(&self) -> CoreExp {
        todo!()
    }
}

/*
constructor of type params[0] -> ... -> params[n] -> THIS args[0] ... args[m]
type_param_len is length of given type's parameter (is is external information to constructor type)
e.g.
```
Inductive List (A: Type) : Type :=
| nil : List A
| cons : A -> List A -> List A.
```
ConstructorType of nil = {
    type_param_len: 1, // from `A` is declared in `Inductive List (A: Type)`
    params: []
    args: [Var(0)]
}
ConstructorType of cons = {
    type_param_len: 1,
    params: [Simple(Var(0)), StrictPositive {pre: [], args: [List Var(0)]}]
    args: [Var(0)]
}
*/
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorType {
    pub type_param_len: usize,
    // any free variable in params must be in 0..type_param_len
    pub params: Vec<IndParam>,
    // any free variable in params must be in 0..type_param_len
    pub args: Vec<CoreExp>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IndParam {
    StrictPositive {
        pre: Vec<CoreExp>,
        args: Vec<CoreExp>,
    },
    Simple(CoreExp),
}

// for given constructor type, return type of corresponding eliminator case
// elim_type(ConstructorType , motive or return type, element of THIS type, some useful var) where
// elim_type((THIS a_0 ... a_m), q, c, x) => q a_0 ... a_m c
// elim_type((p: A) -> rest, q, c, x) => (_p: A) -> elim_type(rest, q, c _p, x) where A is simple (this is not represented in De Bruijn index) **_p* is new variable
// elim_type((p: ((x_0: M_0) -> ... -> (x_n: M_n) -> THIS m_0 ... m_l), q, c, x) =>
// (p: ((x_0: M_0) -> ... -> (x_n: M_n) -> THIS m_0 ... m_l))
// -> (_e: (x_0: M_0) -> ... -> (x_n: M_n) -> (q m_0 ... m_l (p x)))
// -> elim_type(rest, q, c p, x) where THIS is the inductive type being defined
fn eliminator_type_recdef(
    cst_type: &ConstructorType,
    q: &CoreExp,
    c: &CoreExp,
    index: usize,   // index of current attension of params in cst_type in inductive type
    this: &CoreExp, // this should be the inductive type itself (extenal)
) -> CoreExp {
    if index == cst_type.type_param_len {
        // q a_0 ... a_m c
        return CoreExp::App {
            func: Box::new(utils::assoc_apply(q.clone(), cst_type.args.clone())),
            arg: Box::new(c.clone()),
        };
    }
    match &cst_type.params[index] {
        IndParam::StrictPositive { pre, args } => {
            todo!()
        }
        IndParam::Simple(core_exp) => CoreExp::Prod {
            ty: Box::new(core_exp.clone()),
            body: Box::new(eliminator_type_recdef(
                cst_type,
                q,
                &CoreExp::App {
                    func: Box::new(c.clone()),
                    arg: Box::new(core_exp.clone()),
                },
                index + 1,
                this,
            )),
        },
    }
}

fn recursor(
    cst_type: &ConstructorType,
    ff: &CoreExp,
    f: &CoreExp,
    index: usize,
    this: &CoreExp, // this should be the inductive type itself (extenal )
) -> CoreExp {
    todo!()
}

// (simple) check well-formedness of elim and reduce
pub fn inductive_type_elim_reduction(e: &CoreExp) -> Result<CoreExp, String> {
    let CoreExp::IndTypeElim {
        ty,
        elim,
        return_type: _,
        cases,
    } = e
    else {
        return Err("Not an InductiveTypeElim".to_string());
    };
    let CoreExp::IndTypeCst { ty: ty2, idx, args } = elim.as_ref() else {
        return Err("Elim is not an InductiveTypeCst".to_string());
    };
    if !std::rc::Rc::ptr_eq(ty, ty2) {
        return Err("Elim type mismatch".to_string());
    }
    if *idx >= ty.parameter.len() {
        return Err("Constructor index out of bounds".to_string());
    }
    let case = &cases[*idx];
    if args.len() != ty.parameter.len() {
        return Err("Constructor arguments length mismatch".to_string());
    }
    todo!()
}
