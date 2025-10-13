use crate::utils;

use super::coreexp::*;

#[derive(Debug, Clone)]
pub struct InductiveTypeSpecs {
    pub parameter: Vec<(Var, CoreExp)>,
    pub arity: Vec<(Var, CoreExp)>,
    pub sort: Sort,
    pub constructors: Vec<ConstructorType>,
}

impl InductiveTypeSpecs {
    fn constructor_len(&self) -> usize {
        self.constructors.len()
    }
    fn param_args_len(&self) -> usize {
        self.parameter.len()
    }
    fn arg_len_cst(&self, idx: usize) -> usize {
        self.constructors[idx].args.len()
    }
}

/*
constructor of type (v[0]: params[0]) -> ... -> (v[n]: params[n]) -> THIS args[0] ... args[m]
e.g.
```
Inductive List (A: Type) : Type :=
| nil : List A
| cons : A -> List A -> List A.
```
ConstructorType of nil = {
    params: []
    args: [Var("A")]
}
ConstructorType of cons = {
    type_param_len: 1,
    params: [Simple((Var("_"), Var("A")), StrictPositive {pre: [], args: [Var("A")]})]}]
    args: [Var("A")]
}
*/
#[derive(Debug, Clone)]
pub struct ConstructorType {
    pub params: Vec<IndParam>,
    pub args: Vec<CoreExp>,
}

#[derive(Debug, Clone)]
pub enum IndParam {
    StrictPositive {
        pre: Vec<(Var, CoreExp)>,
        args: Vec<CoreExp>,
    },
    Simple((Var, CoreExp)),
}

// return type of corresponding eliminator case for the given constructor
/*
- elim_type(X a[], q, c, THIS) = q a[] c
  - `X` のところには型名が来る想定
- simple case: elim_type((x: t) -> n, q, c, THIS)
  - = (x: t) -> elim_type(n, q, c x, THIS)
- strpos case: elim_type(((x[]: t[]) -> THIS m[]) -> n, q, c, THIS)
  - = (p: (x[]: t[]) -> THIS m[]) // `THIS` のところには型名が来る想定
  - -> (_: (x[]: t[]) -> q m[] (p x[]))
  - -> elim_type(n, (c p), THIS)
*/
fn eliminator_type(
    cst_type: &ConstructorType,
    q: &CoreExp,
    c: &CoreExp,
    this: &CoreExp, // this should be the inductive type itself (extenaly given)
) -> CoreExp {
    let ConstructorType {
        params: poss,
        args: a,
    } = cst_type;
    let mut c = c.clone();

    // c <- q args[0] ... args[m] c
    c = {
        let e = utils::assoc_apply(q.clone(), a.clone());
        CoreExp::App {
            func: Box::new(e),
            arg: Box::new(c.clone()),
        }
    };

    let mut bindstack = vec![];

    for pos in poss.iter().rev() {
        match pos {
            IndParam::Simple((x, t)) => {
                // c <- (c x)
                c = CoreExp::App {
                    func: Box::new(c),
                    arg: Box::new(CoreExp::Var(x.clone())),
                };
                // (x: t) -> foobar
                bindstack.push((x.clone(), t.clone()));
            }
            IndParam::StrictPositive { pre: xts, args: m } => {
                // new variable p
                let p = Var::new("p");
                // c <- (c p)
                c = CoreExp::App {
                    func: Box::new(c),
                    arg: Box::new(CoreExp::Var(p.clone())),
                };
                // (_: r) -> foobar
                //      where r = (x[]: t[]) -> q m[] (p x[])
                {
                    // r = (x[]: t[]) -> q m[] (p x[]) to push in bindstack (_: r)
                    let r = {
                        // q m[] (p x[])
                        let r = CoreExp::App {
                            func: Box::new(utils::assoc_apply(q.clone(), m.clone())), // q m[]
                            arg: Box::new(utils::assoc_apply(
                                CoreExp::Var(p.clone()),
                                xts.iter().map(|(x, _)| CoreExp::Var(x.clone())).collect(),
                            )), // (p x[])
                        };

                        // (x[]: t[]) -> ...
                        utils::assoc_prod(xts.clone(), r)
                    };
                    // new variable "_"
                    let unused = Var::new("_");

                    // push in bindstack
                    bindstack.push((unused, r));
                }
                // (p: (x[]: t[]) -> THIS m[]) -> foobar
                {
                    // (x[]: t[]) -> THIS m[]
                    let r = {
                        let r = utils::assoc_apply(this.clone(), m.clone()); // THIS m[]
                        utils::assoc_prod(xts.clone(), r) // (x[]: t[]) -> THIS m[]
                    };
                    bindstack.push((p, r));
                }
            }
        }
    }

    // finally, wrap with all the bindings
    utils::assoc_prod(bindstack, c)
}

// recursor of the given constructor
/*
- recursor(THIS a[], q, f, THIS) = f
- simple case: recursor((x: t) -> n, q, f, THIS)
  - = (x: t) => recursor(n, q, (f x), THIS)
- strpos case: recursor(((x[]: t[]) -> THIS m[]) -> n, q, f, THIS)
  - = (p: (x[]: t[]) -> THIS m[])
  - => recursor(n, q, (f p ((x[]: t[]) -> q m[] (p x[]))), THIS)
*/
fn recursor(
    cst_type: &ConstructorType,
    ff: &CoreExp,
    f: &CoreExp,
    this: &CoreExp, // this should be the inductive type itself (extenal )
) -> CoreExp {
    let ConstructorType {
        params: poss,
        args: _, // a but not used
    } = cst_type;
    let mut f = f.clone();

    let mut bindstack = vec![];

    for pos in poss.iter().rev() {
        match pos {
            IndParam::Simple((x, t)) => {
                // f <- (f x)
                f = CoreExp::App {
                    func: Box::new(f),
                    arg: Box::new(CoreExp::Var(x.clone())),
                };
                // (x: t) => foobar
                bindstack.push((x.clone(), t.clone()));
            }
            IndParam::StrictPositive { pre: xts, args: m } => {
                // new variable p
                let p = Var::new("p");
                // f <- (f p ((x[]: t[]) -> q m[] (p x[])))
                {
                    // (x[]: t[]) -> q m[] (p x[])
                    let r = {
                        let r = CoreExp::App {
                            func: Box::new(utils::assoc_apply(ff.clone(), m.clone())), // q m[]
                            arg: Box::new(utils::assoc_apply(
                                CoreExp::Var(p.clone()),
                                xts.iter().map(|(x, _)| CoreExp::Var(x.clone())).collect(),
                            )), // (p x[])
                        };
                        utils::assoc_prod(xts.clone(), r) // (x[]: t[]) -> ...
                    };
                    f = CoreExp::App {
                        func: Box::new(f),
                        arg: Box::new(CoreExp::App {
                            func: Box::new(CoreExp::Var(p.clone())),
                            arg: Box::new(r),
                        }),
                    };
                }
                // push (p: (x[]: t[]) -> THIS m[])
                {
                    // (x[]: t[]) -> THIS m[]
                    let r = {
                        let r = utils::assoc_apply(this.clone(), m.clone()); // THIS m[]
                        utils::assoc_prod(xts.clone(), r) // (x[]: t[]) -> THIS m[]
                    };
                    bindstack.push((p, r));
                }
            }
        }
    }
    // finally, wrap with all the bindings
    utils::assoc_lam(bindstack, f)
}

// (simple) check well-formedness of elim and reduce
/*
- Elim(C_i m[], q, f[]) where C_i is i-th constructor of inductive type I
- => recursor(C_i, ff, f[i]) m[]
- where ff = (x[]: a[]) => (c: (Type x[])) => Elim(Type, c, q, f[])
- where Type I has arity (x[]: a[]) -> s
*/
pub fn inductive_type_elim_reduce(e: &CoreExp) -> Result<CoreExp, String> {
    // A. check well-formedness
    // 1. check e is of form IndTypeElim(IndTypeCst(...), ... )
    let CoreExp::IndTypeElim {
        ty,
        elim,
        return_type: q,
        cases: f,
    } = e
    else {
        return Err("Not an InductiveTypeElim".to_string());
    };
    let CoreExp::IndTypeCst {
        ty: ty2,
        idx,
        parameter,
        args: m,
    } = elim.as_ref()
    else {
        return Err("Elim is not an InductiveTypeCst".to_string());
    };
    // 2. check whether ty is same as ty2
    if !std::rc::Rc::ptr_eq(ty, ty2) {
        return Err("Elim type mismatch".to_string());
    }
    // 3. check constructor is exists
    if *idx >= ty.constructor_len() {
        return Err("Constructor index out of bounds".to_string());
    }
    // 4. check number of arg is correct
    if parameter.len() != ty.param_args_len() {
        return Err("Constructor (parameter) arguments length mismatch".to_string());
    }
    if m.len() != ty.arg_len_cst(*idx) {
        return Err("Constructor (constructor specific) arguments length mismatch".to_string());
    }
    // 5. check cases length
    if f.len() != ty.constructor_len() {
        return Err("Cases length mismatch".to_string());
    }
    // B. reduce
    // new variable
    // ff = (x[]: a[]) => (c: (Type x[])) => Elim(Type, c, q, f[])
    let ff = {
        let c = Var::new("c");
        // we use same "string" but different as variable
        let arities: Vec<(Var, CoreExp)> = ty
            .arity
            .iter()
            .map(|(x, t)| (Var::new(x.name()), t.clone()))
            .collect();

        // Elim(Type, c, q, f[])
        let body = CoreExp::IndTypeElim {
            ty: ty.clone(),
            elim: Box::new(CoreExp::Var(c.clone())),
            return_type: q.clone(),
            cases: f.clone(),
        };

        // (c: (Type x[])) => Elim(Type, c, q, f[]) where x[] are in variables in arities
        let t = CoreExp::IndType {
            ty: ty.clone(),
            parameters: parameter.clone(),
            index: arities
                .iter()
                .map(|(x, _)| CoreExp::Var(x.clone()))
                .collect(),
            // x[] are in variables in arities
        };
        let body = CoreExp::Lam {
            var: c.clone(),
            ty: Box::new(t),
            body: Box::new(body),
        };

        // (x[]: a[]) => (c: (Type x[])) => Elim(Type, c, q, f[])
        utils::assoc_lam(arities, body)
    };
    // type should be curried (i.e. I can be considered as a function (params => arity => I param arity)))
    let this = utils::assoc_lam(
        ty.parameter.clone(),
        utils::assoc_lam(
            ty.arity.clone(),
            CoreExp::IndType {
                ty: ty.clone(),
                parameters: parameter.clone(),
                index: m.clone(),
            },
        ),
    );

    Ok(recursor(&ty.constructors[*idx], &ff, &f[*idx], &this))
}
