use std::rc::Rc;

use crate::{
    derivation::{check, infer_sort},
    utils,
};

use super::exp::*;

// specifications of inductive type
/*
Inductive NAME (parameters.var[]: parameters.ty[]): (indices.var[]: indices.ty[]) -> sort := list of
| constructor[] = [{telescope1[] -> NAME indices1[]}]
*/
#[derive(Debug, Clone)]
pub struct InductiveTypeSpecs {
    // context of definition
    pub ctx: Context,
    // type parameters
    pub parameters: Vec<(Var, Exp)>,
    // indices of the type
    pub indices: Vec<(Var, Exp)>,
    // sort of the type
    pub sort: Sort,
    // constructors
    pub constructors: Vec<CtorType>,
}

impl InductiveTypeSpecs {
    // arity = (indices.var[]: indices.ty[]) -> sort
    pub fn arity(&self) -> Exp {
        utils::assoc_prod(self.indices.clone(), Exp::Sort(self.sort))
    }
    // number of constructors
    pub fn constructor_len(&self) -> usize {
        self.constructors.len()
    }
    // number of parameters
    pub fn param_args_len(&self) -> usize {
        self.parameters.len()
    }
    // number of indices of the idx-th constructor
    pub fn arg_len_cst(&self, idx: usize) -> usize {
        self.constructors[idx].indices.len()
    }
    // type of constructor C_i with given parameters
    pub fn type_of_constructor(indty: &std::rc::Rc<Self>, idx: usize, parameters: Vec<Exp>) -> Exp {
        indty.constructors[idx].as_exp_with_type(&Exp::IndType {
            indty: indty.clone(),
            parameters,
        })
    }
    // (x[]: t[]) -> THIS x[] -> sort
    pub fn return_type_kind(indty: &std::rc::Rc<Self>, parameters: Vec<Exp>, sort: Sort) -> Exp {
        // THIS x[] where x[] is ty.arity_arg's variables
        let e = utils::assoc_apply(
            Exp::IndType {
                indty: indty.clone(),
                parameters: parameters.clone(),
            },
            indty
                .indices
                .iter()
                .map(|(x, _)| Exp::Var(x.clone()))
                .collect(),
        );
        utils::assoc_prod(
            indty.indices.clone(),
            Exp::Prod {
                var: Var::new("_"),
                ty: Box::new(e),
                body: Box::new(Exp::Sort(sort)),
            },
        )
    }
}

/*
constructor of type (telescope[0] -> ... -> telescope[n] -> THIS indices[0] ... indices[m])
*/
#[derive(Debug, Clone)]
pub struct CtorType {
    // binders
    pub telescope: Vec<CtorBinder>,
    // indices of type
    pub indices: Vec<Exp>,
}

#[derive(Debug, Clone)]
pub enum CtorBinder {
    // recursive case
    // (_: {(x[]: t[]) -> THIS m[]}) where THIS should be the inductive type itself
    StrictPositive {
        binders: Vec<(Var, Exp)>, // x[]: t[]
        self_indices: Vec<Exp>,   // m[]
    },
    // nonrecursive case
    // (x: t)
    Simple((Var, Exp)),
}

impl CtorType {
    // subst "THIS" in args with the given type and return as CoreExp
    pub fn as_exp_with_type(&self, this: &Exp) -> Exp {
        let mut pre_prod_stack = vec![];
        for pos in self.telescope.iter() {
            match pos {
                CtorBinder::StrictPositive {
                    binders: xts,
                    self_indices: m,
                } => {
                    let unused_var = Var::new("_");
                    // ty = (x[]: t[]) -> THIS m[]
                    let ty =
                        utils::assoc_prod(xts.clone(), utils::assoc_apply(this.clone(), m.clone()));
                    // push (_: (x[]: t[]) -> ty m[])
                    pre_prod_stack.push((unused_var, ty));
                }
                CtorBinder::Simple((x, t)) => {
                    let t = t.clone();
                    // push (x: t)
                    pre_prod_stack.push((x.clone(), t));
                }
            }
        }
        utils::assoc_prod(
            pre_prod_stack,
            utils::assoc_apply(this.clone(), self.indices.clone()),
        )
    }
}

// check well-formedness of inductive type specifications
pub fn acceptable_typespecs(
    ctx: Context, // assume well-formed
    params: Vec<(Var, Exp)>,
    arity_arg: Vec<(Var, Exp)>,
    sort: Sort,
    constructors: Vec<CtorType>,
) -> (Vec<Derivation>, Result<InductiveTypeSpecs, String>) {
    // 1. check parameters are well-sorted (parameters can depend on previous parameters)
    // (ctx, parameter.var[..i]: parameter.ty[..i] |- parameter.ty[i] : sort)
    let mut well_derivation = vec![];
    let mut local_context = ctx.clone();
    for (x, a) in params.iter() {
        let derivation = infer_sort(&local_context, a);
        let well_sorted = derivation.node().unwrap().is_success();
        well_derivation.push(derivation);

        if !well_sorted {
            return (
                well_derivation,
                Err("Parameter type is not well-sorted".to_string()),
            );
        }

        local_context = local_context.extend((x.clone(), a.clone()));
    }
    // after this, local_context contains all parameters

    // 2. check arity is well-sorted (arity can depend on parameters and previous arities)
    // arity = arity_arg[] -> sort
    // (ctx, parameters[] |- arity : sort)
    let arity = utils::assoc_prod(arity_arg.clone(), Exp::Sort(sort));
    let derivation = infer_sort(&local_context, &arity);
    let well_sorted = derivation.node().unwrap().is_success();
    well_derivation.push(derivation);

    if !well_sorted {
        return (well_derivation, Err("Arity is not well-sorted".to_string()));
    }

    // 3. check constructors are well-sorted (constructor can depend on parameters and each params)
    // adding (Var("THIS"): arity) to local_context and check each constructor under this context
    let this = Var::new("THIS");
    local_context = local_context.extend((this.clone(), arity.clone()));

    for cst in constructors.iter() {
        // cst_type(constructor as type) = pos[] -> THIS args[0] ... args[m]
        let cst_type = cst.as_exp_with_type(&Exp::Var(this.clone()));
        // check (ctx |- cst_type : sort)
        let derivation = check(&local_context, &cst_type, &Exp::Sort(sort));
        let well_typed = derivation.node().unwrap().is_success();
        well_derivation.push(derivation);

        if !well_typed {
            return (
                well_derivation,
                Err(format!("Constructor {cst:?} is not well-sorted")),
            );
        }
    }

    (
        well_derivation,
        Ok(InductiveTypeSpecs {
            ctx,
            parameters: params,
            indices: arity_arg,
            sort,
            constructors,
        }),
    )
}

// return type of corresponding eliminator case for the given constructor
/*
- elim_type(THIS a[], q, c, THIS) = q a[] c
- simple case: elim_type((x: t) -> n, q, c, THIS)
  - = (x: t) -> elim_type(n, q, c x, THIS)
- strpos case: elim_type(((x[]: t[]) -> THIS m[]) -> n, q, c, THIS)
  - = (p: (x[]: t[]) -> THIS m[])
  - -> (_: (x[]: t[]) -> q m[] (p x[]))
  - -> elim_type(n, (c p), THIS)
*/
pub fn eliminator_type(
    CtorType {
        telescope: poss,
        indices: a,
    }: &CtorType,
    q: &Exp,
    c: &Exp,
    this: &Exp, // this should be the inductive type itself (externaly given)
) -> Exp {
    let mut c = c.clone();

    // c <- q a[0] ... a[m] c
    c = {
        let e = utils::assoc_apply(q.clone(), a.clone());
        Exp::App {
            func: Box::new(e),
            arg: Box::new(c.clone()),
        }
    };

    let mut bindstack = vec![];

    // iterate in reverse order (corresponds to recursion)
    for pos in poss.iter().rev() {
        match pos {
            CtorBinder::Simple((x, t)) => {
                // c <- (c x)
                c = Exp::App {
                    func: Box::new(c),
                    arg: Box::new(Exp::Var(x.clone())),
                };
                // push (x: t)
                bindstack.push((x.clone(), t.clone()));
            }
            CtorBinder::StrictPositive {
                binders: xts,
                self_indices: m,
            } => {
                // new variable p
                let p = Var::new("p");
                // c <- (c p)
                c = Exp::App {
                    func: Box::new(c),
                    arg: Box::new(Exp::Var(p.clone())),
                };
                // push (_: r) where r = (x[]: t[]) -> q m[] (p x[])
                {
                    // r = (x[]: t[]) -> q m[] (p x[]) to push in bindstack (_: r)
                    let r = {
                        // q m[] (p x[])
                        let r = Exp::App {
                            func: Box::new(utils::assoc_apply(q.clone(), m.clone())), // q m[]
                            arg: Box::new(utils::assoc_apply(
                                Exp::Var(p.clone()),
                                xts.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                            )), // (p x[])
                        };

                        // (x[]: t[]) -> q m[] (p x[])
                        utils::assoc_prod(xts.clone(), r)
                    };

                    // push in bindstack
                    bindstack.push((Var::new("_"), r));
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

    bindstack.reverse();
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
pub fn recursor(
    CtorType {
        telescope: poss,
        indices: _, // a[] but not used
    }: &CtorType,
    ff: &Exp,
    f: &Exp,
    this: &Exp, // this should be the inductive type itself (external)
) -> Exp {
    let mut f = f.clone();

    let mut bindstack = vec![];

    for pos in poss.iter().rev() {
        match pos {
            CtorBinder::Simple((x, t)) => {
                // f <- (f x)
                f = Exp::App {
                    func: Box::new(f),
                    arg: Box::new(Exp::Var(x.clone())),
                };
                // push (x: t)
                bindstack.push((x.clone(), t.clone()));
            }
            CtorBinder::StrictPositive {
                binders: xts,
                self_indices: m,
            } => {
                // new variable p
                let p = Var::new("p");
                // f <- (f p ((x[]: t[]) -> q m[] (p x[])))
                {
                    // (x[]: t[]) -> q m[] (p x[])
                    let r = {
                        let r = Exp::App {
                            func: Box::new(utils::assoc_apply(ff.clone(), m.clone())), // q m[]
                            arg: Box::new(utils::assoc_apply(
                                Exp::Var(p.clone()),
                                xts.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                            )), // (p x[])
                        };
                        utils::assoc_prod(xts.clone(), r) // (x[]: t[]) -> ...
                    };
                    f = Exp::App {
                        func: Box::new(f),
                        arg: Box::new(Exp::App {
                            func: Box::new(Exp::Var(p.clone())),
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

    bindstack.reverse();
    utils::assoc_lam(bindstack, f)
}

struct RedexShapeInductiveTypeElim {
    ty: Rc<InductiveTypeSpecs>,
    idx: usize,
    parameter: Vec<Exp>,
    m: Vec<Exp>,
    q: Box<Exp>,
    sort: Sort,
    f: Vec<Exp>,
}

// simple well-formedness check for inductive type eliminator
// check only the shape of the expression
fn indelim_shapecheck(e: &Exp) -> Result<RedexShapeInductiveTypeElim, String> {
    // 1. check e = Elim{ty}(e', q, f[])
    let Exp::IndElim {
        indty: ty,
        elim,
        return_type: q,
        sort,
        cases: f,
    } = e
    else {
        return Err("Not an InductiveTypeElim".to_string());
    };
    // 2. check e' = Ctor{ty2, idx}{parameter[]} m[]
    let (
        Exp::IndCtor {
            indty: ty2,
            idx,
            parameters: parameter,
        },
        m,
    ) = utils::decompose_app_ref(elim.as_ref())
    else {
        return Err("Elim is not an InductiveTypeCst".to_string());
    };

    // 2. check ty == ty2
    if !std::rc::Rc::ptr_eq(ty, ty2) {
        return Err("Elim type mismatch".to_string());
    }

    // 3. check ty.constructor[idx] exists
    if *idx >= ty.constructor_len() {
        return Err("Constructor index out of bounds".to_string());
    }

    // 4. check number of parameter (given to constructor) is match with ty's parameter length
    if parameter.len() != ty.param_args_len() {
        return Err("Constructor (parameter) arguments length mismatch".to_string());
    }

    // 5. check number of arguments (given to constructor) is match with ty's constructor[idx]'s argument length
    if m.len() != ty.arg_len_cst(*idx) {
        return Err("Constructor (constructor specific) arguments length mismatch".to_string());
    }

    // 6. check number of cases is match with ty's constructor length
    if f.len() != ty.constructor_len() {
        return Err("Cases length mismatch".to_string());
    }

    Ok(RedexShapeInductiveTypeElim {
        ty: ty.clone(),
        idx: *idx,
        parameter: parameter.clone(),
        m: m.iter().map(|e| (**e).clone()).collect(),
        q: q.clone(),
        sort: *sort,
        f: f.clone(),
    })
}

/*
- Elim(C_i m[], q, f[]) where C_i is i-th constructor of inductive type THIS
- => recursor(C_i, ff, f[i]) m[]
- where ff = (x[]: a[]) => (c: (THIS x[])) => Elim(THIS, c, q, f[])
- where Type THIS has arity (x[]: a[]) -> s
*/
pub fn inductive_type_elim_reduce(e: &Exp) -> Result<Exp, String> {
    // A. check well-formedness
    let RedexShapeInductiveTypeElim {
        ty,
        idx,
        parameter,
        m,
        q,
        sort,
        f,
    } = indelim_shapecheck(e)?;

    // B. reduce
    // ff = (x[]: a[]) => (c: (THIS x[])) => Elim(THIS, c, q, f[])
    let ff = {
        // new variable "c"
        let c = Var::new("c");
        // Elim(THIS, c, q, f[])
        let body = Exp::IndElim {
            indty: ty.clone(),
            elim: Box::new(Exp::Var(c.clone())),
            return_type: q.clone(),
            sort,
            cases: f.clone(),
        };

        // indices (x[]: a[])
        let indices: Vec<(Var, Exp)> = ty.indices.clone();

        // (c: (THIS x[])) => Elim(Type, c, q, f[]) where x[] are in variables in arities
        let body = Exp::Lam {
            var: c.clone(),
            ty: Box::new(utils::assoc_apply(
                Exp::IndType {
                    indty: ty.clone(),
                    parameters: parameter.clone(),
                },
                indices.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
            )),
            body: Box::new(body),
        };

        // (x[]: a[]) => (c: (Type x[])) => Elim(Type, c, q, f[])
        utils::assoc_lam(indices, body)
    };

    let recursor = recursor(
        &ty.constructors[idx],
        &ff,
        &f[idx],
        &Exp::IndType {
            indty: ty.clone(),
            parameters: parameter.clone(),
        },
    );

    // recursor(C_i, ff, f[i]) m[]
    Ok(utils::assoc_apply(recursor, m))
}
