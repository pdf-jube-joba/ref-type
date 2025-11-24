use std::rc::Rc;

use serde::Serialize;

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
#[derive(Debug, Clone, Serialize)]
pub struct InductiveTypeSpecs {
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
    pub fn type_of_constructor(
        indspec: &std::rc::Rc<Self>,
        idx: usize,
        parameters: Vec<Exp>,
    ) -> Exp {
        indspec.constructors[idx].as_exp_with_type(&Exp::IndType {
            indspec: indspec.clone(),
            parameters,
        })
    }
    // (x[]: t[]) -> THIS x[] -> sort
    pub fn return_type_kind(indspec: &std::rc::Rc<Self>, parameters: Vec<Exp>, sort: Sort) -> Exp {
        // THIS x[] where x[] is ty.arity_arg's variables
        let e = utils::assoc_apply(
            Exp::IndType {
                indspec: indspec.clone(),
                parameters: parameters.clone(),
            },
            indspec
                .indices
                .iter()
                .map(|(x, _)| Exp::Var(x.clone()))
                .collect(),
        );
        utils::assoc_prod(
            indspec.indices.clone(),
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
#[derive(Debug, Clone, Serialize)]
pub struct CtorType {
    // binders
    pub telescope: Vec<CtorBinder>,
    // indices of type
    pub indices: Vec<Exp>,
}

#[derive(Debug, Clone, Serialize)]
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
    ctx: &Context, // assume well-formed
    inductive_type_specs: &InductiveTypeSpecs,
) -> Result<DerivationSuccess, DerivationFail> {
    let rc = Rc::new(inductive_type_specs.clone());
    let InductiveTypeSpecs {
        parameters,
        indices,
        sort,
        constructors,
    } = inductive_type_specs;
    // 1. check parameters are well-sorted (parameters can depend on previous parameters)
    // (ctx, parameter.var[..i]: parameter.ty[..i] |- parameter.ty[i] : sort)
    let mut well_derivation = vec![];
    let mut local_context = ctx.clone();
    for (x, a) in parameters.iter() {
        let derivation = infer_sort(&local_context, a);

        match derivation {
            Ok(ok) => {
                well_derivation.push(ok);
            }
            Err(err) => {
                let err_der = DerivationFail {
                    base: DerivationBase {
                        premises: well_derivation.clone(),
                        rule: "inductive type well formed".to_string(),
                        phase: format!("parameter '{}' type check", x),
                    },
                    head: FailHead::WellFormednessInductive {
                        ctx: ctx.clone(),
                        indspec: rc.clone(),
                    },
                    kind: FailKind::Propagate {
                        fail: Box::new(err),
                        expect: "Parameter is well-sorted".to_string(),
                    },
                };
                return Err(err_der);
            }
        }

        local_context = ctx_extend(&local_context, (x.clone(), a.clone()));
    }
    // after this, local_context contains all parameters

    // 2. check arity is well-sorted (arity can depend on parameters and previous arities)
    // arity = indices[] -> sort
    // (ctx, parameters[] |- arity : sort)
    let arity = utils::assoc_prod(indices.clone(), Exp::Sort(*sort));
    let derivation = infer_sort(&local_context, &arity);
    match derivation {
        Ok(ok) => {
            well_derivation.push(ok);
        }
        Err(err) => {
            let err_der = DerivationFail {
                base: DerivationBase {
                    premises: well_derivation.clone(),
                    rule: "inductive type well formed".to_string(),
                    phase: "arity type check".to_string(),
                },
                head: FailHead::WellFormednessInductive {
                    ctx: ctx.clone(),
                    indspec: rc.clone(),
                },
                kind: FailKind::Propagate {
                    fail: Box::new(err),
                    expect: "Arity is well-sorted".to_string(),
                },
            };
            return Err(err_der);
        }
    }

    // 3. check constructors are well-sorted (constructor can depend on parameters and each params)
    // adding (Var("THIS"): arity) to local_context and check each constructor under this context
    let this = Var::new("THIS");
    local_context = ctx_extend(&local_context, (this.clone(), arity.clone()));

    for (i, ctor) in constructors.iter().enumerate() {
        // cst_type(constructor as type) = pos[] -> THIS args[0] ... args[m]
        let cst_type = ctor.as_exp_with_type(&Exp::Var(this.clone()));
        // check (ctx |- cst_type : sort)
        let derivation = check(&local_context, &cst_type, &Exp::Sort(*sort));
        match derivation {
            Ok(ok) => {
                well_derivation.push(ok);
            }
            Err(err) => {
                let err_der = DerivationFail {
                    base: DerivationBase {
                        premises: well_derivation.clone(),
                        rule: "inductive type well formed".to_string(),
                        phase: format!("constructor '{}' type check", i),
                    },
                    head: FailHead::WellFormednessInductive {
                        ctx: ctx.clone(),
                        indspec: rc.clone(),
                    },
                    kind: FailKind::Propagate {
                        fail: Box::new(err),
                        expect: "Constructor is well-sorted".to_string(),
                    },
                };
                return Err(err_der);
            }
        }
    }
    // all checks passed
    let ok: DerivationSuccess = DerivationSuccess {
        head: SuccessHead::WellFormednessInductive {
            ctx: ctx.clone(),
            indspec: rc,
        },
        base: DerivationBase {
            premises: well_derivation,
            rule: "inductive type well formed".to_string(),
            phase: "complete".to_string(),
        },
        generated_goals: vec![],
        through: false,
    };
    Ok(ok)
}

// return type of corresponding eliminator case for the given constructor
/*
- elim_type(THIS a[], q, c, THIS) = q a[] c
- simple case: elim_type((x: t) -> n, q, c, THIS)
  - = (x: t) -> elim_type(n, q, c x, THIS)
- strpos case: elim_type(((x[]: t[]) -> THIS m[]) -> n, q, c, THIS)
  - = (p: (x[]: t[]) -> THIS m[])
  - -> (_: (x[]: t[]) -> q m[] (p x[]))
  - -> elim_type(n, q, (c p), THIS)
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
    let mut bindstack = vec![];
    let mut c = c.clone();

    for pos in poss.iter() {
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
                // push (p: (x[]: t[]) -> THIS m[])
                {
                    // (x[]: t[]) -> THIS m[]
                    let r = {
                        let r = utils::assoc_apply(this.clone(), m.clone()); // THIS m[]
                        utils::assoc_prod(xts.clone(), r) // (x[]: t[]) -> THIS m[]
                    };
                    bindstack.push((p.clone(), r));
                }
                // push (_: r) where r = (x[]: t[]) -> q m[] (p x[])
                {
                    // r = (x[]: t[]) -> q m[] (p x[]) to push in bindstack (_: r)
                    let r = {
                        let pxs = utils::assoc_apply(
                            Exp::Var(p.clone()),
                            xts.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                        ); // (p x[])
                        let qms = utils::assoc_apply(q.clone(), m.clone()); // q m[]

                        let right = Exp::App {
                            func: Box::new(qms), // q m[]
                            arg: Box::new(pxs),  // (p x[])
                        };

                        // (x[]: t[]) -> q m[] (p x[])
                        utils::assoc_prod(xts.clone(), right)
                    };

                    // push in bindstack
                    bindstack.push((Var::new("_"), r));
                }
            }
        }
    }

    // c <- q a[0] ... a[m] c
    c = {
        let e = utils::assoc_apply(q.clone(), a.clone());
        Exp::App {
            func: Box::new(e),
            arg: Box::new(c.clone()),
        }
    };

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
    q: &Exp,
    f: &Exp,
    this: &Exp, // this should be the inductive type itself (external)
) -> Exp {
    let mut f = f.clone();

    let mut bindstack = vec![];

    for pos in poss.iter() {
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
                    let right = {
                        let pxs = utils::assoc_apply(
                            Exp::Var(p.clone()),
                            xts.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                        ); // (p x[])
                        let qms = utils::assoc_apply(q.clone(), m.clone()); // q m[]
                        let r = Exp::App {
                            func: Box::new(qms),
                            arg: Box::new(pxs),
                        }; // q m[] (p x[])
                        utils::assoc_prod(xts.clone(), r) // (x[]: t[]) -> q m[] (p x[])
                    };
                    f = Exp::App {
                        func: Box::new(Exp::App {
                            func: Box::new(f.clone()),
                            arg: Box::new(Exp::Var(p.clone())),
                        }),
                        arg: Box::new(right),
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

    utils::assoc_lam(bindstack, f)
}

struct RedexShapeInductiveTypeElim {
    ty: Rc<InductiveTypeSpecs>,
    idx: usize,
    parameter: Vec<Exp>,
    m: Vec<Exp>,
    q: Box<Exp>,
    f: Vec<Exp>,
}

// simple well-formedness check for inductive type eliminator
// check only the shape of the expression
fn indelim_shapecheck(e: &Exp) -> Result<RedexShapeInductiveTypeElim, String> {
    // 1. check e = Elim{ty}(e', q, f[])
    let Exp::IndElim {
        indspec,
        elim,
        return_type: q,
        cases: f,
    } = e
    else {
        return Err("Not an InductiveTypeElim".to_string());
    };
    // 2. check e' = Ctor{ty2, idx}{parameter[]} m[]
    let (
        Exp::IndCtor {
            indspec: indspec2,
            idx,
            parameters: parameter,
        },
        m,
    ) = utils::decompose_app_ref(elim.as_ref())
    else {
        return Err("Elim is not an InductiveTypeCst".to_string());
    };

    // 2. check ty == ty2
    if !std::rc::Rc::ptr_eq(indspec, indspec2) {
        return Err("Elim type mismatch".to_string());
    }

    // 3. check ty.constructor[idx] exists
    if *idx >= indspec.constructor_len() {
        return Err("Constructor index out of bounds".to_string());
    }

    // 4. check number of parameter (given to constructor) is match with ty's parameter length
    if parameter.len() != indspec.param_args_len() {
        return Err("Constructor (parameter) arguments length mismatch".to_string());
    }

    // 5. check number of arguments (given to constructor) is match with ty's constructor[idx]'s argument length
    if m.len() != indspec.arg_len_cst(*idx) {
        return Err("Constructor (constructor specific) arguments length mismatch".to_string());
    }

    // 6. check number of cases is match with ty's constructor length
    if f.len() != indspec.constructor_len() {
        return Err("Cases length mismatch".to_string());
    }

    Ok(RedexShapeInductiveTypeElim {
        ty: indspec.clone(),
        idx: *idx,
        parameter: parameter.clone(),
        m: m.iter().map(|e| (**e).clone()).collect(),
        q: q.clone(),
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
        f,
    } = indelim_shapecheck(e)?;

    // B. reduce
    // ff = (x[]: a[]) => (c: (THIS x[])) => Elim(THIS, c, q, f[])
    let ff = {
        // new variable "c"
        let c = Var::new("c");
        // Elim(THIS, c, q, f[])
        let body = Exp::IndElim {
            indspec: ty.clone(),
            elim: Box::new(Exp::Var(c.clone())),
            return_type: q.clone(),
            cases: f.clone(),
        };

        // indices (x[]: a[])
        let indices: Vec<(Var, Exp)> = ty.indices.clone();

        // (c: (THIS x[])) => Elim(Type, c, q, f[]) where x[] are in variables in arities
        let body = Exp::Lam {
            var: c.clone(),
            ty: Box::new(utils::assoc_apply(
                Exp::IndType {
                    indspec: ty.clone(),
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
            indspec: ty.clone(),
            parameters: parameter.clone(),
        },
    );

    // recursor(C_i, ff, f[i]) m[]
    Ok(utils::assoc_apply(recursor, m))
}

impl InductiveTypeSpecs {
    pub fn subst(&self, subst_mapping: &[(Var, Exp)]) -> InductiveTypeSpecs {
        InductiveTypeSpecs {
            parameters: self
                .parameters
                .iter()
                .map(|(x, t)| (x.clone(), t.subst(subst_mapping)))
                .collect(),
            indices: self
                .indices
                .iter()
                .map(|(x, t)| (x.clone(), t.subst(subst_mapping)))
                .collect(),
            sort: self.sort,
            constructors: self
                .constructors
                .iter()
                .map(|cst| CtorType {
                    telescope: cst
                        .telescope
                        .iter()
                        .map(|binder| match binder {
                            CtorBinder::StrictPositive {
                                binders: xts,
                                self_indices: m,
                            } => CtorBinder::StrictPositive {
                                binders: xts
                                    .iter()
                                    .map(|(x, t)| (x.clone(), t.subst(subst_mapping)))
                                    .collect(),
                                self_indices: m.iter().map(|t| t.subst(subst_mapping)).collect(),
                            },
                            CtorBinder::Simple((x, t)) => {
                                CtorBinder::Simple((x.clone(), t.subst(subst_mapping)))
                            }
                        })
                        .collect(),
                    indices: cst.indices.iter().map(|t| t.subst(subst_mapping)).collect(),
                })
                .collect(),
        }
    }
    // generate primitive recursion principle for this inductive type
    // return (q: (x[]: t[]) -> THIS x[] -> sort) => (f[0]: _) => ... => (f[n]: _) => (x[]: t[]) => (c: q x[]) => elim(THIS, c, q, f[])
    // which has type of
    // (q: (x[]: t[]) -> THIS x[] -> sort) -> (f[0]: _) -> ... -> (f[n]: _) -> (x[]: t[]) -> (c: THIS x[]) -> q x[] c ... this is type of induction
    pub fn primitive_recursion(
        indspec: &std::rc::Rc<Self>,
        parameters: Vec<Exp>,
        sort: Sort,
    ) -> Exp {
        let this = Exp::IndType {
            indspec: indspec.clone(),
            parameters: parameters.clone(),
        };

        let mut telescope = vec![];

        // q: (x[]: t[]) -> THIS x[] -> sort
        let q = Var::new("q");
        let q_ty = InductiveTypeSpecs::return_type_kind(indspec, parameters.clone(), sort);
        telescope.push((q.clone(), q_ty));

        // f_i: eliminator_type(C_i, q, type of constructor of C_i, THIS) for each constructor C_i
        let mut cases = vec![];
        for i in 0..indspec.constructor_len() {
            let f_i = Var::new(&format!("f{}", i));
            let ctor = &indspec.constructors[i];
            let f_i_ty = eliminator_type(
                ctor,
                &Exp::Var(q.clone()),
                &Exp::IndCtor {
                    indspec: indspec.clone(),
                    parameters: parameters.clone(),
                    idx: i,
                },
                &this,
            );
            telescope.push((f_i.clone(), f_i_ty));
            cases.push(Exp::Var(f_i));
        }

        let c = Var::new("c");
        let c_ty = utils::assoc_apply(
            Exp::IndType {
                indspec: indspec.clone(),
                parameters: parameters.clone(),
            },
            indspec
                .indices
                .iter()
                .map(|(x, _)| Exp::Var(x.clone()))
                .collect(),
        );
        telescope.push((c.clone(), c_ty));

        // elim(THIS, c, q, f[])
        let body = Exp::IndElim {
            indspec: indspec.clone(),
            elim: Box::new(Exp::Var(c.clone())),
            return_type: Box::new(Exp::Var(q.clone())),
            cases,
        };

        utils::assoc_lam(telescope, body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_constructor() {
        let q = Exp::Var(Var::new("q"));
        let c = Exp::Var(Var::new("c"));
        let this = Exp::Var(Var::new("THIS"));
        // trivial case
        {
            // | ctor: THIS
            let ctor = CtorType {
                telescope: vec![],
                indices: vec![],
            };
            let e = eliminator_type(&ctor, &q, &c, &this);
            println!("Eliminator type (trivial): {e}");
            let r = recursor(&ctor, &q, &c, &this);
            println!("Recursor (trivial): {r}");
        }
        // simple case
        {
            // | ctor: A -> THIS
            let another = Var::new("A");
            let ctor = CtorType {
                telescope: vec![CtorBinder::Simple((
                    Var::dummy(),
                    Exp::Var(another.clone()),
                ))],
                indices: vec![],
            };
            let e = eliminator_type(&ctor, &q, &c, &this);
            println!("Eliminator type (trivial): {e}");
            let r = recursor(&ctor, &q, &c, &this);
            println!("Recursor (trivial): {r}");
        }
        // strictly positive case
        {
            // | ctor: (_: THIS) -> THIS
            let ctor = CtorType {
                telescope: vec![CtorBinder::StrictPositive {
                    binders: vec![],
                    self_indices: vec![],
                }],
                indices: vec![],
            };
            let e = eliminator_type(&ctor, &q, &c, &this);
            println!("Eliminator type (trivial): {e}");
            let r = recursor(&ctor, &q, &c, &this);
            println!("Recursor (trivial): {r}");
        }
    }
    #[test]
    fn test_by_unit_inductive() {
        let specs = InductiveTypeSpecs {
            parameters: vec![],
            indices: vec![],
            sort: Sort::Set(0),
            constructors: vec![CtorType {
                telescope: vec![],
                indices: vec![],
            }],
        };
        let _res = acceptable_typespecs(&Context::new(), &specs).unwrap();
        let specs = Rc::new(specs);
        let prin_rec = InductiveTypeSpecs::primitive_recursion(&specs, vec![], Sort::Set(0));
        println!("Primitive recursion principle for Unit type: {prin_rec}");
    }
    #[test]
    fn test_by_bool_inductive() {
        let specs = InductiveTypeSpecs {
            parameters: vec![],
            indices: vec![],
            sort: Sort::Set(0),
            constructors: vec![
                CtorType {
                    telescope: vec![],
                    indices: vec![],
                },
                CtorType {
                    telescope: vec![],
                    indices: vec![],
                },
            ],
        };
        let _res = acceptable_typespecs(&Context::new(), &specs).unwrap();
        let specs = Rc::new(specs);
        let prin_rec = InductiveTypeSpecs::primitive_recursion(&specs, vec![], Sort::Set(0));
        println!("Primitive recursion principle for Bool type: {prin_rec}");
    }
    #[test]
    fn test_by_natural_number_inductive() {
        let specs = InductiveTypeSpecs {
            parameters: vec![],
            indices: vec![],
            sort: Sort::Set(0),
            constructors: vec![
                CtorType {
                    telescope: vec![],
                    indices: vec![],
                },
                CtorType {
                    telescope: vec![CtorBinder::StrictPositive {
                        binders: vec![],
                        self_indices: vec![],
                    }],
                    indices: vec![],
                },
            ],
        };
        let _res = acceptable_typespecs(&Context::new(), &specs).unwrap();
        let specs = Rc::new(specs);
        let prin_rec = InductiveTypeSpecs::primitive_recursion(&specs, vec![], Sort::Set(0));
        println!("Primitive recursion principle for Nat type: {prin_rec}");
    }
}
