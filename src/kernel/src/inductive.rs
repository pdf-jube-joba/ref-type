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
/// A validated inductive type specification.
///
/// Its fields are private so values from outside the kernel can only be created
/// through [`InductiveTypeSpecs::new`] or another validating operation.
#[derive(Debug, Clone, Serialize)]
pub struct InductiveTypeSpecs {
    // type parameters
    parameters: Vec<(Var, Exp)>,
    // indices of the type
    indices: Vec<(Var, Exp)>,
    // sort of the type
    sort: Sort,
    // constructors
    constructors: Vec<CtorType>,
}

impl InductiveTypeSpecs {
    pub fn new(
        ctx: &Context,
        parameters: Vec<(Var, Exp)>,
        indices: Vec<(Var, Exp)>,
        sort: Sort,
        constructors: Vec<CtorType>,
    ) -> Result<Self, Box<JudgementError>> {
        let specs = Self {
            parameters,
            indices,
            sort,
            constructors,
        };
        specs.validate(ctx)?;
        Ok(specs)
    }

    pub fn parameters(&self) -> &[(Var, Exp)] {
        &self.parameters
    }

    pub fn indices(&self) -> &[(Var, Exp)] {
        &self.indices
    }

    pub fn sort(&self) -> Sort {
        self.sort
    }

    pub fn constructors(&self) -> &[CtorType] {
        &self.constructors
    }

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
    // number of arguments of the idx-th constructor
    pub fn arg_len_cst(&self, idx: usize) -> usize {
        self.constructors[idx].telescope.len()
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
        let subst_mapping = indspec.parameter_subst_mapping(&parameters);
        let indices = indspec
            .indices
            .iter()
            .map(|(x, t)| (x.clone(), t.subst(&subst_mapping)))
            .collect::<Vec<_>>();
        // THIS x[] where x[] is ty.arity_arg's variables
        let e = utils::assoc_apply(
            Exp::IndType {
                indspec: indspec.clone(),
                parameters: parameters.clone(),
            },
            indices.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
        );
        utils::assoc_prod(
            indices,
            Exp::Prod {
                var: Var::new("_"),
                ty: Box::new(e),
                body: Box::new(Exp::Sort(sort)),
            },
        )
    }

    fn validate(&self, ctx: &Context) -> Result<(), Box<JudgementError>> {
        let span = tracing::debug_span!(
            target: "ref_type::typing",
            "construct_inductive_type_specs",
            ctx_len = ctx.len(),
        );
        let _entered = span.enter();

        let mut local_context = ctx.clone();
        for (x, parameter_ty) in &self.parameters {
            infer_sort(&local_context, parameter_ty).map_err(|error| {
                Box::new(error.with_frame(
                    "InductiveTypeSpecs::new",
                    format!("parameter '{:?}' type check", x),
                    "parameter is well-sorted",
                ))
            })?;
            local_context = ctx_extend(&local_context, (x.clone(), parameter_ty.clone()));
        }

        let arity = self.arity();
        infer_sort(&local_context, &arity).map_err(|error| {
            Box::new(error.with_frame(
                "InductiveTypeSpecs::new",
                "arity type check",
                "arity is well-sorted",
            ))
        })?;

        let this = Var::new("THIS");
        local_context = ctx_extend(&local_context, (this.clone(), arity));
        for (index, constructor) in self.constructors.iter().enumerate() {
            let constructor_ty = constructor.as_exp_with_type(&Exp::Var(this.clone()));
            check(&local_context, &constructor_ty, &Exp::Sort(self.sort)).map_err(|error| {
                Box::new(error.with_frame(
                    "InductiveTypeSpecs::new",
                    format!("constructor '{}' type check", index),
                    "constructor is well-sorted",
                ))
            })?;
        }

        tracing::debug!(target: "ref_type::typing", outcome = "success");
        Ok(())
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

    pub fn subst(&self, subst_mapping: &[(Var, Exp)]) -> CtorType {
        CtorType {
            telescope: self
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
            indices: self
                .indices
                .iter()
                .map(|t| t.subst(subst_mapping))
                .collect(),
        }
    }
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
                        utils::assoc_lam(xts.clone(), r) // (x[]: t[]) => q m[] (p x[])
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
    let subst_mapping = ty.parameter_subst_mapping(&parameter);
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
        let indices: Vec<(Var, Exp)> = ty
            .indices
            .iter()
            .map(|(x, t)| (x.clone(), t.subst(&subst_mapping)))
            .collect();

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
        &ty.constructors[idx].subst(&subst_mapping),
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
    pub(crate) fn parameter_subst_mapping(&self, parameters: &[Exp]) -> Vec<(Var, Exp)> {
        self.parameters
            .iter()
            .zip(parameters.iter())
            .map(|((v, _), e)| (v.clone(), e.clone()))
            .collect()
    }

    /// Apply a substitution and validate the resulting specification in `ctx`.
    pub fn instantiate(
        &self,
        ctx: &Context,
        subst_mapping: &[(Var, Exp)],
    ) -> Result<InductiveTypeSpecs, Box<JudgementError>> {
        InductiveTypeSpecs::new(
            ctx,
            self.parameters
                .iter()
                .map(|(x, t)| (x.clone(), t.subst(subst_mapping)))
                .collect(),
            self.indices
                .iter()
                .map(|(x, t)| (x.clone(), t.subst(subst_mapping)))
                .collect(),
            self.sort,
            self.constructors
                .iter()
                .map(|cst| cst.subst(subst_mapping))
                .collect(),
        )
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
        let subst_mapping = indspec.parameter_subst_mapping(&parameters);

        // f_i: eliminator_type(C_i, q, type of constructor of C_i, THIS) for each constructor C_i
        let mut cases = vec![];
        for i in 0..indspec.constructor_len() {
            let f_i = Var::new(&format!("f{}", i));
            let ctor = indspec.constructors[i].subst(&subst_mapping);
            let f_i_ty = eliminator_type(
                &ctor,
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
        let indices = indspec
            .indices
            .iter()
            .map(|(x, t)| (x.clone(), t.subst(&subst_mapping)))
            .collect::<Vec<_>>();
        let c_ty = utils::assoc_apply(
            Exp::IndType {
                indspec: indspec.clone(),
                parameters: parameters.clone(),
            },
            indices.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
        );
        telescope.extend(indices);
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
    use crate::calculus::{exp_contains_as_freevar, exp_is_alpha_eq, normalize};
    use crate::{app, lam, var};

    fn specs(
        parameters: Vec<(Var, Exp)>,
        indices: Vec<(Var, Exp)>,
        sort: Sort,
        constructors: Vec<CtorType>,
    ) -> InductiveTypeSpecs {
        InductiveTypeSpecs::new(&Context::new(), parameters, indices, sort, constructors).unwrap()
    }

    fn nat_specs() -> Rc<InductiveTypeSpecs> {
        Rc::new(specs(
            vec![],
            vec![],
            Sort::Set(0),
            vec![
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
        ))
    }

    #[test]
    fn construction_rejects_an_ill_sorted_parameter() {
        let result = InductiveTypeSpecs::new(
            &Context::new(),
            vec![(Var::new("A"), Exp::Var(Var::new("missing")))],
            vec![],
            Sort::Set(0),
            vec![],
        );

        assert!(result.is_err());
    }

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
            println!("Eliminator type (trivial): {e:?}");
            let r = recursor(&ctor, &q, &c, &this);
            println!("Recursor (trivial): {r:?}");
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
            println!("Eliminator type (trivial): {e:?}");
            let r = recursor(&ctor, &q, &c, &this);
            println!("Recursor (trivial): {r:?}");
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
            println!("Eliminator type (trivial): {e:?}");
            let r = recursor(&ctor, &q, &c, &this);
            println!("Recursor (trivial): {r:?}");
        }
    }

    #[test]
    fn constructor_argument_redex_reduces() {
        let specs = nat_specs();

        let nat = Exp::IndType {
            indspec: specs.clone(),
            parameters: vec![],
        };
        let zero = Exp::IndCtor {
            indspec: specs.clone(),
            parameters: vec![],
            idx: 0,
        };
        let succ = Exp::IndCtor {
            indspec: specs.clone(),
            parameters: vec![],
            idx: 1,
        };
        let n = var!("n");
        let ih = var!("ih");
        let motive = lam!(n.clone(), nat.clone(), nat.clone());
        let succ_case = lam!(
            n,
            nat.clone(),
            lam!(
                ih.clone(),
                nat.clone(),
                app!(func: succ.clone(), arg: Exp::Var(ih))
            )
        );

        let redex = Exp::IndElim {
            indspec: specs.clone(),
            elim: Box::new(app!(func: succ.clone(), arg: zero.clone())),
            return_type: Box::new(motive),
            cases: vec![zero.clone(), succ_case],
        };

        let expected = app!(func: succ, arg: zero);
        assert!(exp_is_alpha_eq(&normalize(&redex), &expected));
    }

    #[test]
    fn strict_positive_ih_is_lambda_term() {
        let a = var!("A");
        let x = var!("x");
        let p = Var::new("p");
        let q = Exp::Var(var!("q"));
        let f = Exp::Var(var!("f"));
        let this = Exp::Var(var!("THIS"));
        let ctor = CtorType {
            telescope: vec![CtorBinder::StrictPositive {
                binders: vec![(x.clone(), Exp::Var(a))],
                self_indices: vec![],
            }],
            indices: vec![],
        };

        let rec = recursor(&ctor, &q, &f, &this);
        let Exp::Lam { body, .. } = rec else {
            panic!("expected recursive argument lambda");
        };
        let Exp::App { arg: ih_arg, .. } = body.as_ref() else {
            panic!("expected case function application");
        };
        assert!(matches!(ih_arg.as_ref(), Exp::Lam { .. }));

        // keep the generated binder live enough to guard against accidental dummy changes
        assert!(!exp_contains_as_freevar(ih_arg, &p));
    }

    #[test]
    fn primitive_recursion_substitutes_parameters() {
        let a = Var::new("A");
        let b = Var::new("B");
        let specs = Rc::new(specs(
            vec![(a.clone(), Exp::Sort(Sort::Set(0)))],
            vec![],
            Sort::Set(0),
            vec![CtorType {
                telescope: vec![CtorBinder::Simple((Var::new("head"), Exp::Var(a.clone())))],
                indices: vec![],
            }],
        ));

        let rec = InductiveTypeSpecs::primitive_recursion(
            &specs,
            vec![Exp::Var(b.clone())],
            Sort::Set(0),
        );

        assert!(!exp_contains_as_freevar(&rec, &a));
        assert!(exp_contains_as_freevar(&rec, &b));
    }

    #[test]
    fn primitive_recursion_binds_indices() {
        let a = Var::new("A");
        let b = Var::new("B");
        let i = Var::new("i");
        let x = Var::new("x");
        let specs = Rc::new(specs(
            vec![(a.clone(), Exp::Sort(Sort::Set(0)))],
            vec![(i.clone(), Exp::Var(a.clone()))],
            Sort::Set(0),
            vec![CtorType {
                telescope: vec![CtorBinder::Simple((x.clone(), Exp::Var(a.clone())))],
                indices: vec![Exp::Var(x)],
            }],
        ));

        let rec = InductiveTypeSpecs::primitive_recursion(
            &specs,
            vec![Exp::Var(b.clone())],
            Sort::Set(0),
        );

        assert!(!exp_contains_as_freevar(&rec, &a));
        assert!(!exp_contains_as_freevar(&rec, &i));
        assert!(exp_contains_as_freevar(&rec, &b));
    }

    #[test]
    fn test_by_unit_inductive() {
        let specs = specs(
            vec![],
            vec![],
            Sort::Set(0),
            vec![CtorType {
                telescope: vec![],
                indices: vec![],
            }],
        );
        let specs = Rc::new(specs);
        let prin_rec = InductiveTypeSpecs::primitive_recursion(&specs, vec![], Sort::Set(0));
        println!("Primitive recursion principle for Unit type: {prin_rec:?}");
    }
    #[test]
    fn test_by_bool_inductive() {
        let specs = specs(
            vec![],
            vec![],
            Sort::Set(0),
            vec![
                CtorType {
                    telescope: vec![],
                    indices: vec![],
                },
                CtorType {
                    telescope: vec![],
                    indices: vec![],
                },
            ],
        );
        let specs = Rc::new(specs);
        let prin_rec = InductiveTypeSpecs::primitive_recursion(&specs, vec![], Sort::Set(0));
        println!("Primitive recursion principle for Bool type: {prin_rec:?}");
    }
    #[test]
    fn test_by_natural_number_inductive() {
        let specs = specs(
            vec![],
            vec![],
            Sort::Set(0),
            vec![
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
        );
        let specs = Rc::new(specs);
        let prin_rec = InductiveTypeSpecs::primitive_recursion(&specs, vec![], Sort::Set(0));
        println!("Primitive recursion principle for Nat type: {prin_rec:?}");
    }
    #[test]
    fn test_by_polymorphic_list_inductive() {
        let a = Var::new("A");
        let specs = specs(
            vec![(a.clone(), Exp::Sort(Sort::Set(0)))],
            vec![],
            Sort::Set(0),
            vec![
                // nil: List[A]
                CtorType {
                    telescope: vec![],
                    indices: vec![],
                },
                // cons: (head: A) -> (tail: List[A]) -> List[A]
                CtorType {
                    telescope: vec![
                        CtorBinder::Simple((Var::new("head"), Exp::Var(a.clone()))),
                        CtorBinder::StrictPositive {
                            binders: vec![],
                            self_indices: vec![],
                        },
                    ],
                    indices: vec![],
                },
            ],
        );
        let specs = Rc::new(specs);
        let prin_rec = InductiveTypeSpecs::primitive_recursion(
            &specs,
            vec![Exp::Var(a.clone())],
            Sort::Set(0),
        );
        println!("Primitive recursion principle for List type: {prin_rec:?}");
    }
}
