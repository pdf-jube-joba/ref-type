use super::calculus::*;
use super::coreexp::*;

struct Builder {
    rule: String,
    meta: Option<String>,
    premises: Vec<Derivation>,
}

impl Builder {
    fn new(rule: String, meta: Option<String>) -> Self {
        Self {
            rule,
            meta,
            premises: vec![],
        }
    }
    fn add(&mut self, premise: Derivation) -> &mut Self {
        self.premises.push(premise);
        self
    }
    fn build(self, judgement: Judgement) -> Derivation {
        Derivation {
            conclusion: judgement,
            premises: self.premises,
            rule: self.rule,
            meta: self.meta,
        }
    }
}

pub fn check(ctx: &Context, term: &CoreExp, ty: &CoreExp) -> Result<Derivation, Derivation> {
    // rule is Conversion, meta is check
    let mut builder = Builder::new("Conversion".to_string(), Some("check".to_string()));

    // 1. Infer the type of the term
    let inferred_ty_result = match infer(ctx, term) {
        Ok((infer_derivation, ty)) => {
            builder.add(infer_derivation);
            ty
        }
        Err(derivation) => {
            builder.add(derivation);
            return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                "Failed to infer type of term {:?}",
                term
            )))));
        }
    };

    // 2. check ty is a well-sorted
    match infer_sort(ctx, ty) {
        Ok((ty_sort_derivation, _sort)) => {
            builder.add(ty_sort_derivation);
        }
        Err(derivation) => {
            return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                "Expected type {:?} is not well-sorted: {:?}",
                ty, derivation
            )))));
        }
    };

    // 3. check ty and inferred_ty_result are convertible
    if convertible(&inferred_ty_result, ty) {
        Ok(builder.build(Judgement::Type(TypeJudge {
            ctx: ctx.clone(),
            term: term.clone(),
            ty: ty.clone(),
        })))
    } else {
        Err(builder.build(Judgement::FailJudge(FailJudge(format!(
            "Type mismatch: inferred type {:?} is not convertible to expected type {:?}",
            inferred_ty_result, ty
        )))))
    }
}

pub fn infer(ctx: &Context, term: &CoreExp) -> Result<(Derivation, CoreExp), Derivation> {
    let judgement_from_ty = |ty: &CoreExp| {
        Judgement::Type(TypeJudge {
            ctx: ctx.clone(),
            term: term.clone(),
            ty: ty.clone(),
        })
    };
    match term {
        CoreExp::Sort(sort) => {
            let builder = Builder::new("Sort".to_string(), Some("infer".to_string()));

            // conclude (ctx |- sort : sort_of_sort) if (sort_of_sort exists)
            match sort.type_of_sort() {
                Some(sort_of_sort) => {
                    let ty = CoreExp::Sort(sort_of_sort);
                    Ok((builder.build(judgement_from_ty(&ty)), ty))
                }
                None => Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "No higher sort for sort {:?}",
                    sort
                ))))),
            }
        }
        CoreExp::Var(index) => {
            let builder = Builder::new("Var".to_string(), Some("infer".to_string()));
            // conclude (ctx |- Var(index) : ctx[index]) if ctx[index] exists
            match ctx.get(*index) {
                Some(ty) => Ok((builder.build(judgement_from_ty(ty)), ty.clone())),
                None => Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Variable at index {} not found in context",
                    index
                ))))),
            }
        }
        CoreExp::Prod { ty, body } => {
            let mut builder = Builder::new("Prod".to_string(), Some("infer".to_string()));
            // 1. infer (ctx |- ty : s1)
            let s1 = match infer_sort(ctx, ty) {
                Ok((ty_sort_derivation, s)) => {
                    builder.add(ty_sort_derivation);
                    s
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        ty
                    )))));
                }
            };
            let extend = ctx.extend(*ty.clone());
            // 2. infer (ctx, ty |= body : s2)
            let s2 = match infer_sort(&extend, body) {
                Ok((body_sort_derivation, s)) => {
                    builder.add(body_sort_derivation);
                    s
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of body {:?}",
                        body
                    )))));
                }
            };
            // 3. check if (s1, s2) can form a product type with sort s3
            let s3 = match s1.relation_of_sort(s2) {
                Some(s3) => s3,
                None => {
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Cannot form product type with domain sort {:?} and codomain sort {:?}",
                        s1, s2
                    )))));
                }
            };
            let ty = CoreExp::Sort(s3);
            // 4. conclude (ctx |- Prod(ty, body) : s3)
            Ok((builder.build(judgement_from_ty(&ty)), ty))
        }
        CoreExp::Lam { ty, body } => {
            let mut builder = Builder::new("Lam".to_string(), Some("infer".to_string()));
            // 1. infer (ctx |- ty : s)
            match infer_sort(ctx, ty) {
                Ok((ty_sort_derivation, _)) => {
                    builder.add(ty_sort_derivation);
                    // we don't need the sort itself here
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        ty
                    )))));
                }
            };
            let extend = ctx.extend(*ty.clone());
            // 2. infer (ctx, ty |- body : body_ty)
            let body_ty = match infer(&extend, body) {
                Ok((derivation, ty)) => {
                    builder.add(derivation);
                    ty
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer type of body {:?}",
                        body
                    )))));
                }
            };
            let lam_ty = CoreExp::Prod {
                ty: ty.clone(),
                body: Box::new(body_ty),
            };
            // 3. conclude (ctx |- Lam(ty, body) : Prod(ty, body_ty))
            Ok((builder.build(judgement_from_ty(&lam_ty)), lam_ty))
        }
        CoreExp::App { func, arg } => {
            let mut builder = Builder::new("App".to_string(), Some("infer".to_string()));
            // 1. infer (ctx |- func : (x: arg_ty) -> ret_ty)
            let func_ty = match infer(ctx, func) {
                Ok((func_derivation, func_ty)) => {
                    builder.add(func_derivation);
                    func_ty
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer type of function {:?}",
                        func
                    )))));
                }
            };
            let CoreExp::Prod {
                ty: arg_ty,
                body: ret_ty,
            } = normalize(&func_ty)
            else {
                return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Function type {:?} is not a product type",
                    func_ty
                )))));
            };
            // 2. check (ctx |- arg : arg_ty)
            match check(ctx, arg, &arg_ty) {
                Ok(arg_check_derivation) => {
                    builder.add(arg_check_derivation);
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check argument {:?} against type {:?}",
                        arg, arg_ty
                    )))));
                }
            };
            let ret_ty_substituted = subst(&ret_ty, arg, 0);
            // 3. conclude (ctx |- App(func, arg) : ret_ty[arg/0])
            Ok((
                builder.build(judgement_from_ty(&ret_ty_substituted)),
                ret_ty_substituted,
            ))
        }
        CoreExp::IndType { ty, args } => todo!(),
        CoreExp::IndTypeCst { ty, idx, args } => todo!(),
        CoreExp::IndTypeElim {
            ty,
            elim,
            return_type,
            cases,
        } => todo!(),
        CoreExp::Cast { exp, to } => {
            let mut builder = Builder::new("Cast".to_string(), Some("infer".to_string()));
            // simply, check (ctx |- exp : to)
            match check(ctx, exp, to) {
                Ok(check_derivation) => {
                    builder.add(check_derivation);
                    Ok((builder.build(judgement_from_ty(to)), *to.clone()))
                }
                Err(derivation) => {
                    builder.add(derivation);
                    Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check casted expression {:?} against type {:?}",
                        exp, to
                    )))))
                }
            }
        }
        // (ctx |- Proof(exp): exp) if (ctx |- exp : Prop) and (ctx |= exp)
        CoreExp::Proof { exp } => {
            let mut builder = Builder::new("Proof".to_string(), Some("infer".to_string()));
            // 1. check (ctx |- exp : Prop)
            match check(ctx, exp, &CoreExp::Sort(Sort::Prop)) {
                Ok(derivation) => {
                    builder.add(derivation);
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check proof expression {:?} against type Prop",
                        exp
                    )))));
                }
            }
            // 2. add goal (ctx |= exp)
            builder.add(Derivation::make_goal(ctx.clone(), *exp.clone()));
            // 3. conclude (ctx |- Proof(exp) : exp)
            Ok((builder.build(judgement_from_ty(exp)), *exp.clone()))
        }
        CoreExp::PowerSet { exp } => {
            let mut builer = Builder::new("PowerSet".to_string(), Some("infer".to_string()));
            // 1. check (ctx |- exp : Set(i))
            let sort = match infer_sort(ctx, exp) {
                Ok((derivation, sort)) => {
                    builer.add(derivation);
                    sort
                }
                Err(derivation) => {
                    builer.add(derivation);
                    return Err(builer.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        exp
                    )))));
                }
            };
            let Sort::Set(i) = sort else {
                return Err(builer.build(Judgement::FailJudge(FailJudge(format!(
                    "Type {:?} is not of form Set(i)",
                    exp
                )))));
            };
            // 2. conclude (ctx |- PowerSet(exp) : Set(i))
            let ty = CoreExp::Sort(Sort::Set(i));
            Ok((builer.build(judgement_from_ty(&ty)), ty))
        }
        CoreExp::SubSet { exp, predicate } => {
            let mut builder = Builder::new("SubSet".to_string(), Some("infer".to_string()));
            // 1. check (ctx |- exp : Set(i))
            let sort = match infer_sort(ctx, exp) {
                Ok((derivation, sort)) => {
                    builder.add(derivation);
                    sort
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        exp
                    )))));
                }
            };
            let Sort::Set(i) = sort else {
                return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Type {:?} is not of form Set(i)",
                    exp
                )))));
            };
            // 2. check (ctx, exp |= predicate : Prop)
            let extend = ctx.extend(*exp.clone());
            match check(&extend, predicate, &CoreExp::Sort(Sort::Prop)) {
                Ok(derivation) => {
                    builder.add(derivation);
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check predicate {:?} against type Prop in extended context",
                        predicate
                    )))));
                }
            };
            // 3. conclude (ctx |- SubSet(exp, predicate) : Power(exp)
            let ty = CoreExp::PowerSet { exp: exp.clone() };
            Ok((builder.build(judgement_from_ty(&ty)), ty))
        }
        CoreExp::Pred {
            superset,
            subset,
            element,
        } => {
            let mut builder = Builder::new("Pred".to_string(), Some("infer".to_string()));
            // 1. check (ctx |- superset : Set(i))
            let sort = match infer_sort(ctx, superset) {
                Ok((derivation, sort)) => {
                    builder.add(derivation);
                    sort
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        superset
                    )))));
                }
            };
            let Sort::Set(i) = sort else {
                return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Type {:?} is not of form Set(i)",
                    superset
                )))));
            };
            // 2. check (ctx |- subset : Power(superset))
            match check(
                ctx,
                subset,
                &CoreExp::PowerSet {
                    exp: superset.clone(),
                },
            ) {
                Ok(derivation) => {
                    builder.add(derivation);
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check subset {:?} against type Power(superset) in context",
                        subset
                    )))));
                }
            };
            // 3. check (ctx |- element : superset)
            match check(ctx, element, superset) {
                Ok(derivation) => {
                    builder.add(derivation);
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check element {:?} against type superset in context",
                        element
                    )))));
                }
            };
            // 4. conclude (ctx |- Pred(superset, subset, element) : Prop)
            let ty = CoreExp::Sort(Sort::Prop);
            Ok((builder.build(judgement_from_ty(&ty)), ty))
        }
        CoreExp::TypeLift { superset, subset } => {
            let mut builder = Builder::new("TypeLift".to_string(), Some("infer".to_string()));
            // 1. check (ctx |- superset : Set(i))
            let sort = match infer_sort(ctx, superset) {
                Ok((derivation, sort)) => {
                    builder.add(derivation);
                    sort
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        superset
                    )))));
                }
            };
            let Sort::Set(i) = sort else {
                return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Type {:?} is not of form Set(i)",
                    superset
                )))));
            };
            // 2. check (ctx |- subset : Power(superset))
            match check(
                ctx,
                subset,
                &CoreExp::PowerSet {
                    exp: superset.clone(),
                },
            ) {
                Ok(derivation) => {
                    builder.add(derivation);
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check subset {:?} against type Power(superset) in context",
                        subset
                    )))));
                }
            };
            // 3. conclude (ctx |- TypeLift(superset, subset) : Set(i))
            let ty = CoreExp::Sort(Sort::Set(i));
            Ok((builder.build(judgement_from_ty(&ty)), ty))
        }
        CoreExp::Equal { left, right } => {
            let mut builder = Builder::new("Equal".to_string(), Some("infer".to_string()));
            // 1. infer type of left
            let left_ty = match infer(ctx, left) {
                Ok((derivation, ty)) => {
                    builder.add(derivation);
                    ty
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer type of left expression {:?}",
                        left
                    )))));
                }
            };
            // 2. infer type of right
            let right_ty = match infer(ctx, right) {
                Ok((derivation, ty)) => {
                    builder.add(derivation);
                    ty
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer type of right expression {:?}",
                        right
                    )))));
                }
            };
            // 3. check left_ty and right_ty are convertible
            if !convertible(&left_ty, &right_ty) {
                return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Type mismatch: left type {:?} is not convertible to right type {:?}",
                    left_ty, right_ty
                )))));
            }
            // 4. conclude (ctx |- Equal(left, right) : Prop)
            let ty = CoreExp::Sort(Sort::Prop);
            Ok((builder.build(judgement_from_ty(&ty)), ty))
        }
        CoreExp::Exists { ty } => {
            let mut builder = Builder::new("Exists".to_string(), Some("infer".to_string()));
            // 1. check (ctx |- ty : Set(i))
            let sort = match infer_sort(ctx, ty) {
                Ok((derivation, sort)) => {
                    builder.add(derivation);
                    sort
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        ty
                    )))));
                }
            };
            let Sort::Set(_i) = sort else {
                return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Type {:?} is not of form Set(i)",
                    ty
                )))));
            };
            // 2. conclude (ctx |- Exists(ty) : Prop)
            let ty = CoreExp::Sort(Sort::Prop);
            Ok((builder.build(judgement_from_ty(&ty)), ty))
        }
        CoreExp::Take {
            map,
            domain,
            codomain,
        } => {
            let mut builder = Builder::new("Take".to_string(), Some("infer".to_string()));
            // 1. check (ctx |- domain : Set(i))
            let sort = match infer_sort(ctx, domain) {
                Ok((derivation, sort)) => {
                    builder.add(derivation);
                    sort
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        domain
                    )))));
                }
            };
            let Sort::Set(i) = sort else {
                return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Type {:?} is not of form Set(i)",
                    domain
                )))));
            };
            // 2. check (ctx |- codomain: Set(i))
            let sort = match infer_sort(ctx, codomain) {
                Ok((derivation, sort)) => {
                    builder.add(derivation);
                    sort
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to infer sort of type {:?}",
                        codomain
                    )))));
                }
            };
            let Sort::Set(j) = sort else {
                return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Type {:?} is not of form Set(i)",
                    codomain
                )))));
            };
            if i != j {
                return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                    "Type mismatch: domain sort Set({}) is not equal to codomain sort Set({})",
                    i, j
                )))));
            }
            // 3. check (ctx |- map : domain -> codomain)
            match check(
                ctx,
                map,
                &CoreExp::Prod {
                    ty: domain.clone(),
                    body: codomain.clone(),
                },
            ) {
                Ok(derivation) => {
                    builder.add(derivation);
                }
                Err(derivation) => {
                    builder.add(derivation);
                    return Err(builder.build(Judgement::FailJudge(FailJudge(format!(
                        "Failed to check map {:?} against type domain -> codomain in context",
                        map
                    )))));
                }
            };
            // 4. make two goals (ctx |= Exists(domain)) and (ctx |= (ctx |= (x1: domain) -> (x2: domain) -> Equal(map(x1), map(x2))))
            builder.add(Derivation::make_goal(
                ctx.clone(),
                CoreExp::Exists { ty: domain.clone() },
            ));
            let eq = CoreExp::Equal {
                left: Box::new(CoreExp::App {
                    func: map.clone(),
                    arg: Box::new(CoreExp::Var(0)),
                }),
                right: Box::new(CoreExp::App {
                    func: map.clone(),
                    arg: Box::new(CoreExp::Var(1)),
                }),
            };
            let impl_exp = CoreExp::Prod {
                ty: Box::new(domain.as_ref().clone()),
                body: Box::new(CoreExp::Prod {
                    ty: Box::new(domain.as_ref().clone()),
                    body: Box::new(eq),
                }),
            };
            builder.add(Derivation::make_goal(ctx.clone(), impl_exp));
            // 5. conclude (ctx |- Take(map, domain, codomain) : codomain)
            let ty = codomain.as_ref().clone();
            Ok((builder.build(judgement_from_ty(&ty)), ty))
        }
    }
}

pub fn infer_sort(ctx: &Context, term: &CoreExp) -> Result<(Derivation, Sort), Derivation> {
    // rule is Conversion, meta is sort
    let rule = "Conversion".to_string();
    let meta = "sort".to_string().into();

    // 1. infer type
    let (infer_derivation, inferred_ty) = match infer(ctx, term) {
        Ok(ok) => ok,
        Err(derivation) => {
            return Err(Derivation {
                conclusion: Judgement::FailJudge(FailJudge(format!(
                    "Failed to infer type of term {:?}: {:?}",
                    term, derivation
                ))),
                premises: vec![derivation],
                rule,
                meta,
            });
        }
    };
    // 2. check type is convertible to a sort
    let CoreExp::Sort(s) = normalize(&inferred_ty) else {
        return Err(Derivation {
            conclusion: Judgement::FailJudge(FailJudge(format!(
                "Type {:?} is not convertible to a sort",
                inferred_ty
            ))),
            premises: vec![infer_derivation],
            rule,
            meta,
        });
    };
    Ok((
        Derivation {
            conclusion: Judgement::Type(TypeJudge {
                ctx: ctx.clone(),
                term: term.clone(),
                ty: CoreExp::Sort(s),
            }),
            premises: vec![infer_derivation],
            rule,
            meta,
        },
        s,
    ))
}

pub fn prove_command(command: ProveCommandBy) -> Result<Derivation, (Derivation, String)> {
    match command {
        ProveCommandBy::Construct { ctx, proof_term } => todo!(),
        ProveCommandBy::ExactElem { ctx, elem, ty } => todo!(),
        ProveCommandBy::SubsetElim { ctx, elem, subset, superset } => todo!(),
        ProveCommandBy::IdRefl { ctx, elem, ty } => todo!(),
        ProveCommandBy::IdElim { ctx, elem1, elem2, ty, predicate } => todo!(),
        ProveCommandBy::TakeEq { func, elem } => todo!(),
        ProveCommandBy::Axiom(axiom) => todo!(),
    }
}
