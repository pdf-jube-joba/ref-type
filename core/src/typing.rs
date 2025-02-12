use crate::{
    ast::*,
    environment::{derivation_tree::*, global_context::*, tree_node::*},
    lambda_calculus::*,
    prod,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JudgementTreeBuilder {
    context: LocalContext,
    term: Exp,
    type_of_term: Option<Exp>,
    generated_info: String,
    now_case: Option<String>,
    label: Option<DerivationLabel>,
    child: Vec<DerChild>,
    err_cases: Vec<ErrCases>,
}

impl JudgementTreeBuilder {
    fn new(context: LocalContext, term: Exp, generated_info: String) -> Self {
        Self {
            context,
            term,
            type_of_term: None,
            generated_info,
            now_case: None,
            label: None,
            child: vec![],
            err_cases: vec![],
        }
    }
    fn case(&mut self, case: String) {
        assert!(self.now_case.is_none());
        self.now_case = Some(case);
    }
    fn push(&mut self, child: DerChild) {
        self.child.push(child);
    }
    fn label(&mut self, label: DerivationLabel) {
        assert!(self.label.is_none());
        self.label = Some(label);
    }
    fn set_type(&mut self, type_of_term: Exp) {
        assert!(self.type_of_term.is_none());
        self.type_of_term = Some(type_of_term);
    }
    fn build(self) -> PartialDerivationTreeTypeCheck {
        let Self {
            context,
            term,
            type_of_term,
            generated_info,
            now_case,
            label,
            child,
            err_cases,
        } = self;
        PartialDerivationTreeTypeCheck {
            head: TypeCheckJudgement {
                context,
                term,
                type_of_term: type_of_term.unwrap(),
            },
            label: label.unwrap(),
            child,
            gen_and_case: (generated_info, now_case.unwrap()),
            other_case: err_cases,
        }
    }
    fn case_fail(&mut self, err_info: ErrInfo) {
        assert!(self.now_case.is_some());
        let now_case = {
            let success = self.child.drain(..).collect();
            ErrCases {
                case: self.now_case.take().unwrap(),
                successes: success,
                error: err_info,
            }
        };
        self.err_cases.push(now_case);
    }
    fn build_fail_tree(self) -> DerivationFailed {
        let Self {
            context,
            term,
            type_of_term,
            generated_info,
            now_case,
            label,
            child,
            err_cases,
        } = self;

        assert!(now_case.is_none() && label.is_none() && child.is_empty());

        let head = match type_of_term {
            Some(type_of_term) => FailHead::CheckFail(TypeCheckJudgement {
                context,
                term,
                type_of_term,
            }),
            None => FailHead::InferFail(context, term),
        };

        DerivationFailed {
            head,
            generated_info,
            err_cases,
        }
    }
}

pub fn type_check(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term1: Exp,
    expected: Exp,
) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
    let mut builder = JudgementTreeBuilder::new(
        cxt.clone(),
        term1.clone(),
        format!("type check {cxt} |- {term1}: {expected}"),
    );
    builder.set_type(expected.clone());

    // get infered type of term1
    let infered_tree = match type_infer(gcxt, cxt.clone(), term1.clone()) {
        Ok(ok) => ok,
        Err(err) => {
            // term1 should infered type
            builder.case(format!("inference type of {term1}"));
            builder.case_fail(err.into());
            return Err(builder.build_fail_tree());
        }
    };

    // get infered sort of expected
    let (sort_of_expected_tree, sort_of_expected) =
        match type_infered_to_sort(gcxt, cxt.clone(), expected.clone()) {
            Ok(ok) => ok,
            Err(err) => {
                // expected should have infered sort
                builder.case(format!("inference type of {expected}"));
                builder.case_fail(err.into());
                return Err(builder.build_fail_tree());
            }
        };

    // 1. if infered =^beta expected => OK (by Conv Rule)
    builder.case("conv ?".to_string());
    let err = 'conversion: {
        match Condition::convertible(gcxt, expected.clone(), infered_tree.of_type().clone()) {
            Ok(cond) => {
                // ok by conv
                builder.push(cond.into()); // infered ~= expected
            }
            Err(err) => {
                break 'conversion err;
            }
        };
        builder.push(infered_tree.into()); // G |- t: infered
        builder.push(sort_of_expected_tree.into()); // G |- expected: sort
        builder.label(DerivationLabel::Conv);
        return Ok(builder.build());
    };
    builder.case_fail(err.into());

    // 2. if infered ->* Pow(A), expected ->* SET => Ok (by PowWeak)
    builder.case("pow weak ?".to_string());
    let err: ErrInfo = 'pow_weak: {
        // 1. check expected ->* SET
        let sort = match Condition::reduce_to_sort(gcxt, expected.clone()) {
            Ok((cond, sort)) => {
                builder.push(cond.into());
                sort
            }
            Err(err) => {
                break 'pow_weak err.into();
            }
        };

        if sort != Sort::Set {
            break 'pow_weak format!("expected ->*! SET but {sort}").into();
        }

        // 2. infered ->* Pow(A)
        match Condition::reduce_to_pow(gcxt, infered_tree.of_type().clone()) {
            Ok((cond, pow)) => {
                builder.push(cond.into());
                pow
            }
            Err(err) => {
                break 'pow_weak err.into();
            }
        };

        // ok by powersetweak
        builder.push(infered_tree.into()); // G |- t: infered
        builder.label(DerivationLabel::PowerSetWeak);
        return Ok(builder.build());
    };
    builder.case_fail(err);

    // 3. if cxt |- expected: Pow(super_expected)
    // check cxt |- term1 <| super_expected
    // ask cxt |= Pred(super_expected, expected) term1
    builder.case("expect has super set ?".to_string());
    let err: ErrInfo = 'sub_intro: {
        // 1. check cxt |- expected |> Pow(super_expected)
        let super_expected = match type_infered_to_pow(gcxt, cxt.clone(), expected.clone()) {
            Ok((tree, super_exp)) => {
                builder.push(tree.into());
                super_exp
            }
            Err(err) => {
                break 'sub_intro err.into();
            }
        };

        // 2. check term1 <| A
        match type_check(gcxt, cxt.clone(), term1.clone(), super_expected.clone()) {
            Ok(tree) => {
                builder.push(tree.into());
            }
            Err(err) => {
                break 'sub_intro err.into();
            }
        };

        // let prop := cxt |= Pred(A, expected) term1
        let proposition = Exp::pred_of_element(super_expected, expected, term1);

        builder.push(
            ProvableJudgement {
                context: cxt.clone(),
                proposition,
            }
            .into(),
        );
        builder.label(DerivationLabel::SubsetIntro);

        return Ok(builder.build());
    };
    builder.case_fail(err);

    // 4. otherwise
    // expected has no super set .. so outermost super set of infered should equal to expected
    // check cxt |- infered <= A_1 <= ... <= A_n !<= term with expected =~ A_n
    builder.case("infered <= expected ?".to_string());
    let err: ErrInfo = 'subset_elim_set: {
        let mut set = infered_tree.of_type().clone();
        while let Ok((super_set_tree, super_set)) =
            type_infered_to_pow(gcxt, cxt.clone(), set.clone())
        {
            builder.push(super_set_tree.into());
            set = super_set;
        }

        let cond = match Condition::convertible(gcxt, expected.clone(), set) {
            Ok(cond) => cond,
            Err(err) => {
                break 'subset_elim_set err.into();
            }
        };

        builder.push(cond.into());
        builder.label(DerivationLabel::SubsetElimSet);
        return Ok(builder.build());
    };
    builder.case_fail(err);

    Err(builder.build_fail_tree())
}

// Γ |- t |>_s (s in S) かどうか
pub fn type_infered_to_sort(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
) -> Result<(PartialDerivationTreeTypeCheck, Sort), DerivationFailed> {
    let mut builder = JudgementTreeBuilder::new(
        cxt.clone(),
        term.clone(),
        format!("infered to sort {cxt} |- {term}: ?"),
    );

    // get T of G |- t |> infered
    let der_tree_infered = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => der_tree_check,
        Err(derivation_failed) => {
            builder.case(format!("infer {term}"));
            builder.case_fail(derivation_failed.into());
            return Err(builder.build_fail_tree());
        }
    };

    // 1. if infered ->* sort => ok
    builder.case("conv to sort ?".to_string());
    let err: ErrInfo = 'conv_to_sort: {
        // 1. infered ->* sort ?
        let infered_sort = match Condition::reduce_to_sort(gcxt, der_tree_infered.of_type().clone())
        {
            Ok((cond, sort)) => {
                builder.push(cond.into());
                sort
            }
            Err(err) => {
                break 'conv_to_sort err.into();
            }
        };

        builder.push(der_tree_infered.into());
        builder.set_type(infered_sort.into());
        builder.label(DerivationLabel::Conv);
        return Ok((builder.build(), infered_sort));
    };
    builder.case_fail(err);

    // 2. if infered ->* Pow(A) => ok
    builder.case("conv to pow ?".to_string());
    let err: ErrInfo = 'conv_to_pow: {
        match Condition::reduce_to_pow(gcxt, der_tree_infered.of_type().clone()) {
            Ok((cond, _)) => {
                builder.push(cond.into());
            }
            Err(err) => {
                break 'conv_to_pow err.into();
            }
        };
        builder.push(der_tree_infered.into());
        builder.label(DerivationLabel::PowerSetWeak);
        builder.set_type(Sort::Set.into());

        // ok
        return Ok((builder.build(), Sort::Set));
    };
    builder.case_fail(err);

    Err(builder.build_fail_tree())
}

// Γ |- t |> (x: a) -> b
pub fn type_infered_to_prod(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
) -> Result<(PartialDerivationTreeTypeCheck, (Var, Exp, Exp)), DerivationFailed> {
    let mut builder = JudgementTreeBuilder::new(
        cxt.clone(),
        term.clone(),
        format!("infered prod {cxt} |- {term}"),
    );
    builder.case("only prod".to_string());

    // get T of G |- t |> infered
    let infered_type = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => {
            let infered = der_tree_check.of_type().clone();
            builder.push(der_tree_check.into());
            infered
        }
        Err(derivation_failed) => {
            builder.case_fail(derivation_failed.into());
            // t should have type
            return Err(builder.build_fail_tree());
        }
    };

    // get outer_most super set of infered
    let outer_infered: Exp = {
        let mut set = infered_type;
        while let Ok((super_set_tree, super_set)) =
            type_infered_to_pow(gcxt, cxt.clone(), set.clone())
        {
            builder.push(super_set_tree.into());
            set = super_set;
        }
        set
    };

    match Condition::reduce_to_prod(gcxt, outer_infered) {
        Ok((cond, (x, a, b))) => {
            builder.push(cond.into());
            builder.label(DerivationLabel::Conv);
            builder.set_type(Exp::prod(x.clone(), a.clone(), b.clone()));
            Ok((builder.build(), (x, a, b)))
        }

        Err(err) => {
            builder.case_fail(err.into());
            Err(builder.build_fail_tree())
        }
    }
}

// Γ |- t1 |> P(t2) かどうか
pub fn type_infered_to_pow(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
) -> Result<(PartialDerivationTreeTypeCheck, Exp), DerivationFailed> {
    let mut builder = JudgementTreeBuilder::new(
        cxt.clone(),
        term.clone(),
        format!("infered pow {cxt} |- {term}: ?"),
    );
    builder.case("only pow".to_string());

    // get T of G |- t |> infered
    let infered_type = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => {
            let infered_type = der_tree_check.of_type().clone();
            builder.push(der_tree_check.into());
            infered_type
        }
        Err(derivation_failed) => {
            builder.case_fail(derivation_failed.into());
            // t should have type
            return Err(builder.build_fail_tree());
        }
    };

    // check infered ->* Pow(super)
    match Condition::reduce_to_pow(gcxt, infered_type) {
        Ok((cond, pow)) => {
            builder.push(cond.into());
            builder.label(DerivationLabel::Conv);
            builder.set_type(Exp::Pow(Box::new(pow.clone())));
            Ok((builder.build(), pow))
        }
        Err(err) => {
            builder.case_fail(err.into());
            Err(builder.build_fail_tree())
        }
    }
}

// Γ |- t |> I a1 ... an
pub fn type_infered_to_ind(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
) -> Result<(PartialDerivationTreeTypeCheck, (TypeName, Vec<Exp>)), DerivationFailed> {
    let mut builder = JudgementTreeBuilder::new(
        cxt.clone(),
        term.clone(),
        format!("infered ind {cxt} |- {term}"),
    );
    builder.case("only ind".to_string());

    // get T of G |- t |> infered
    let infered_type = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => {
            let infered_type = der_tree_check.of_type().clone();
            builder.push(der_tree_check.into());
            infered_type
        }
        Err(derivation_failed) => {
            builder.case_fail(derivation_failed.into());
            // t should have type
            return Err(builder.build_fail_tree());
        }
    };

    match Condition::reduce_to_indtype(gcxt, infered_type) {
        Ok((cond, (type_name, args))) => {
            builder.push(cond.into());
            builder.label(DerivationLabel::Conv);
            builder.set_type(utils::assoc_apply(
                Exp::IndTypeType {
                    ind_type_name: type_name.clone(),
                },
                args.clone(),
            ));
            Ok((builder.build(), (type_name, args)))
        }
        Err(err) => {
            builder.case_fail(err.into());
            Err(builder.build_fail_tree())
        }
    }
}

// exists s' s.t.  |- t |> (x_1: A_1) -> ... (x_k: A_k) -> (_: I x_1 ... x_k) -> s'
// where (x_1: A_1) -> ... -> (x_k A_k) = arity of I
pub fn type_infered_to_ind_return_type(
    gcxt: &GlobalContext,
    cxt: LocalContext,
    term: Exp,
    type_name: TypeName,
) -> Result<(PartialDerivationTreeTypeCheck, Sort), DerivationFailed> {
    let mut builder = JudgementTreeBuilder::new(
        cxt.clone(),
        term.clone(),
        format!("infered return type {cxt} |- {term}: ... -> {type_name}"),
    );
    builder.case("only return type".to_string());

    // get T of G |- t |> infered
    let infered_type = match type_infer(gcxt, cxt.clone(), term.clone()) {
        Ok(der_tree_check) => {
            let infered_type = der_tree_check.of_type().clone();
            builder.push(der_tree_check.into());
            infered_type
        }
        Err(derivation_failed) => {
            builder.case_fail(derivation_failed.into());
            // t should have type
            return Err(builder.build_fail_tree());
        }
    };

    match Condition::reduce_to_returntype(gcxt, infered_type, type_name) {
        Ok((cond, (_params, sort))) => {
            builder.push(cond.into());
            builder.label(DerivationLabel::Conv);
            builder.set_type(Exp::Sort(sort));
            Ok((builder.build(), sort))
        }
        Err(err) => {
            builder.case_fail(err.into());
            Err(builder.build_fail_tree())
        }
    }
}

pub fn type_infer(
    gcxt: &GlobalContext,
    mut cxt: LocalContext,
    term1: Exp,
) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
    let mut builder = JudgementTreeBuilder::new(
        cxt.clone(),
        term1.clone(),
        format!("type infer {cxt} |- {term1}"),
    );

    match term1 {
        Exp::Sort(sort) => {
            builder.case("term is sort".to_string());

            match Condition::axiom_sort(sort) {
                Ok((cond, sort)) => {
                    builder.push(cond.into());
                    builder.label(DerivationLabel::Axiom);
                    builder.set_type(sort.into());
                    Ok(builder.build())
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    Err(builder.build_fail_tree())
                }
            }
        }
        Exp::Var(x) => {
            // global definition
            builder.case("var: global def".to_string());
            if let Some(e) = gcxt.search_var_defined(x.clone()) {
                builder.label(DerivationLabel::GlobalDefinition);
                builder.set_type(e.0.clone());
                return Ok(builder.build());
            }
            builder.case_fail("not global def".to_string().into());

            // global assumption
            builder.case("var: global assum".to_string());
            if let Some(e) = gcxt.search_var_assum(x.clone()) {
                builder.label(DerivationLabel::GlobalAssumption);
                builder.set_type(e.clone());
                return Ok(builder.build());
            }
            builder.case_fail("not global assum".to_string().into());

            builder.case("var: context".to_string());
            match Condition::context_has_var(cxt, x.clone()) {
                Ok((cond, e)) => {
                    builder.push(cond.into());
                    builder.label(DerivationLabel::Variable);
                    builder.set_type(e);
                    Ok(builder.build())
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    Err(builder.build_fail_tree())
                }
            }
        }
        Exp::Prod(mut x, t, mut t2) => {
            builder.case("prod".to_string());

            // get G |- t |. s
            let sort_of_t = match type_infered_to_sort(gcxt, cxt.clone(), *t.clone()) {
                Ok((der_tree, sort)) => {
                    builder.push(der_tree.into());
                    sort
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            };

            // overlap of variable
            if cxt.search_var_exp(&x).is_some() {
                let new_var = cxt.new_variable();
                t2 = Box::new(subst(*t2, &x, &Exp::Var(new_var.clone())));
                x = new_var;
            }

            cxt.push_decl((x, *t));

            let sort_of_t2 = match type_infered_to_sort(gcxt, cxt, *t2.clone()) {
                Ok((der_tree, sort)) => {
                    builder.push(der_tree.into());
                    sort
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            };

            match Condition::relation_sort(sort_of_t, sort_of_t2) {
                Ok((cond, s3)) => {
                    builder.push(cond.into());
                    builder.label(DerivationLabel::ProdForm);
                    builder.set_type(s3.into());
                    Ok(builder.build())
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    Err(builder.build_fail_tree())
                }
            }
        }
        Exp::Lam(mut x, t, mut m) => {
            builder.case("case lam".to_string());

            // sort of t
            let sort_of_t = match type_infered_to_sort(gcxt, cxt.clone(), *t.clone()) {
                Ok((der_tree, sort)) => {
                    builder.push(der_tree.into());
                    sort
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            };

            // overlap of variable
            if cxt.search_var_exp(&x).is_some() {
                let new_var = cxt.new_variable();
                m = Box::new(subst(*m, &x, &Exp::Var(new_var.clone())));
                x = new_var;
            }

            cxt.push_decl((x.clone(), *t.clone()));

            let type_m = match type_infer(gcxt, cxt.clone(), *m.clone()) {
                Ok(der_tree) => {
                    let type_of_m = der_tree.head.type_of_term.clone();
                    builder.push(der_tree.into());
                    type_of_m
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            };

            builder.label(DerivationLabel::ProdIntro);
            builder.set_type(Exp::prod(x, *t, type_m));

            Ok(builder.build())
        }
        Exp::App(t1, t2) => {
            builder.case("term is app".to_string());

            // get G |- t1 |> (x: a)  ->* b
            let (x, a, b) = match type_infered_to_prod(gcxt, cxt.clone(), *t1.clone()) {
                Ok((der_tree, (x, a, b))) => {
                    builder.push(der_tree.into());
                    (x, a, b)
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            };

            match type_check(gcxt, cxt.clone(), *t2.clone(), a.clone()) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                    builder.label(DerivationLabel::ProdElim);
                    builder.set_type(subst(b, &x, &t2));
                    Ok(builder.build())
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    Err(builder.build_fail_tree())
                }
            }
        }
        Exp::IndTypeType { ind_type_name } => {
            builder.case("ind form".to_string());

            // ind_type_name is defined ?
            let type_of_ind_type = match gcxt.type_of_indtype(&ind_type_name) {
                Some(e) => e,
                None => {
                    builder.case_fail(format!("ind type {ind_type_name} is not defined").into());
                    return Err(builder.build_fail_tree());
                }
            };

            builder.label(DerivationLabel::IndForm);
            builder.set_type(type_of_ind_type);

            // ok
            Ok(builder.build())
        }
        Exp::IndTypeCst {
            ind_type_name,
            constructor_name,
        } => {
            builder.case("ind intro".to_string());

            // ind_type_name::constructor_name is defined ?
            let type_of_cst_type = match gcxt.type_of_cst(&ind_type_name, &constructor_name) {
                Some(e) => e,
                None => {
                    builder.case_fail(
                        format!("constructor {ind_type_name}::{constructor_name} is not defined")
                            .into(),
                    );
                    return Err(builder.build_fail_tree());
                }
            };

            builder.label(DerivationLabel::IndIntro);
            builder.set_type(type_of_cst_type);
            Ok(builder.build())
        }
        Exp::IndTypeElim {
            ind_type_name,
            eliminated_exp,
            return_type,
            cases,
        } => {
            builder.case("ind elim".to_string());

            // find ind type
            let inddefs = match gcxt.indtype_def(&ind_type_name) {
                Some(inddefs) => inddefs,
                None => {
                    builder.case_fail(format!("ind_type {ind_type_name} is not defined").into());
                    return Err(builder.build_fail_tree());
                }
            };

            // return type infered to nice form
            let end_sort = match type_infered_to_ind_return_type(
                gcxt,
                cxt.clone(),
                *return_type.clone(),
                ind_type_name.clone(),
            ) {
                Ok((der_tree, end_sort)) => {
                    builder.push(der_tree.into());
                    end_sort
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            };

            // (sort of ind type, sort of return type) in rel
            match Condition::indrel_sort(inddefs.sort(), end_sort) {
                Ok(cond) => {
                    builder.push(cond.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            // |- eliminated_exp: I a1 ... an where I == ind_type
            let arg_of_type = match type_infered_to_ind(gcxt, cxt.clone(), *eliminated_exp.clone())
            {
                Ok((der_tree, (type_name, args))) => {
                    builder.push(der_tree.into());
                    if type_name != *inddefs.name() {
                        builder.case_fail(
                            format!("type of {eliminated_exp} expected {} found {type_name}", {
                                inddefs.name()
                            })
                            .into(),
                        );
                        return Err(builder.build_fail_tree());
                    }
                    args
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            };

            // for each f[i],  |- f[i]: eliminator_type
            for (cname, c) in inddefs.constructors() {
                let corresponding_case = cases
                    .iter()
                    .find_map(|(c, e)| if c == cname { Some(e.clone()) } else { None })
                    .unwrap();
                let expected = c.eliminator_type(
                    *return_type.clone(),
                    Exp::IndTypeCst {
                        ind_type_name: ind_type_name.clone(),
                        constructor_name: cname.clone(),
                    },
                    ind_type_name.clone(),
                );

                match type_check(gcxt, cxt.clone(), corresponding_case, expected) {
                    Ok(der_tree) => {
                        builder.push(der_tree.into());
                    }
                    Err(err) => {
                        builder.case_fail(err.into());
                        return Err(builder.build_fail_tree());
                    }
                };
            }

            let type_of_term = Exp::App(
                Box::new(utils::assoc_apply(
                    *return_type.clone(),
                    arg_of_type.clone(),
                )),
                Box::new(*eliminated_exp.clone()),
            );

            builder.label(DerivationLabel::IndElim);
            builder.set_type(type_of_term);
            Ok(builder.build())
        }
        Exp::Proof(t) => {
            builder.case("proof".to_string());

            match type_check(gcxt, cxt.clone(), *t.clone(), Sort::Prop.into()) {
                Ok(tree) => builder.push(tree.into()),
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            let provablejudgement = ProvableJudgement {
                context: cxt.clone(),
                proposition: *t.clone(),
            };
            builder.push(provablejudgement.into());
            builder.label(DerivationLabel::Proof);
            builder.set_type(*t.clone());
            Ok(builder.build())
        }
        Exp::Sub(mut x, a, mut p) => {
            builder.case("sub form".to_string());

            // check cxt |- a: SET
            match type_check(gcxt, cxt.clone(), *a.clone(), Exp::Sort(Sort::Set)) {
                Ok(der_tree) => builder.push(der_tree.into()),
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            };

            // overlap of variable
            if cxt.search_var_exp(&x).is_some() {
                let new_var = cxt.new_variable();
                p = Box::new(subst(*p, &x, &Exp::Var(new_var.clone())));
                x = new_var;
            }

            // check cxt, x: a |- p: PROP
            cxt.push_decl((x, *a.clone()));
            match type_check(gcxt, cxt.clone(), *p.clone(), Exp::Sort(Sort::Prop)) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            // ok
            builder.label(DerivationLabel::SubsetForm);
            builder.set_type(Exp::Pow(a));
            Ok(builder.build())
        }
        Exp::Pow(a) => {
            builder.case("pow form".to_string());

            // check cxt |- a: SET
            match type_check(gcxt, cxt.clone(), *a.clone(), Exp::Sort(Sort::Set)) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            // ok
            builder.label(DerivationLabel::PowerSetForm);
            builder.set_type(Sort::Set.into());
            Ok(builder.build())
        }
        Exp::Pred(a, b) => {
            builder.case("pred ".to_string());

            // check cxt |- b: Pow(a) ?
            match type_check(gcxt, cxt.clone(), *b.clone(), Exp::Pow(a.clone())) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            builder.label(DerivationLabel::PredForm);
            builder.set_type(Exp::prod(Var::Unused, *a.clone(), Exp::Sort(Sort::Prop)));
            Ok(builder.build())
        }
        Exp::Id(exp, exp1, exp2) => {
            builder.case("identity".to_string());

            // check cxt |- exp: SET
            match type_check(gcxt, cxt.clone(), *exp.clone(), Sort::Set.into()) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            // check cxt |- exp1: exp
            match type_check(gcxt, cxt.clone(), *exp1.clone(), *exp.clone()) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            // check cxt |- exp2: exp
            match type_check(gcxt, cxt.clone(), *exp2.clone(), *exp.clone()) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            builder.label(DerivationLabel::IdentityForm);
            builder.set_type(Sort::Prop.into());

            Ok(builder.build())
        }
        Exp::Refl(exp, exp1) => {
            builder.case("refl".to_string());

            // check cxt |- exp: SET
            match type_check(gcxt, cxt.clone(), *exp.clone(), Sort::Set.into()) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            // check cxt |- exp1: exp
            match type_check(gcxt, cxt.clone(), *exp1.clone(), *exp.clone()) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            builder.label(DerivationLabel::IndIntro);
            builder.set_type(Exp::Id(
                Box::new(*exp.clone()),
                Box::new(*exp1.clone()),
                Box::new(*exp1.clone()),
            ));

            Ok(builder.build())
        }
        Exp::Exists(exp) => {
            builder.case("exists".to_string());

            // check cxt |- exp: SET
            match type_check(gcxt, cxt.clone(), *exp.clone(), Sort::Set.into()) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            builder.label(DerivationLabel::ExistsIntro);
            builder.set_type(Sort::Prop.into());

            Ok(builder.build())
        }
        Exp::Take(mut var, exp, mut exp1) => {
            builder.case("take".to_string());

            // check cxt |- exp: SET
            match type_check(gcxt, cxt.clone(), *exp.clone(), Sort::Set.into()) {
                Ok(der_tree) => {
                    builder.push(der_tree.into());
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            }

            // overlap of variable
            if cxt.search_var_exp(&var).is_some() {
                let new_var = cxt.new_variable();
                exp1 = Box::new(subst(*exp1, &var, &Exp::Var(new_var.clone())));
                var = new_var;
            }

            // infer cxt, var: exp |- exp1: M
            cxt.push_decl((var.clone(), *exp.clone()));
            let infered_type = match type_infer(gcxt, cxt.clone(), *exp1.clone()) {
                Ok(ok) => {
                    let infered = ok.of_type().clone();
                    builder.push(ok.into());
                    infered
                }
                Err(err) => {
                    builder.case_fail(err.into());
                    return Err(builder.build_fail_tree());
                }
            };
            let (cxt, _) = cxt.poped().unwrap();

            // need proof of cxt |-
            let proposition1: ProvableJudgement = ProvableJudgement {
                context: cxt.clone(),
                proposition: Exp::Exists(exp.clone()),
            };

            // need proof of (y1: exp) -> (y2: exp) ->
            let proposition2: ProvableJudgement = {
                let fresh_num = fresh(&exp1);

                let new_var1 = Var::Internal("gen by take".to_string(), fresh_num);
                let new_var2 = Var::Internal("gen by take".to_string(), fresh_num + 1);

                let end = Exp::Id(
                    Box::new(infered_type.clone()),
                    Box::new(subst(*exp.clone(), &var, &Exp::Var(new_var1.clone()))),
                    Box::new(subst(*exp.clone(), &var, &Exp::Var(new_var2.clone()))),
                );

                ProvableJudgement {
                    context: cxt.clone(),
                    proposition: prod!(new_var1, *exp.clone(), prod!(new_var2, *exp.clone(), end)),
                }
            };

            builder.push(proposition1.into());
            builder.push(proposition2.into());
            builder.label(DerivationLabel::TakeIntro);
            builder.set_type(infered_type);

            Ok(builder.build())
        }
    }
}
