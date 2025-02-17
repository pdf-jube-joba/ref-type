use super::*;
use inductive::*;

pub mod inductive {
    use self::inductives::InductiveDefinitionsSyntax;
    use crate::utils;

    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct IndTypeDefs {
        name: TypeName,
        parameter: Vec<(Var, Exp)>,
        arity: (Vec<(Var, Exp)>, Sort),
        constructors: Vec<(ConstructorName, ConstructorType)>,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    // P1 -> ... -> Pn -> X m1 ... mk
    pub struct ConstructorType {
        end: Vec<Exp>,         // = I m1 ... mk
        params: Vec<ParamCst>, // P[.]
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum ParamCst {
        Positive(Positive), // (_: P) -> C where P is positive of variable = X
        Simple((Var, Exp)), // (x: A) -> C where A.free_var does not contains X
    }

    // variable = X, parameter = [(y_1, M_1), ..., (y_k, M_k)], exps = [N_1, ... N_l]
    // => (y_1: M_1) -> ... -> (y_k: M_k) -> (X N_1 ... N_l)
    // free variable of Pos is only X
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Positive {
        parameter: Vec<(Var, Exp)>,
        exps: Vec<Exp>, // X N_1 ... N_l
    }

    impl ConstructorType {
        pub fn arg_num(&self) -> usize {
            self.params.len()
        }
        pub fn arg_end(&self) -> &Vec<Exp> {
            &self.end
        }
    }

    pub fn cstr_into_exp_with_assign(value: ConstructorType, exp: Exp) -> Exp {
        let ConstructorType { end, params } = value;
        let mut end = assoc_apply(exp.clone(), end);
        for p in params.into_iter().rev() {
            match p {
                ParamCst::Positive(positive) => {
                    end = Exp::prod(
                        Var::Unused,
                        positive_into_exp_with_assign(positive, exp.clone()),
                        end,
                    );
                }
                ParamCst::Simple((var, a)) => end = Exp::prod(var, a, end),
            }
        }
        end
    }

    impl Positive {
        pub fn parameter(&self) -> &Vec<(Var, Exp)> {
            &self.parameter
        }
        pub fn exps(&self) -> &Vec<Exp> {
            &self.exps
        }
    }

    pub fn positive_into_exp_with_assign(Positive { parameter, exps }: Positive, exp: Exp) -> Exp {
        assoc_prod(parameter, assoc_apply(exp, exps))
    }

    impl ConstructorType {
        pub fn eliminator_type(&self, q: Exp, mut c: Exp, type_name: TypeName) -> Exp {
            let Self { end, params } = self;

            let mut usable_fresh_var: usize = {
                let end_fresh = end.iter().map(fresh).max().unwrap_or(0);
                let params_fresh = params
                    .iter()
                    .map(|p| match p {
                        ParamCst::Positive(positive) => {
                            let positive: Exp = positive_into_exp_with_assign(
                                positive.clone(),
                                Exp::IndTypeType {
                                    ind_type_name: type_name.clone(),
                                },
                            );
                            fresh(&positive)
                        }
                        ParamCst::Simple((v, a)) => std::cmp::max(fresh_var(v), fresh(a)),
                    })
                    .max()
                    .unwrap_or(0);
                std::cmp::max(end_fresh, params_fresh)
            };

            let mut pre_params: Vec<(Var, Exp)> = vec![];

            for p in params {
                match p {
                    ParamCst::Positive(positive) => {
                        let Positive { parameter, exps } = positive.clone();
                        let new_var_p: Var = {
                            usable_fresh_var += 1;
                            Var::Internal("elimtype".to_string(), usable_fresh_var)
                        };
                        let qmpx_type = {
                            let p_x = assoc_apply(
                                Exp::Var(new_var_p.clone()),
                                parameter.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                            );
                            let q_m = assoc_apply(q.clone(), exps.clone());
                            let qmpx = Exp::App(Box::new(q_m), Box::new(p_x));
                            assoc_prod(parameter.clone(), qmpx)
                        };
                        let positive_as_exp: Exp = positive_into_exp_with_assign(
                            positive.clone(),
                            Exp::IndTypeType {
                                ind_type_name: type_name.clone(),
                            },
                        );
                        pre_params.push((new_var_p.clone(), positive_as_exp));
                        pre_params.push((Var::Unused, qmpx_type));
                        c = Exp::App(Box::new(c), Box::new(Exp::Var(new_var_p)));
                    }
                    ParamCst::Simple((x, a)) => {
                        pre_params.push((x.clone(), a.clone()));
                        c = Exp::App(Box::new(c), Box::new(Exp::Var(x.clone())));
                    }
                }
            }

            let res = Exp::App(Box::new(assoc_apply(q, end.to_owned())), Box::new(c));
            utils::assoc_prod(pre_params, res)
        }

        pub fn recursor(&self, ff: Exp, mut f: Exp, type_name: TypeName) -> Exp {
            let Self { end, params } = self;

            let mut usable_fresh_var = {
                let end_fresh = end.iter().map(fresh).max().unwrap_or(0);
                let params_fresh = params
                    .iter()
                    .map(|p| match p {
                        ParamCst::Positive(positive) => {
                            let positive_as_exp: Exp = positive_into_exp_with_assign(
                                positive.clone(),
                                Exp::IndTypeType {
                                    ind_type_name: type_name.clone(),
                                },
                            );
                            fresh(&positive_as_exp)
                        }
                        ParamCst::Simple((v, a)) => std::cmp::max(fresh_var(v), fresh(a)),
                    })
                    .max()
                    .unwrap_or(0);
                std::cmp::max(end_fresh, params_fresh)
            };

            let mut pre_params: Vec<(Var, Exp)> = vec![];
            for p in params {
                match p {
                    ParamCst::Positive(positive) => {
                        let Positive { parameter, exps } = positive.clone();
                        let new_var_p = {
                            usable_fresh_var += 1;
                            Var::Internal("recursor".to_string(), usable_fresh_var)
                        };
                        let lam_ffmpx = {
                            let p_x = assoc_apply(
                                Exp::Var(new_var_p.clone()),
                                parameter.iter().map(|(x, _)| Exp::Var(x.clone())).collect(),
                            );
                            let f_m = assoc_apply(ff.clone(), exps.clone());
                            let fmpx = Exp::App(Box::new(f_m), Box::new(p_x));
                            assoc_lam(parameter.clone(), fmpx)
                        };
                        f = Exp::App(
                            Box::new(Exp::App(Box::new(f), Box::new(Exp::Var(new_var_p.clone())))),
                            Box::new(lam_ffmpx),
                        );
                        let positive_as_exp: Exp = positive_into_exp_with_assign(
                            positive.clone(),
                            Exp::IndTypeType {
                                ind_type_name: type_name.clone(),
                            },
                        );
                        pre_params.push((new_var_p, positive_as_exp));
                    }
                    ParamCst::Simple((x, a)) => {
                        f = Exp::App(Box::new(f), Box::new(Exp::Var(x.clone())));
                        pre_params.push((x.clone(), a.clone()));
                    }
                }
            }

            utils::assoc_lam(pre_params, f)
        }
    }

    impl IndTypeDefs {
        pub fn new(
            InductiveDefinitionsSyntax {
                type_name,
                parameter,
                arity,
                constructors,
            }: crate::syntax::ast::inductives::InductiveDefinitionsSyntax,
        ) -> Result<Self, String> {
            use crate::environment::inductive::*;
            use crate::syntax::ast::inductives::*;
            let type_name_variable: Var = type_name.as_str().into();

            let mut cs_name_type = vec![];

            for (cs_name, params, mut end) in constructors {
                let mut new_params = vec![];

                for param in params {
                    let param = match param {
                        ParamCstSyntax::Positive((parameter, mut exps)) => {
                            if exps[0] != type_name_variable.clone().into() {
                                return Err(format!("type name mismatch in param:{exps:?} "));
                            }
                            let mut i = 0;
                            for (x, a) in &parameter {
                                if exps[i + 1] != x.clone().into() {
                                    return Err(format!(
                                        "parameter mismatch in param: {exps:?} at {i}"
                                    ));
                                }
                                i += 1;
                            }
                            exps.drain(0..=i);
                            let positive = Positive { parameter, exps };
                            ParamCst::Positive(positive)
                        }
                        ParamCstSyntax::Simple(simple) => ParamCst::Simple(simple),
                    };
                    new_params.push(param)
                }

                if end[0] != type_name_variable.clone().into() {
                    return Err(format!("type name mismatch in end: {end:?}"));
                }
                end.remove(0);

                let cstype = ConstructorType {
                    end,
                    params: new_params,
                };

                cs_name_type.push((cs_name.into(), cstype));
            }

            Ok(IndTypeDefs {
                name: type_name.as_str().to_owned().into(),
                parameter,
                arity,
                constructors: cs_name_type,
            })
        }
        pub fn name(&self) -> &TypeName {
            &self.name
        }
        pub fn name_as_var(&self) -> Var {
            self.name().to_string().into()
        }
        pub fn parameters(&self) -> &Vec<(Var, Exp)> {
            &self.parameter
        }
        pub fn arity(&self) -> &(Vec<(Var, Exp)>, Sort) {
            &self.arity
        }
        pub fn arity_as_exp(&self) -> Exp {
            let (vars, sort) = self.arity();
            assoc_prod(vars.clone(), (*sort).into())
        }
        pub fn arg_of_type(&self) -> &Vec<(Var, Exp)> {
            &self.arity.0
        }
        pub fn sort(&self) -> Sort {
            self.arity.1
        }
        pub fn constructors(&self) -> &Vec<(ConstructorName, ConstructorType)> {
            &self.constructors
        }
        pub fn constructor(&self, constructor_name: &ConstructorName) -> Option<&ConstructorType> {
            self.constructors.iter().find_map(|(name, c)| {
                if name == constructor_name {
                    Some(c)
                } else {
                    None
                }
            })
        }
        pub fn constructor_as_exp(&self, constructor_name: &ConstructorName) -> Option<Exp> {
            self.constructors.iter().find_map(|(name, constructor)| {
                if name == constructor_name {
                    Some(cstr_into_exp_with_assign(
                        constructor.clone(),
                        Exp::IndTypeType {
                            ind_type_name: self.name.clone(),
                        },
                    ))
                } else {
                    None
                }
            })
        }
        pub fn return_type(&self, sort: Sort) -> Exp {
            let arity = self.arity().clone();
            let vars = arity.0.iter().map(|(x, _)| Exp::Var(x.clone())).collect();
            let end = Exp::prod(
                Var::Unused,
                utils::assoc_apply(
                    Exp::IndTypeType {
                        ind_type_name: self.name().clone(),
                    },
                    vars,
                ),
                Exp::Sort(sort),
            );
            utils::assoc_prod(arity.0.clone(), end)
        }
        pub fn induction_scheme(&self, sort: Sort) -> Exp {
            let arity = self.arity().clone();
            // (x1: A1) -> ... -> (xn: An) -> (_: I x1 ... xn) -> s
            let return_type: Exp = {
                let vars = arity.0.iter().map(|(x, _)| Exp::Var(x.clone())).collect();
                let end = Exp::lambda(
                    Var::Unused,
                    utils::assoc_apply(
                        Exp::IndTypeType {
                            ind_type_name: self.name().clone(),
                        },
                        vars,
                    ),
                    Exp::Sort(sort),
                );
                utils::assoc_prod(arity.0.clone(), end)
            };
            let q_exp = Exp::Var("Q".into());
            // (fi: xi(I, Q, I::i, C_i)) -> ... ->
            let type_cases: Vec<(Var, Exp)> = {
                let mut v = vec![];
                for (cname, c) in self.constructors() {
                    // xi_X(Q, c, C[i])
                    let pre = c.eliminator_type(
                        q_exp.clone(),
                        Exp::IndTypeCst {
                            ind_type_name: self.name().clone(),
                            constructor_name: cname.clone(),
                        },
                        self.name.clone(),
                    );
                    v.push((cname.to_string().into(), pre));
                }
                v
            };
            // (x1: A1) -> ... -> (xn: An) -> (x: I x1... xn) -> Q x1 ... xn x
            let end: Exp = {
                let vars: Vec<Exp> = arity.0.iter().map(|(x, _)| Exp::Var(x.clone())).collect();
                let new_x: Var = "x".into();
                let end = Exp::lambda(
                    new_x.clone(),
                    utils::assoc_apply(
                        Exp::IndTypeType {
                            ind_type_name: self.name().clone(),
                        },
                        vars.clone(),
                    ),
                    utils::assoc_apply(
                        utils::assoc_apply(q_exp.clone(), vars),
                        vec![Exp::Var(new_x)],
                    ),
                );
                utils::assoc_prod(arity.0.clone(), end)
            };
            Exp::prod("Q".into(), return_type, utils::assoc_prod(type_cases, end))
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct GlobalContext {
    definitions: Vec<(Var, Exp, Exp)>,       // x := v
    parameters: Vec<(Var, Exp)>,             // x: t
    inductive_definitions: Vec<IndTypeDefs>, // inductive definitions
}
impl GlobalContext {
    pub(crate) fn push_new_defs(&mut self, (x, a, v): (Var, Exp, Exp)) {
        self.definitions.push((x, a, v));
    }
    pub(crate) fn push_new_assum(&mut self, (x, a): (Var, Exp)) {
        self.parameters.push((x, a));
    }
    pub(crate) fn push_new_ind(&mut self, defs: IndTypeDefs) {
        self.inductive_definitions.push(defs);
    }
    pub fn type_of_indtype(&self, ind_type_name: &TypeName) -> Option<Exp> {
        let indtype_def = self.indtype_def(ind_type_name)?;
        Some(indtype_def.arity_as_exp())
    }
    pub fn indtype_def(&self, type_name: &TypeName) -> Option<&IndTypeDefs> {
        self.inductive_definitions
            .iter()
            .find(|defs| defs.name() == type_name)
    }
    pub fn indtype_defs(&self) -> &Vec<IndTypeDefs> {
        &self.inductive_definitions
    }
    pub fn type_of_cst(
        &self,
        ind_type_name: &TypeName,
        constructor_name: &ConstructorName,
    ) -> Option<Exp> {
        let defs = self.indtype_def(ind_type_name)?;
        let constructor_def = defs.constructor(constructor_name)?;
        let constructor_exp: Exp = cstr_into_exp_with_assign(
            constructor_def.clone(),
            Exp::IndTypeType {
                ind_type_name: ind_type_name.clone(),
            },
        );
        Some(constructor_exp)
    }
    pub fn ind_type_return_type(&self, ind_type_name: &TypeName, sort: Sort) -> Option<Exp> {
        let inddefs = self.indtype_def(ind_type_name)?;
        Some(inddefs.return_type(sort))
    }
    pub fn induction_principal(&self, ind_type_name: &TypeName, sort: Sort) -> Option<Exp> {
        let inddefs = self.indtype_def(ind_type_name)?;
        Some(inddefs.induction_scheme(sort))
    }
    pub fn search_var_defined(&self, y: Var) -> Option<(&Exp, &Exp)> {
        self.definitions
            .iter()
            .find_map(|(x, a, e)| if *x == y { Some((a, e)) } else { None })
    }
    pub fn search_var_assum(&self, y: Var) -> Option<&Exp> {
        self.parameters
            .iter()
            .find_map(|(x, a)| if *x == y { Some(a) } else { None })
    }
}
