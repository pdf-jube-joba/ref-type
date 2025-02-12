use super::*;
use inductive::*;

pub mod inductive {
    use self::inductives::InductiveDefinitionsSyntax;

    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct IndTypeDefs {
        name: TypeName,
        variable: Var,
        arity: (Vec<(Var, Exp)>, Sort),
        constructors: Vec<(ConstructorName, ConstructorType)>,
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    // P1 -> ... -> Pn -> X m1 ... mk
    pub struct ConstructorType {
        end: (Var, Vec<Exp>),  // = X m1 ... mk
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
        variable: Var,
        exps: Vec<Exp>,
    }

    impl ConstructorType {
        pub fn variable(&self) -> &Var {
            &self.end.0
        }
        pub fn arg_num(&self) -> usize {
            self.params.len()
        }
        pub fn arg_end(&self) -> &Vec<Exp> {
            &self.end.1
        }
        pub fn new_constructor(
            end: (Var, Vec<Exp>),
            params: Vec<ParamCst>,
        ) -> Result<(Self, Var), String> {
            let var_type = end.0.clone();
            for p in &params {
                match p {
                    ParamCst::Positive(positive) => {
                        if positive.variable != var_type {
                            return Err(format!(
                                "positive param {positive:?} contains {var_type:?}"
                            ));
                        }
                    }
                    ParamCst::Simple((_, a)) => {
                        if a.free_variable().contains(&var_type) {
                            return Err(format!("arg {a:?} contains {var_type:?}"));
                        }
                    }
                }
            }
            Ok((Self { end, params }, var_type))
        }
    }

    impl From<ConstructorType> for Exp {
        fn from(value: ConstructorType) -> Exp {
            let ConstructorType {
                end: (v, exps),
                params,
            } = value;
            let mut end = assoc_apply(Exp::Var(v), exps);
            for p in params.into_iter().rev() {
                match p {
                    ParamCst::Positive(positive) => {
                        end = Exp::prod(Var::Unused, positive.into(), end);
                    }
                    ParamCst::Simple((var, a)) => end = Exp::prod(var, a, end),
                }
            }
            end
        }
    }
    impl Positive {
        pub fn parameter(&self) -> &Vec<(Var, Exp)> {
            &self.parameter
        }
        pub fn exps(&self) -> &Vec<Exp> {
            &self.exps
        }
        pub fn subst(&self, e: Exp) -> Exp {
            let Positive {
                parameter,
                variable: _,
                exps,
            } = self.clone();
            assoc_prod(parameter, assoc_apply(e, exps))
        }
        pub fn new(
            variable: Var,
            parameter: Vec<(Var, Exp)>,
            exps: Vec<Exp>,
        ) -> Result<Self, String> {
            for (_, a) in &parameter {
                // a.free_variables() <=(subset) allow
                if a.free_variable().contains(&variable) {
                    return Err(format!("pos param {a:?} contains {variable:?}"));
                }
            }

            for e in &exps {
                if e.free_variable().contains(&variable) {
                    return Err(format!("arg {e:?} contains {variable:?}"));
                }
            }

            let positive = Positive {
                variable,
                parameter,
                exps,
            };

            Ok(positive)
        }
    }

    impl From<Positive> for Exp {
        fn from(
            Positive {
                variable,
                parameter,
                exps,
            }: Positive,
        ) -> Self {
            assoc_prod(parameter, assoc_apply(Exp::Var(variable), exps))
        }
    }

    impl ConstructorType {
        pub fn eliminator_type(&self, q: Exp, mut c: Exp) -> Exp {
            let Self { end, params } = self;

            let mut usable_fresh_var: usize = {
                let end_fresh = end.1.iter().map(fresh).max().unwrap_or(0);
                let params_fresh = params
                    .iter()
                    .map(|p| match p {
                        ParamCst::Positive(positive) => {
                            let positive: Exp = positive.clone().into();
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
                        let Positive {
                            variable: _,
                            parameter,
                            exps,
                        } = positive.clone();
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
                        pre_params.push((new_var_p.clone(), positive.clone().into()));
                        pre_params.push((Var::Unused, qmpx_type));
                        c = Exp::App(Box::new(c), Box::new(Exp::Var(new_var_p)));
                    }
                    ParamCst::Simple((x, a)) => {
                        pre_params.push((x.clone(), a.clone()));
                        c = Exp::App(Box::new(c), Box::new(Exp::Var(x.clone())));
                    }
                }
            }

            let res = Exp::App(Box::new(assoc_apply(q, end.1.to_owned())), Box::new(c));
            utils::assoc_prod(pre_params, res)
        }

        pub fn recursor(&self, ff: Exp, mut f: Exp) -> Exp {
            let Self { end, params } = self;

            let mut usable_fresh_var = {
                let end_fresh = end.1.iter().map(fresh).max().unwrap_or(0);
                let params_fresh = params
                    .iter()
                    .map(|p| match p {
                        ParamCst::Positive(positive) => {
                            let positive: Exp = positive.clone().into();
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
                        let Positive {
                            variable: _,
                            parameter,
                            exps,
                        } = positive.clone();
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
                        pre_params.push((new_var_p, positive.clone().into()));
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
                arity,
                constructors,
            }: crate::ast::inductives::InductiveDefinitionsSyntax,
        ) -> Result<Self, String> {
            use crate::ast::inductives::*;
            use crate::environment::inductive::*;
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
                            exps.remove(0);
                            let positive =
                                Positive::new(type_name_variable.clone(), parameter, exps)?;
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

                let cstype = ConstructorType::new_constructor(
                    (type_name_variable.clone(), end),
                    new_params,
                )?
                .0;

                cs_name_type.push((cs_name.into(), cstype));
            }

            Ok(IndTypeDefs {
                name: type_name.as_str().to_owned().into(),
                variable: type_name.as_str().into(),
                arity,
                constructors: cs_name_type,
            })
        }
        pub fn name(&self) -> &TypeName {
            &self.name
        }
        pub fn variable(&self) -> &Var {
            &self.variable
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
            self.constructors.iter().find_map(|(name, exp)| {
                if name == constructor_name {
                    Some(exp.clone().into())
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
                    );
                    let exact = crate::lambda_calculus::subst(
                        pre,
                        self.variable(),
                        &Exp::IndTypeType {
                            ind_type_name: self.name().clone(),
                        },
                    );
                    v.push((cname.to_string().into(), exact));
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
        let constructor_exp: Exp = constructor_def.clone().into();
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
