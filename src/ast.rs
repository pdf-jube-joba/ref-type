use std::fmt::Display;

// use crate::relation::{
//     subst, type_check, type_infered_to_sort, Context, PartialDerivationTree, StatePartialTree,
// };

pub mod parse;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeName(String);

impl<S> From<S> for TypeName
where
    S: AsRef<str>,
{
    fn from(value: S) -> Self {
        TypeName(value.as_ref().to_string())
    }
}

impl Display for TypeName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorName(String);

impl<S> From<S> for ConstructorName
where
    S: AsRef<str>,
{
    fn from(value: S) -> Self {
        ConstructorName(value.as_ref().to_string())
    }
}

impl Display for ConstructorName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exp {
    Sort(Sort),
    Var(Var),
    Prod(Var, Box<Exp>, Box<Exp>),
    Lam(Var, Box<Exp>, Box<Exp>),
    App(Box<Exp>, Box<Exp>),
    // inductive hoge は global context を見ながらやること
    // 型 T
    IndTypeType {
        ind_type_name: TypeName,
    },
    // 型 T のコンストラクタ C の指定
    IndTypeCst {
        ind_type_name: TypeName,
        constructor_name: ConstructorName,
    },
    // Elim(T, c, Q){f[0], ..., f[m]}
    IndTypeElim {
        ind_type_name: TypeName,
        eliminated_exp: Box<Exp>,
        return_type: Box<Exp>,
        cases: Vec<(ConstructorName, Exp)>,
    },
    // これがほしいメインの部分
    Proof(Box<Exp>),              // Proof t
    Sub(Var, Box<Exp>, Box<Exp>), // { x : A | P }
    Pow(Box<Exp>),                // Power X
    Pred(Box<Exp>, Box<Exp>),     // Pred X
                                  // Id(Box<Exp>, Box<Exp>, Box<Exp>), // a =_A b
                                  // Refl(Box<Exp>, Box<Exp>),         // refl_A a
                                  // Take(Var, Box<Exp>, Box<Exp>),    // take x:A. t
                                  // Rec(Var, Var, Box<Exp>), // rec f x = m
}

impl Display for Exp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s: String = match self {
            Exp::Sort(sort) => format!("{sort}"),
            Exp::Var(var) => format!("{var}"),
            Exp::Prod(var, exp, exp1) => format!("({var}:{exp}) -> {exp1}"),
            Exp::Lam(var, exp, exp1) => format!("\\{var}:{exp}. {exp1}"),
            Exp::App(exp, exp1) => format!("({exp} {exp1})"),
            Exp::IndTypeType { ind_type_name } => ind_type_name.to_string(),
            Exp::IndTypeCst {
                ind_type_name,
                constructor_name,
            } => format!("{ind_type_name}::{constructor_name}"),
            Exp::IndTypeElim {
                ind_type_name,
                eliminated_exp,
                return_type,
                cases,
            } => {
                format!(
                    "elim({ind_type_name}) {eliminated_exp} return {return_type} with {} end",
                    cases
                        .iter()
                        .fold(String::new(), |s, (c, e)| { format!("{s} | {c} => {e} ") }),
                )
            }
            Exp::Proof(t) => format!("Proof {t}"),
            Exp::Sub(x, a, p) => format!("{{ {x}: {a}: {p} }}"),
            Exp::Pow(a) => format!("Power({a})"),
            Exp::Pred(a, b) => format!("Pred {a} {b}"),
            // Exp::Id(t, a, b) => format!("Id({t}) {a} = {b}"),
            // Exp::Refl(t, a) => format!("Refl({t}) {a}"),
            // Exp::Take(x, m, t) => format!("take {x}:{m}. {t}"),
        };
        write!(f, "{}", s)
    }
}

impl Exp {
    pub fn prod(var: Var, a: Exp, b: Exp) -> Self {
        Exp::Prod(var, Box::new(a), Box::new(b))
    }
    pub fn lambda(var: Var, a: Exp, b: Exp) -> Self {
        Exp::Lam(var, Box::new(a), Box::new(b))
    }
    pub fn indtype(type_name: String) -> Self {
        Self::IndTypeType {
            ind_type_name: type_name.into(),
        }
    }
    pub fn indcst(ind_type_name: String, constructor_name: String) -> Self {
        Self::IndTypeCst {
            ind_type_name: ind_type_name.into(),
            constructor_name: constructor_name.into(),
        }
    }
    pub fn indelim(
        ind_type_name: String,
        eliminated_exp: Exp,
        return_type: Exp,
        cases: Vec<(String, Exp)>,
    ) -> Self {
        Self::IndTypeElim {
            ind_type_name: ind_type_name.into(),
            eliminated_exp: Box::new(eliminated_exp),
            return_type: Box::new(return_type),
            cases: cases.into_iter().map(|(c, e)| (c.into(), e)).collect(),
        }
    }
}

pub mod utils {
    use super::*;

    #[macro_export]
    macro_rules! var {
        ($v: expr) => {{
            {
                Exp::Var($v.into())
            }
        }};
    }

    #[macro_export]
    macro_rules! lam {
        ($x: expr, $a: expr, $b: expr) => {{
            Exp::Lam($x, Box::new($a), Box::new($b))
        }};
    }

    #[macro_export]
    macro_rules! prod {
        ($x: expr, $a: expr, $b: expr) => {{
            Exp::Prod($x, Box::new($a), Box::new($b))
        }};
    }

    #[macro_export]
    macro_rules! app {
        ($e: expr, $($x: expr),* ) => {{
            #[allow(unused_mut)]
            let mut e: Exp = $e;
            $(
                e = Exp::App(Box::new(e), Box::new($x));
            )*
            e
        }};
    }

    // (a v[0] ... v[k])
    pub fn assoc_apply(mut a: Exp, v: Vec<Exp>) -> Exp {
        for v in v {
            a = Exp::App(Box::new(a), Box::new(v))
        }
        a
    }

    // (x[0]: t[0]) -> ... (x[k]: t[k]) -> e
    pub fn assoc_prod(mut v: Vec<(Var, Exp)>, mut e: Exp) -> Exp {
        while let Some((x, a)) = v.pop() {
            e = Exp::Prod(x, Box::new(a), Box::new(e));
        }
        e
    }

    // \ x[0]: t[0]). ... (x[k]: t[k]). e
    pub fn assoc_lam(mut v: Vec<(Var, Exp)>, mut e: Exp) -> Exp {
        while let Some((x, a)) = v.pop() {
            e = Exp::Lam(x, Box::new(a), Box::new(e));
        }
        e
    }

    // e = (((...((e1 e2) e3) ... e(n-1) ) e(n) ) |-> (e1, [e2, ..., en])
    pub fn decompose_to_app_exps(mut e: Exp) -> (Exp, Vec<Exp>) {
        let mut v = vec![];
        while let Exp::App(t1, t2) = e {
            v.push(*t2);
            e = *t1;
        }
        v.reverse();
        (e, v)
    }

    pub fn decompose_to_prod_exps(mut e: Exp) -> (Vec<(Var, Exp)>, Exp) {
        let mut v = vec![];
        while let Exp::Prod(x, a, b) = e {
            v.push((x, *a));
            e = *b;
        }
        (v, e)
    }

    pub fn decompose_to_lam_exps(mut e: Exp) -> (Vec<(Var, Exp)>, Exp) {
        let mut v = vec![];
        while let Exp::Lam(x, a, b) = e {
            v.push((x, *a));
            e = *b;
        }
        (v, e)
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn macros() {
            assert_eq!(var! {"a"}, Exp::Var("a".into()));
            assert_eq!(
                lam! { "a".into(), var!{"b"}, var!{"c"} },
                Exp::Lam(
                    "a".into(),
                    Box::new(Exp::Var("b".into())),
                    Box::new(Exp::Var("c".into()))
                )
            );
            assert_eq!(
                prod!("a".into(), var! {"b"}, var! {"c"}),
                Exp::Prod(
                    "a".into(),
                    Box::new(Exp::Var("b".into())),
                    Box::new(Exp::Var("c".into()))
                )
            );
            assert_eq!(app!(var! {"a"},), Exp::Var("a".into()));
            assert_eq!(
                app!(var! {"a"}, var! {"b"}, var! {"c"}),
                Exp::App(
                    Box::new(Exp::App(
                        Box::new(Exp::Var("a".into())),
                        Box::new(Exp::Var("b".into()))
                    )),
                    Box::new(Exp::Var("c".into()))
                )
            );
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Var {
    Str(String),
    Internal(String, usize),
    Unused,
}

pub fn fresh_var(v: &Var) -> usize {
    match v {
        Var::Str(_) => 0,
        Var::Internal(_, i) => *i + 1,
        Var::Unused => 0,
    }
}

// term に含まれるどの変数よりも大きい数を返す
pub fn fresh(term: &Exp) -> usize {
    match term {
        Exp::Sort(_) => 0,
        Exp::Var(v) => fresh_var(v),
        Exp::Prod(x, t1, t2) => {
            let v1 = fresh(t1);
            let v2 = fresh(t2);
            let v = std::cmp::max(v1, v2);
            std::cmp::max(fresh_var(x), v)
        }
        Exp::Lam(x, t1, t2) => {
            let v1 = fresh(t1);
            let v2 = fresh(t2);
            let v = std::cmp::max(v1, v2);
            std::cmp::max(fresh_var(x), v)
        }
        Exp::App(t1, t2) => {
            let v1 = fresh(t1);
            let v2 = fresh(t2);
            std::cmp::max(v1, v2)
        }
        Exp::IndTypeType { ind_type_name } => 0,
        Exp::IndTypeCst {
            ind_type_name,
            constructor_name,
        } => 0,
        Exp::IndTypeElim {
            ind_type_name,
            eliminated_exp,
            return_type,
            cases,
        } => cases
            .iter()
            .map(|(_, e)| e)
            .chain(vec![eliminated_exp.as_ref(), return_type.as_ref()])
            .map(|e| fresh(e))
            .max()
            .unwrap(),
        Exp::Proof(t) => fresh(t),
        Exp::Sub(x, t1, t2) => {
            let v1 = fresh(t1);
            let v2 = fresh(t2);
            let v = std::cmp::max(v1, v2);
            std::cmp::max(fresh_var(x), v)
        }
        Exp::Pow(t) => fresh(t),
        Exp::Pred(a, b) => std::cmp::max(fresh(&a), fresh(b)),
    }
}

impl<S> From<S> for Var
where
    S: AsRef<str>,
{
    fn from(value: S) -> Self {
        Var::Str(value.as_ref().to_string())
    }
}

impl From<Var> for Exp {
    fn from(value: Var) -> Self {
        Exp::Var(value)
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Var::Str(s) => format!("[{s}]"),
                Var::Internal(s, n) => format!("[{s}_{n}]"),
                Var::Unused => "_".to_string(),
            }
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sort {
    Univ, // universe
    Set,
    Prop,
    Type, // for program
}

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Sort::Set => "SET",
            Sort::Univ => "UNIV",
            Sort::Prop => "PROP",
            Sort::Type => "TYPE",
        };
        write!(f, "{}", s)
    }
}

impl From<Sort> for Exp {
    fn from(value: Sort) -> Self {
        Exp::Sort(value)
    }
}

// functional なものしか考えないのでよい。
impl Sort {
    // functional なので、
    // (s1, s2) in A な s2 は s1 に対して一意 ... それを返す。
    pub fn type_of_sort(self) -> Option<Self> {
        if matches!(self, Sort::Prop | Sort::Set) {
            Some(Sort::Univ)
        } else {
            None
        }
    }

    // functional なので、
    // (s1, s2, s3) in R な s3 は (s1, s2) に対して一意 ... それを返す。
    pub fn relation_of_sort(self, other: Self) -> Option<Self> {
        match (self, other) {
            // CoC 部分
            (Sort::Prop, Sort::Prop) => Some(Sort::Prop),
            (Sort::Univ, Sort::Univ) => Some(Sort::Univ),
            (Sort::Univ, Sort::Prop) => Some(Sort::Prop),
            (Sort::Prop, Sort::Univ) => Some(Sort::Univ),
            // Set を入れる部分
            (Sort::Set, Sort::Set) => Some(Sort::Set),
            (Sort::Set, Sort::Univ) => Some(Sort::Univ),
            (Sort::Set, Sort::Prop) => Some(Sort::Prop),
            (Sort::Prop, Sort::Set) => None,
            (Sort::Univ, Sort::Set) => None, // Set は predicative
            // Type を入れる部分
            (Sort::Type, Sort::Type) => Some(Sort::Type),
            (Sort::Type, Sort::Univ) => Some(Sort::Univ),
            (Sort::Univ, Sort::Type) => Some(Sort::Type),
            (Sort::Type, _) => None,
            (_, Sort::Type) => None,
        }
    }

    // elimination の制限用
    pub fn ind_type_rel(self, other: Self) -> Option<()> {
        match (self, other) {
            (Sort::Prop, Sort::Prop) | (Sort::Set, Sort::Prop) | (Sort::Univ, Sort::Prop) => {
                Some(())
            }
            (Sort::Univ, Sort::Univ) | (Sort::Set, Sort::Univ) | (Sort::Prop, Sort::Univ) => {
                Some(())
            }
            (Sort::Set, Sort::Set) => Some(()),
            _ => None,
        }
    }
}

// inductive definition には自由変数がないことを仮定する
pub mod inductives {
    use super::{utils::*, *};

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Arity {
        signature: Vec<(Var, Exp)>,
        sort: Sort,
    }

    impl Arity {
        pub fn new(signature: Vec<(Var, Exp)>, sort: Sort) -> Result<Self, String> {
            let arity = Arity { signature, sort };
            let as_exp: Exp = arity.clone().into();
            if as_exp.free_variable().is_empty() {
                Ok(arity)
            } else {
                Err(format!("arity {arity:?} contains free variables"))
            }
        }
        pub fn signature(&self) -> &Vec<(Var, Exp)> {
            &self.signature
        }
        pub fn sort(&self) -> &Sort {
            &self.sort
        }
        pub fn arg_num(&self) -> usize {
            self.signature.len()
        }
    }

    impl From<Arity> for Exp {
        fn from(Arity { signature, sort }: Arity) -> Self {
            assoc_prod(signature, Exp::Sort(sort))
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct IndTypeDefs {
        type_name: TypeName,
        variable: Var,
        arity: Arity,
        constructor: Vec<(ConstructorName, ConstructorType)>,
    }

    impl IndTypeDefs {
        pub fn new(
            type_name: String,
            variable: Var,
            (signature, sort): (Vec<(Var, Exp)>, Sort),
            constructor: Vec<(String, ConstructorType)>,
        ) -> Result<Self, String> {
            let arity = Arity::new(signature, sort)?;
            Ok(Self {
                type_name: type_name.into(),
                variable,
                arity,
                constructor: constructor
                    .into_iter()
                    .map(|(c, t)| (c.into(), t))
                    .collect(),
            })
        }
        pub fn name(&self) -> &TypeName {
            &self.type_name
        }
        pub fn variable(&self) -> &Var {
            &self.variable
        }
        pub fn arity(&self) -> &Arity {
            &self.arity
        }
        pub fn constructors(&self) -> &Vec<(ConstructorName, ConstructorType)> {
            &self.constructor
        }
        pub fn constructor(&self, constructor_name: &ConstructorName) -> Option<&ConstructorType> {
            self.constructor.iter().find_map(|(cname, c)| {
                if cname == constructor_name {
                    Some(c)
                } else {
                    None
                }
            })
        }
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
                    ParamCst::Positive(positive) => {}
                    ParamCst::Simple((x, a)) => {}
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

    // variable = X, parameter = [(y_1, M_1), ..., (y_k, M_k)], exps = [N_1, ... N_l]
    // => (y_1: M_1) -> ... -> (y_k: M_k) -> (X N_1 ... N_l)
    // free variable of Pos is only X
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Positive {
        parameter: Vec<(Var, Exp)>,
        variable: Var,
        exps: Vec<Exp>,
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
                let end_fresh = end.1.iter().map(|e| fresh(e)).max().unwrap_or(0);
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
                let end_fresh = end.1.iter().map(|e| fresh(e)).max().unwrap_or(0);
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
}

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct LocalContext(Vec<(Var, Exp)>);

// impl LocalContext {
//     fn search_var(&self, var: &Var) -> Option<&(Var, Exp)> {
//         self.0.iter().find(|(v, e)| v == var)
//     }
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct ProvableJudgement {
//     context: LocalContext,
//     proposition: Exp,
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct TypeCheckJudgement {
//     context: LocalContext,
//     term: Exp,
//     type_of_term: Exp,
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum Judgement {
//     Proof(ProvableJudgement),
//     Type(TypeCheckJudgement),
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum DerivationLabel {
//     Variable,
//     Axiom,
//     Conversion,
//     ProdForm,
//     ProdIntro,
//     ProdElim,
// }

// impl Condition {
//     fn is_well_formed(&self) -> bool {
//         match self {
//             Condition::VariableinContext(_, _) => todo!(),
//             Condition::Convertible(_, _) => todo!(),
//             Condition::SortAxiom(_, _, _) => todo!(),
//             Condition::SortRelation(_, _, _) => todo!(),
//             Condition::SortInductive(_, _, _) => todo!(),
//         }
//     }
//     fn var_cxt(gcxt: &GlobalContext, cxt: LocalContext, var: Var) -> Option<(Self, Exp)> {
//         let v_e = cxt.search_var(&var)?.clone();
//         Some((
//             Condition::VariableinContext(cxt, v_e.clone()),
//             v_e.1.clone(),
//         ))
//     }
//     fn reduce_to_sort(gcxt: &GlobalContext, term: Exp) -> Option<(Self, Sort)> {
//         todo!()
//     }
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum ExtraInfo {
//     Err(String),
//     GeneratedBy(String),
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct DerivationTree {
//     head: Judgement,
//     label: DerivationLabel,
//     extra: ExtraInfo,
//     child: Vec<Either<DerivationTree, Condition>>,
// }

// impl DerivationTree {
//     pub fn is_well_formed(&self) -> Option<Vec<ProvableJudgement>> {
//         let DerivationTree {
//             head,
//             label,
//             extra,
//             child,
//         } = self;
//         match label {
//             DerivationLabel::Variable => todo!(),
//             DerivationLabel::Axiom => todo!(),
//             DerivationLabel::Conversion => todo!(),
//             DerivationLabel::ProdForm => todo!(),
//             DerivationLabel::ProdIntro => todo!(),
//             DerivationLabel::ProdElim => todo!(),
//         }
//     }
// }

// #[cfg(test)]
// mod tests {
//     use crate::relation::alpha_eq;

//     use super::*;
//     use inductives::*;
//     #[test]
//     fn eliminator_and_recursor() {
//         let q_exp = Exp::Var("Q".into());
//         let c_exp = Exp::Var("c".into());
//         let f_exp = Exp::Var("f".into());
//         let ff_exp = Exp::Var("F".into());

//         // X
//         let c = ConstructorType::new_constructor(("X".into(), vec![]), vec![])
//             .unwrap()
//             .0;
//         assert!(alpha_eq(
//             &c.eliminator_type(q_exp.clone(), c_exp.clone()),
//             // q c
//             &Exp::App(Box::new(q_exp.clone()), Box::new(c_exp.clone())),
//         ));

//         // X m_1 m_2
//         let c = ConstructorType::new_constructor(
//             (
//                 "X".into(),
//                 vec![Exp::Var("m1".into()), Exp::Var("m2".into())],
//             ),
//             vec![],
//         )
//         .unwrap()
//         .0;
//         // q m_1 m_2 c
//         let expected = {
//             Exp::App(
//                 Box::new(utils::assoc_apply(
//                     q_exp.clone(),
//                     vec![Exp::Var("m1".into()), Exp::Var("m2".into())],
//                 )),
//                 Box::new(c_exp.clone()),
//             )
//         };
//         assert!(alpha_eq(
//             &c.eliminator_type(q_exp.clone(), c_exp.clone()),
//             &expected,
//         ));
//         // f
//         let expected = { f_exp.clone() };
//         assert!(alpha_eq(
//             &c.recursor(ff_exp.clone(), f_exp.clone()),
//             &expected,
//         ));

//         // simple(l1: L1) -> simple(l2: L2) -> X m1 m2
//         let c = ConstructorType::new_constructor(
//             (
//                 "X".into(),
//                 vec![Exp::Var("m1".into()), Exp::Var("m2".into())],
//             ),
//             vec![
//                 ParamCst::Simple(("l1".into(), Exp::Var("L1".into()))),
//                 ParamCst::Simple(("l2".into(), Exp::Var("L2".into()))),
//             ],
//         )
//         .unwrap()
//         .0;
//         // xi(Q, c, simple(l1: L1) -> simple(l2: L2) -> X m1 m2)
//         // (l1: L2) -> xi(Q, (c l1), simple(l2: L2) -> X m1 m2)
//         // => (l1: L1) -> (l2: L2) -> xi(Q, ((c l1) l2), X m1 m2)
//         // => (l1: L2) -> (l2: L2) -> Q m1 m2 ((c l1) l2)
//         let expected = {
//             let cl1l2 = utils::assoc_apply(
//                 c_exp.clone(),
//                 vec![Exp::Var("l1".into()), Exp::Var("l2".into())],
//             );
//             let qm1m2 = utils::assoc_apply(
//                 q_exp.clone(),
//                 vec![Exp::Var("m1".into()), Exp::Var("m2".into())],
//             );
//             let a = Exp::App(Box::new(qm1m2), Box::new(cl1l2));
//             utils::assoc_prod(
//                 vec![
//                     ("l1".into(), Exp::Var("L1".into())),
//                     ("l2".into(), Exp::Var("L2".into())),
//                 ],
//                 a,
//             )
//         };
//         assert!(alpha_eq(
//             &c.eliminator_type(q_exp.clone(), c_exp.clone()),
//             &expected,
//         ));
//         // mu(F, f, simple(l1: L1) -> simple(l2: L2) -> X m1 m2)
//         // => \l1: L1. mu(F, f l1, simple(l2: L2) -> X m1 m2)
//         // => \l1: L1. \l2: L2. mu(F, ((f l1) l2), X m1 m2)
//         // => \l1: L2. \l2: L2. ((f l1) l2)
//         let expected = {
//             let fl1l2 = utils::assoc_apply(
//                 f_exp.clone(),
//                 vec![Exp::Var("l1".into()), Exp::Var("l2".into())],
//             );
//             utils::assoc_lam(
//                 vec![
//                     ("l1".into(), Exp::Var("L1".into())),
//                     ("l2".into(), Exp::Var("L2".into())),
//                 ],
//                 fl1l2,
//             )
//         };
//         assert!(alpha_eq(
//             &c.recursor(ff_exp.clone(), f_exp.clone()),
//             &expected,
//         ));
//     }
//     #[test]
//     fn eliminator_and_recursor_positivecase() {
//         let q_exp = Exp::Var("Q".into());
//         let c_exp = Exp::Var("c".into());
//         let f_exp = Exp::Var("f".into());
//         let ff_exp = Exp::Var("F".into());
//         // positive(X t1 t2)
//         let positive1 = Positive::new(
//             "X".into(),
//             vec![],
//             vec![Exp::Var("t1".into()), Exp::Var("t2".into())],
//         )
//         .unwrap();

//         // positive(X t1 t2) -> X m1 m2
//         let c = ConstructorType::new_constructor(
//             (
//                 "X".into(),
//                 vec![Exp::Var("m1".into()), Exp::Var("m2".into())],
//             ),
//             vec![ParamCst::Positive(positive1.clone())],
//         )
//         .unwrap()
//         .0;

//         // (p: (X t1 t2)) -> (_: Q t1 t2 p) -> Q m1 m2 (c p)
//         let expected_elimtype: Exp = {
//             let p_var: Var = "p".into();
//             let qtpx = utils::assoc_apply(
//                 q_exp.clone(),
//                 vec![
//                     Exp::Var("t1".into()),
//                     Exp::Var("t2".into()),
//                     Exp::Var(p_var.clone()),
//                 ],
//             );
//             let qmcp = utils::assoc_apply(
//                 q_exp.clone(),
//                 vec![
//                     Exp::Var("m1".into()),
//                     Exp::Var("m2".into()),
//                     Exp::App(Box::new(c_exp.clone()), Box::new(Exp::Var(p_var.clone()))),
//                 ],
//             );
//             utils::assoc_prod(
//                 vec![
//                     (
//                         p_var.clone(),
//                         utils::assoc_apply(
//                             Exp::Var("X".into()),
//                             vec![Exp::Var("t1".into()), Exp::Var("t2".into())],
//                         ),
//                     ),
//                     (Var::Unused, qtpx),
//                 ],
//                 qmcp,
//             )
//         };
//         println!("{}", c.eliminator_type(q_exp.clone(), c_exp.clone()));
//         println!("{}", expected_elimtype);
//         assert!(alpha_eq(
//             &c.eliminator_type(q_exp.clone(), c_exp.clone()),
//             &expected_elimtype
//         ));

//         // \p: X t1 t2. f p (F t1 t2 p)
//         let expected_recursor = {
//             let p_var: Var = "p".into();
//             let ffmpx = {
//                 utils::assoc_apply(
//                     ff_exp.clone(),
//                     vec![
//                         Exp::Var("t1".into()),
//                         Exp::Var("t2".into()),
//                         Exp::Var(p_var.clone()),
//                     ],
//                 )
//             };
//             // F t1 t2 p
//             let lam_ffmpx = { ffmpx };
//             Exp::Lam(
//                 p_var.clone(),
//                 Box::new(positive1.clone().into()),
//                 Box::new(Exp::App(
//                     Box::new(Exp::App(Box::new(f_exp.clone()), Box::new(Exp::Var(p_var)))),
//                     Box::new(lam_ffmpx),
//                 )),
//             )
//         };
//         println!("{}", c.recursor(ff_exp.clone(), f_exp.clone()));
//         println!("{}", expected_recursor);
//         assert!(alpha_eq(
//             &c.recursor(ff_exp.clone(), f_exp.clone()),
//             &expected_recursor
//         ));
//     }
//     #[test]
//     fn eliminator_and_recursor_positivecase2() {
//         let q_exp = Exp::Var("Q".into());
//         let c_exp = Exp::Var("c".into());
//         let f_exp = Exp::Var("f".into());
//         let ff_exp = Exp::Var("F".into());

//         // positive(X t1)
//         let positive2 = Positive::new("X".into(), vec![], vec![Exp::Var("t1".into())]).unwrap();

//         // positive((l: L) -> X t2) -> X m
//         let positive3 = Positive::new(
//             "X".into(),
//             vec![("l".into(), Exp::Var("L".into()))],
//             vec![Exp::Var("t2".into())],
//         )
//         .unwrap();

//         // positive(X t1) -> positive((l: L) -> X t2) -> X m
//         let c = ConstructorType::new_constructor(
//             ("X".into(), vec![Exp::Var("m".into())]),
//             vec![
//                 ParamCst::Positive(positive2.clone()),
//                 ParamCst::Positive(positive3.clone()),
//             ],
//         )
//         .unwrap()
//         .0;

//         // (p1: X t1) -> (_: Q t1 p1) -> // positive(X t1)
//         //      xi(Q, c p1, positive((l: L) -> X t2) )
//         // -> (p2: (l: L) -> X t2) -> (_: (l: L) -> (Q t2 (p2 l)))
//         //      xi(Q, c p1 p2, X m)
//         // -> (Q m (c p1 p2))
//         let expected_elimtype: Exp = {
//             let mut params: Vec<(Var, Exp)> = vec![];
//             let new_p1: Var = "p1".into();
//             // p1: X t1
//             params.push((
//                 new_p1.clone(),
//                 utils::assoc_apply(Exp::Var("X".into()), vec![Exp::Var("t1".into())]),
//             ));
//             // _: Q t1 p1
//             params.push((
//                 Var::Unused,
//                 utils::assoc_apply(
//                     q_exp.clone(),
//                     vec![Exp::Var("t1".into()), Exp::Var(new_p1.clone())],
//                 ),
//             ));
//             let new_p2: Var = "p2".into();
//             // p2: (l: L) -> X t2
//             params.push((
//                 new_p2.clone(),
//                 Exp::prod(
//                     "l".into(),
//                     Exp::Var("L".into()),
//                     utils::assoc_apply(Exp::Var("X".into()), vec![Exp::Var("t2".into())]),
//                 ),
//             ));
//             // _: (l: L) -> (Q t2 (p2 l))
//             params.push((
//                 Var::Unused,
//                 Exp::prod(
//                     "l".into(),
//                     Exp::Var("L".into()),
//                     utils::assoc_apply(
//                         q_exp.clone(),
//                         vec![
//                             Exp::Var("t2".into()),
//                             utils::assoc_apply(
//                                 Exp::Var(new_p2.clone()),
//                                 vec![Exp::Var("l".into())],
//                             ),
//                         ],
//                     ),
//                 ),
//             ));
//             // Q m (c p1 p2)
//             let qmcp = utils::assoc_apply(
//                 q_exp.clone(),
//                 vec![
//                     Exp::Var("m".into()),
//                     utils::assoc_apply(
//                         c_exp.clone(),
//                         vec![Exp::Var(new_p1.clone()), Exp::Var(new_p2.clone())],
//                     ),
//                 ],
//             );

//             utils::assoc_prod(params, qmcp)
//         };
//         println!("{}", expected_elimtype);
//         println!("{}", c.eliminator_type(q_exp.clone(), c_exp.clone()));
//         assert!(alpha_eq(
//             &expected_elimtype,
//             &c.eliminator_type(q_exp, c_exp)
//         ));

//         // mu(F, f, positive(X t1) -> positive((l: L) -> X t2) -> X m )
//         // \p1: X t1.
//         //      mu(F, f p (F t1 p1), positive((l: L) -> X t2) -> X m)
//         // \p2: (l: L) -> X t2.
//         //      mu(F, (f p (F t1 p1)) p2 (\l: L. F t2 (p2 l)), X m)
//         // (f p1 (F t1 p1)) p2 (\l: L. F t2 (p2 l))
//         let expected_recursor = {
//             let new_p1: Var = "p1".into();
//             let new_p2: Var = "p2".into();
//             // \l: L. F t2 (p2 l)
//             let p2_lam = Exp::lambda(
//                 "l".into(),
//                 Exp::Var("L".into()),
//                 utils::assoc_apply(
//                     ff_exp.clone(),
//                     vec![
//                         Exp::Var("t2".into()),
//                         utils::assoc_apply(Exp::Var(new_p2.clone()), vec![Exp::Var("l".into())]),
//                     ],
//                 ),
//             );
//             // F t1 p1
//             let p1_lam = utils::assoc_apply(
//                 ff_exp.clone(),
//                 vec![Exp::Var("t1".into()), Exp::Var(new_p1.clone())],
//             );
//             // f p1 (F t1 p1)
//             let fp1_lam = utils::assoc_apply(f_exp.clone(), vec![Exp::Var(new_p1.clone()), p1_lam]);
//             // (f p1 F t1 p1) p2 (\l:L. F t2 p2)
//             let end = utils::assoc_apply(fp1_lam, vec![Exp::Var(new_p2.clone()), p2_lam]);
//             utils::assoc_lam(
//                 vec![
//                     (new_p1, positive2.clone().into()),
//                     (new_p2, positive3.clone().into()),
//                 ],
//                 end,
//             )
//         };
//         let result = c.recursor(ff_exp.clone(), f_exp.clone());
//         println!("{}", expected_recursor);
//         println!("{}", result);
//         assert!(alpha_eq(&expected_recursor, &result,))
//     }
// }
