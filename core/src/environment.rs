use crate::{
    ast::*,
    lambda_calculus::*,
    typing::{type_check, type_infered_to_sort},
};
use std::fmt::Display;

use self::utils::{assoc_apply, assoc_lam, assoc_prod, decompose_to_app_exps};

pub mod derivation_tree;
pub mod global_context;
pub mod interpreter;
pub mod printing;
pub mod tree_node;

use derivation_tree::*;
use global_context::*;
use interpreter::*;
use tree_node::*;

pub mod check_well_formed {
    use self::inductives::InductiveDefinitionsSyntax;

    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum ResIndDefsError {
        AlreadyDefinedType,
        SyntaxError(String),
        ArityNotWellformed(DerivationFailed),
        ConstructorNotWellFormed(Vec<Result<PartialDerivationTreeTypeCheck, DerivationFailed>>),
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct ResIndDefsOk {
        pub arity_well_formed: PartialDerivationTreeTypeCheck,
        pub constructor_wellformed: Vec<PartialDerivationTreeTypeCheck>,
    }

    pub fn check_well_formedness_new_definition(
        gcxt: &GlobalContext,
        cxt: LocalContext,
        x: Var,
        a: Exp,
        v: Exp,
    ) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
        match type_check(gcxt, cxt, v.clone(), a.clone()) {
            Ok(der_tree) => Ok(der_tree),
            Err(err) => Err(err),
        }
    }

    pub fn check_well_formedness_new_assmption(
        gcxt: &GlobalContext,
        cxt: LocalContext,
        x: Var,
        a: Exp,
    ) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
        match type_infered_to_sort(gcxt, cxt, a.clone()) {
            Ok((der_tree, _)) => Ok(der_tree),
            Err(err) => Err(err),
        }
    }

    pub fn check_well_formedness_new_inddefs(
        gcxt: &GlobalContext,
        cxt: LocalContext,
        defs: inductive::IndTypeDefs,
    ) -> Result<ResIndDefsOk, ResIndDefsError> {
        if gcxt
            .indtype_defs()
            .iter()
            .any(|inddefs| inddefs.name() == defs.name())
        {
            return Err(ResIndDefsError::AlreadyDefinedType);
        }

        // arity の well defined
        let arity_well_formed =
            match type_infered_to_sort(gcxt, LocalContext::default(), defs.arity_as_exp()) {
                Ok((der_tree, _)) => der_tree,
                Err(err) => return Err(ResIndDefsError::ArityNotWellformed(err)),
            };

        let mut constructor_well_formed = vec![];
        let mut flag = true;

        // 各 constructor の well defined
        for (_, c) in defs.constructors() {
            let sort = defs.sort();
            let mut cxt = LocalContext::default();
            let (x, a) = (defs.variable().clone(), defs.arity_as_exp());
            cxt.push_decl((x, a));
            let constructor: Exp = c.clone().into();
            match type_check(gcxt, cxt, constructor, Exp::Sort(sort)) {
                Ok(der_tree) => {
                    constructor_well_formed.push(Ok(der_tree));
                }
                Err(err) => {
                    flag = false;
                    constructor_well_formed.push(Err(err));
                }
            };
        }

        if !flag {
            Err(ResIndDefsError::ConstructorNotWellFormed(
                constructor_well_formed,
            ))
        } else {
            Ok(ResIndDefsOk {
                arity_well_formed,
                constructor_wellformed: constructor_well_formed
                    .into_iter()
                    .map(|res| res.unwrap())
                    .collect(),
            })
        }
    }
}
