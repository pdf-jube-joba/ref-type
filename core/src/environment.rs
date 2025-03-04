use crate::{
    computation::{
        lambda_calculus::*,
        typing::{type_check, type_infered_to_sort},
    },
    syntax::ast::*,
    utils::*,
};
use std::fmt::Display;

pub mod derivation_tree;
pub mod global_context;
pub mod tree_node;

use derivation_tree::*;
use global_context::*;
use tree_node::*;

pub mod check_well_formed {

    use crate::{computation::typing::type_infer, utils};

    use self::inductive::cstr_into_exp_with_assign;

    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum ResIndDefsError {
        AlreadyDefinedType,
        SyntaxError(String),
        ParameterNotWellFormed(DerivationFailed),
        ArityNotWellformed(DerivationFailed),
        ConstructorNotWellFormed(Vec<Result<PartialDerivationTreeTypeCheck, DerivationFailed>>),
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct ResIndDefsOk {
        pub parameters_well_formed: Vec<PartialDerivationTreeTypeCheck>,
        pub arity_well_formed: PartialDerivationTreeTypeCheck,
        pub constructor_wellformed: Vec<PartialDerivationTreeTypeCheck>,
    }

    pub fn check_well_formedness_new_definition(
        gcxt: &GlobalContext,
        cxt: LocalContext,
        _x: Var,
        a: Exp,
        v: Exp,
    ) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
        type_check(gcxt, cxt, v.clone(), a.clone())
    }

    pub fn check_well_formedness_new_assmption(
        gcxt: &GlobalContext,
        cxt: LocalContext,
        _x: Var,
        a: Exp,
    ) -> Result<PartialDerivationTreeTypeCheck, DerivationFailed> {
        match type_infered_to_sort(gcxt, cxt, a.clone()) {
            Ok((der_tree, _)) => Ok(der_tree),
            Err(err) => Err(err),
        }
    }

    pub fn check_well_formedness_new_inddefs(
        gcxt: &GlobalContext,
        defs: inductive::IndTypeDefs,
    ) -> Result<ResIndDefsOk, ResIndDefsError> {
        if gcxt
            .indtype_defs()
            .iter()
            .any(|inddefs| inddefs.name() == defs.name())
        {
            return Err(ResIndDefsError::AlreadyDefinedType);
        }
        let mut local_context = LocalContext::default();
        // parameter の well formred
        let mut parameters_well_formed = vec![];
        for (x, a) in defs.parameters() {
            match type_infer(gcxt, local_context.clone(), a.clone()) {
                Ok(tree) => {
                    parameters_well_formed.push(tree);
                    local_context.push_decl((x.clone(), a.clone()));
                }
                Err(err) => {
                    return Err(ResIndDefsError::ParameterNotWellFormed(err));
                }
            }
        }

        // arity の well defined
        let arity_well_formed =
            match type_infered_to_sort(gcxt, local_context.clone(), defs.arity_as_exp()) {
                Ok((der_tree, _)) => der_tree,
                Err(err) => return Err(ResIndDefsError::ArityNotWellformed(err)),
            };

        let mut constructor_well_formed = vec![];
        let mut flag = true;

        // 各 constructor の well defined
        for (_, c) in defs.constructors() {
            let sort = defs.sort();
            let mut cxt = local_context.clone();
            let type_of_this = utils::assoc_prod(defs.parameters().clone(), defs.arity_as_exp());
            let (x, a) = (defs.name_as_var(), type_of_this);
            cxt.push_decl((x.clone(), a));
            let constructor: Exp = cstr_into_exp_with_assign(c.clone(), x.into());
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
                parameters_well_formed,
                arity_well_formed,
                constructor_wellformed: constructor_well_formed
                    .into_iter()
                    .map(|res| res.unwrap())
                    .collect(),
            })
        }
    }
}
