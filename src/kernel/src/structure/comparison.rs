//! Alpha/conversion comparison over each family's computational syntax.
use super::*;
pub(crate) fn compare_children(
    arena: &Arena,
    left: Expression,
    right: Expression,
    mut compare: impl FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    if left.family() != right.family() || arena.sort(left) != arena.sort(right) {
        return Ok(false);
    }
    match (left, right) {
        (Expression::SetTerm(l), Expression::SetTerm(r)) => {
            compare_set_term(arena, l, r, &mut compare)
        }
        (Expression::SetType(l), Expression::SetType(r)) => {
            compare_set_type(arena, l, r, &mut compare)
        }
        (Expression::SetKind(l), Expression::SetKind(r)) => {
            compare_set_kind(arena, l, r, &mut compare)
        }
        (Expression::PropTerm(l), Expression::PropTerm(r)) => {
            compare_prop_term(arena, l, r, &mut compare)
        }
        (Expression::PropType(l), Expression::PropType(r)) => {
            compare_prop_type(arena, l, r, &mut compare)
        }
        (Expression::PropKind(l), Expression::PropKind(r)) => {
            compare_prop_kind(arena, l, r, &mut compare)
        }
        (Expression::ValueTerm(l), Expression::ValueTerm(r)) => {
            compare_value_term(arena, l, r, &mut compare)
        }
        (Expression::ValueType(l), Expression::ValueType(r)) => {
            compare_value_type(arena, l, r, &mut compare)
        }
        (Expression::ValueKind(l), Expression::ValueKind(r)) => {
            compare_value_kind(arena, l, r, &mut compare)
        }
        (Expression::ComputationTerm(l), Expression::ComputationTerm(r)) => {
            compare_computation_term(arena, l, r, &mut compare)
        }
        (Expression::ComputationType(l), Expression::ComputationType(r)) => {
            compare_computation_type(arena, l, r, &mut compare)
        }
        (Expression::ComputationKind(l), Expression::ComputationKind(r)) => {
            compare_computation_kind(arena, l, r, &mut compare)
        }
        _ => Ok(false),
    }
}
fn compare_set_term(
    arena: &Arena,
    left: SetTerm,
    right: SetTerm,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (SetTermForm::Bound { index: index_l }, SetTermForm::Bound { index: index_r }) => {
            index_l == index_r
        }
        (
            SetTermForm::ModuleParam {
                parameter: parameter_l,
            },
            SetTermForm::ModuleParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            SetTermForm::Constant {
                definition: definition_l,
            },
            SetTermForm::Constant {
                definition: definition_r,
            },
        ) => definition_l == definition_r,
        (
            SetTermForm::ReflectedProgramParam {
                parameter: parameter_l,
            },
            SetTermForm::ReflectedProgramParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            SetTermForm::LambdaTerm {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            SetTermForm::LambdaTerm {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            SetTermForm::LambdaType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            SetTermForm::LambdaType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            SetTermForm::AppTerm {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            SetTermForm::AppTerm {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            SetTermForm::AppType {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            SetTermForm::AppType {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            SetTermForm::Subset {
                set: set_l,
                predicate: predicate_l,
                ..
            },
            SetTermForm::Subset {
                set: set_r,
                predicate: predicate_r,
                ..
            },
        ) => {
            compare((*set_l).into(), (*set_r).into())?
                && compare((*predicate_l).into(), (*predicate_r).into())?
        }
        (
            SetTermForm::SubsetIntro {
                superset: superset_l,
                subset: subset_l,
                element: element_l,
                proof: proof_l,
            },
            SetTermForm::SubsetIntro {
                superset: superset_r,
                subset: subset_r,
                element: element_r,
                proof: proof_r,
            },
        ) => {
            compare((*superset_l).into(), (*superset_r).into())?
                && compare((*subset_l).into(), (*subset_r).into())?
                && compare((*element_l).into(), (*element_r).into())?
                && compare((*proof_l).into(), (*proof_r).into())?
        }
        (
            SetTermForm::Continue {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                next: next_l,
            },
            SetTermForm::Continue {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                next: next_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*next_l).into(), (*next_r).into())?
        }
        (
            SetTermForm::Finish {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                output: output_l,
            },
            SetTermForm::Finish {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                output: output_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*output_l).into(), (*output_r).into())?
        }
        (
            SetTermForm::SetRun {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                step: step_l,
                initial: initial_l,
                ..
            },
            SetTermForm::SetRun {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                step: step_r,
                initial: initial_r,
                ..
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*step_l).into(), (*step_r).into())?
                && compare((*initial_l).into(), (*initial_r).into())?
        }
        (
            SetTermForm::SetRunCase {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                step: step_l,
                initial: initial_l,
                transition: transition_l,
                ..
            },
            SetTermForm::SetRunCase {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                step: step_r,
                initial: initial_r,
                transition: transition_r,
                ..
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*step_l).into(), (*step_r).into())?
                && compare((*initial_l).into(), (*initial_r).into())?
                && compare((*transition_l).into(), (*transition_r).into())?
        }
        (
            SetTermForm::Recursor {
                rule: rule_l,
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                motive: motive_l,
                on_continue: on_continue_l,
                on_finish: on_finish_l,
                scrutinee: scrutinee_l,
                ..
            },
            SetTermForm::Recursor {
                rule: rule_r,
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                motive: motive_r,
                on_continue: on_continue_r,
                on_finish: on_finish_r,
                scrutinee: scrutinee_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*motive_l).into(), (*motive_r).into())?
                && compare((*on_continue_l).into(), (*on_continue_r).into())?
                && compare((*on_finish_l).into(), (*on_finish_r).into())?
                && compare((*scrutinee_l).into(), (*scrutinee_r).into())?
        }
        (
            SetTermForm::BoxProgram {
                program_ty: program_ty_l,
                program: program_l,
                ..
            },
            SetTermForm::BoxProgram {
                program_ty: program_ty_r,
                program: program_r,
                ..
            },
        ) => {
            compare((*program_ty_l).into(), (*program_ty_r).into())?
                && compare((*program_l).into(), (*program_r).into())?
        }
        (
            SetTermForm::ForceBox {
                program_ty: program_ty_l,
                boxed: boxed_l,
            },
            SetTermForm::ForceBox {
                program_ty: program_ty_r,
                boxed: boxed_r,
            },
        ) => {
            compare((*program_ty_l).into(), (*program_ty_r).into())?
                && compare((*boxed_l).into(), (*boxed_r).into())?
        }
        (
            SetTermForm::BoxApp {
                rule: rule_l,
                domain: domain_l,
                codomain: codomain_l,
                function: function_l,
                argument: argument_l,
            },
            SetTermForm::BoxApp {
                rule: rule_r,
                domain: domain_r,
                codomain: codomain_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*codomain_l).into(), (*codomain_r).into())?
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            SetTermForm::BoxTypeApp {
                rule: rule_l,
                domain: domain_l,
                codomain: codomain_l,
                function: function_l,
                argument: argument_l,
                ..
            },
            SetTermForm::BoxTypeApp {
                rule: rule_r,
                domain: domain_r,
                codomain: codomain_r,
                function: function_r,
                argument: argument_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*codomain_l).into(), (*codomain_r).into())?
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            SetTermForm::TakeSet {
                domain: domain_l,
                codomain: codomain_l,
                map: map_l,
                existence: existence_l,
                uniqueness: uniqueness_l,
            },
            SetTermForm::TakeSet {
                domain: domain_r,
                codomain: codomain_r,
                map: map_r,
                existence: existence_r,
                uniqueness: uniqueness_r,
            },
        ) => {
            compare((*domain_l).into(), (*domain_r).into())?
                && compare((*codomain_l).into(), (*codomain_r).into())?
                && compare((*map_l).into(), (*map_r).into())?
                && compare((*existence_l).into(), (*existence_r).into())?
                && compare((*uniqueness_l).into(), (*uniqueness_r).into())?
        }
        (
            SetTermForm::IndCtor {
                inductive: inductive_l,
                constructor: constructor_l,
                parameters: parameters_l,
            },
            SetTermForm::IndCtor {
                inductive: inductive_r,
                constructor: constructor_r,
                parameters: parameters_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && constructor_l == constructor_r
                && parameters_l.len() == parameters_r.len())
            {
                return Ok(false);
            }
            for (left, right) in parameters_l.iter().zip(parameters_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            SetTermForm::IndElim {
                inductive: inductive_l,
                motive_vars: motive_vars_l,
                scrutinee: scrutinee_l,
                motive_domains: motive_domains_l,
                motive_body: motive_body_l,
                cases: cases_l,
            },
            SetTermForm::IndElim {
                inductive: inductive_r,
                motive_vars: motive_vars_r,
                scrutinee: scrutinee_r,
                motive_domains: motive_domains_r,
                motive_body: motive_body_r,
                cases: cases_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && motive_vars_l.len() == motive_vars_r.len()
                && compare((*scrutinee_l).into(), (*scrutinee_r).into())?
                && motive_domains_l.len() == motive_domains_r.len()
                && compare((*motive_body_l).into(), (*motive_body_r).into())?
                && cases_l.len() == cases_r.len())
            {
                return Ok(false);
            }
            for (left, right) in motive_domains_l.iter().zip(motive_domains_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            for (left, right) in cases_l.iter().zip(cases_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            SetTermForm::SetCase {
                inductive: inductive_l,
                binders: binders_l,
                result_ty: result_ty_l,
                scrutinee: scrutinee_l,
                branches: branches_l,
            },
            SetTermForm::SetCase {
                inductive: inductive_r,
                binders: binders_r,
                result_ty: result_ty_r,
                scrutinee: scrutinee_r,
                branches: branches_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && binders_l
                    .iter()
                    .map(Vec::len)
                    .eq(binders_r.iter().map(Vec::len))
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*scrutinee_l).into(), (*scrutinee_r).into())?
                && branches_l.len() == branches_r.len())
            {
                return Ok(false);
            }
            for (left, right) in branches_l.iter().zip(branches_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        _ => false,
    })
}
fn compare_set_type(
    arena: &Arena,
    left: SetType,
    right: SetType,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (SetTypeForm::Bound { index: index_l }, SetTypeForm::Bound { index: index_r }) => {
            index_l == index_r
        }
        (
            SetTypeForm::ModuleParam {
                parameter: parameter_l,
            },
            SetTypeForm::ModuleParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            SetTypeForm::Constant {
                definition: definition_l,
            },
            SetTypeForm::Constant {
                definition: definition_r,
            },
        ) => definition_l == definition_r,
        (
            SetTypeForm::ReflectedProgramParam {
                parameter: parameter_l,
            },
            SetTypeForm::ReflectedProgramParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            SetTypeForm::ProdTerm {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            SetTypeForm::ProdTerm {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            SetTypeForm::ProdType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            SetTypeForm::ProdType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            SetTypeForm::LambdaTerm {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            SetTypeForm::LambdaTerm {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            SetTypeForm::LambdaType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            SetTypeForm::LambdaType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            SetTypeForm::AppTerm {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            SetTypeForm::AppTerm {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            SetTypeForm::AppType {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            SetTypeForm::AppType {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (SetTypeForm::PowerSet { set: set_l }, SetTypeForm::PowerSet { set: set_r }) => {
            compare((*set_l).into(), (*set_r).into())?
        }
        (
            SetTypeForm::TypeLift {
                superset: superset_l,
                subset: subset_l,
            },
            SetTypeForm::TypeLift {
                superset: superset_r,
                subset: subset_r,
            },
        ) => {
            compare((*superset_l).into(), (*superset_r).into())?
                && compare((*subset_l).into(), (*subset_r).into())?
        }
        (
            SetTypeForm::RunStep {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
            },
            SetTypeForm::RunStep {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
        }
        (
            SetTypeForm::BoxType {
                program_ty: program_ty_l,
            },
            SetTypeForm::BoxType {
                program_ty: program_ty_r,
            },
        ) => compare((*program_ty_l).into(), (*program_ty_r).into())?,
        (
            SetTypeForm::Recursor {
                rule: rule_l,
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                motive: motive_l,
                on_continue: on_continue_l,
                on_finish: on_finish_l,
                scrutinee: scrutinee_l,
                ..
            },
            SetTypeForm::Recursor {
                rule: rule_r,
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                motive: motive_r,
                on_continue: on_continue_r,
                on_finish: on_finish_r,
                scrutinee: scrutinee_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*motive_l).into(), (*motive_r).into())?
                && compare((*on_continue_l).into(), (*on_continue_r).into())?
                && compare((*on_finish_l).into(), (*on_finish_r).into())?
                && compare((*scrutinee_l).into(), (*scrutinee_r).into())?
        }
        (
            SetTypeForm::IndType {
                inductive: inductive_l,
                parameters: parameters_l,
            },
            SetTypeForm::IndType {
                inductive: inductive_r,
                parameters: parameters_r,
            },
        ) => {
            if !(inductive_l == inductive_r && parameters_l.len() == parameters_r.len()) {
                return Ok(false);
            }
            for (left, right) in parameters_l.iter().zip(parameters_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            SetTypeForm::IndCtor {
                inductive: inductive_l,
                constructor: constructor_l,
                parameters: parameters_l,
            },
            SetTypeForm::IndCtor {
                inductive: inductive_r,
                constructor: constructor_r,
                parameters: parameters_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && constructor_l == constructor_r
                && parameters_l.len() == parameters_r.len())
            {
                return Ok(false);
            }
            for (left, right) in parameters_l.iter().zip(parameters_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            SetTypeForm::IndElim {
                inductive: inductive_l,
                motive_vars: motive_vars_l,
                scrutinee: scrutinee_l,
                motive_domains: motive_domains_l,
                motive_body: motive_body_l,
                cases: cases_l,
            },
            SetTypeForm::IndElim {
                inductive: inductive_r,
                motive_vars: motive_vars_r,
                scrutinee: scrutinee_r,
                motive_domains: motive_domains_r,
                motive_body: motive_body_r,
                cases: cases_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && motive_vars_l.len() == motive_vars_r.len()
                && compare((*scrutinee_l).into(), (*scrutinee_r).into())?
                && motive_domains_l.len() == motive_domains_r.len()
                && compare((*motive_body_l).into(), (*motive_body_r).into())?
                && cases_l.len() == cases_r.len())
            {
                return Ok(false);
            }
            for (left, right) in motive_domains_l.iter().zip(motive_domains_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            for (left, right) in cases_l.iter().zip(cases_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        _ => false,
    })
}
fn compare_set_kind(
    arena: &Arena,
    left: SetKind,
    right: SetKind,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (SetKindForm::Base, SetKindForm::Base) => true,
        (
            SetKindForm::ProdTerm {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            SetKindForm::ProdTerm {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            SetKindForm::ProdType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            SetKindForm::ProdType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            SetKindForm::IndType {
                inductive: inductive_l,
                parameters: parameters_l,
            },
            SetKindForm::IndType {
                inductive: inductive_r,
                parameters: parameters_r,
            },
        ) => {
            if !(inductive_l == inductive_r && parameters_l.len() == parameters_r.len()) {
                return Ok(false);
            }
            for (left, right) in parameters_l.iter().zip(parameters_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            SetKindForm::ModuleParam {
                parameter: parameter_l,
            },
            SetKindForm::ModuleParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            SetKindForm::Constant {
                definition: definition_l,
            },
            SetKindForm::Constant {
                definition: definition_r,
            },
        ) => definition_l == definition_r,
        _ => false,
    })
}
fn compare_prop_term(
    arena: &Arena,
    left: PropTerm,
    right: PropTerm,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (PropTermForm::Bound { index: index_l }, PropTermForm::Bound { index: index_r }) => {
            index_l == index_r
        }
        (
            PropTermForm::ModuleParam {
                parameter: parameter_l,
            },
            PropTermForm::ModuleParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            PropTermForm::Constant {
                definition: definition_l,
            },
            PropTermForm::Constant {
                definition: definition_r,
            },
        ) => definition_l == definition_r,
        (
            PropTermForm::LambdaTerm {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            PropTermForm::LambdaTerm {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            PropTermForm::LambdaType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            PropTermForm::LambdaType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            PropTermForm::AppTerm {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            PropTermForm::AppTerm {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            PropTermForm::AppType {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            PropTermForm::AppType {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            PropTermForm::Recursor {
                rule: rule_l,
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                motive: motive_l,
                on_continue: on_continue_l,
                on_finish: on_finish_l,
                scrutinee: scrutinee_l,
                ..
            },
            PropTermForm::Recursor {
                rule: rule_r,
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                motive: motive_r,
                on_continue: on_continue_r,
                on_finish: on_finish_r,
                scrutinee: scrutinee_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*motive_l).into(), (*motive_r).into())?
                && compare((*on_continue_l).into(), (*on_continue_r).into())?
                && compare((*on_finish_l).into(), (*on_finish_r).into())?
                && compare((*scrutinee_l).into(), (*scrutinee_r).into())?
        }
        (
            PropTermForm::IdRefl { element: element_l },
            PropTermForm::IdRefl { element: element_r },
        ) => compare((*element_l).into(), (*element_r).into())?,
        (
            PropTermForm::ExistsIntro {
                element: element_l,
                set: set_l,
            },
            PropTermForm::ExistsIntro {
                element: element_r,
                set: set_r,
            },
        ) => {
            compare((*element_l).into(), (*element_r).into())?
                && compare((*set_l).into(), (*set_r).into())?
        }
        (
            PropTermForm::SubsetElim {
                element: element_l,
                subset: subset_l,
                superset: superset_l,
            },
            PropTermForm::SubsetElim {
                element: element_r,
                subset: subset_r,
                superset: superset_r,
            },
        ) => {
            compare((*element_l).into(), (*element_r).into())?
                && compare((*subset_l).into(), (*subset_r).into())?
                && compare((*superset_l).into(), (*superset_r).into())?
        }
        (
            PropTermForm::IdElim {
                left: left_l,
                right: right_l,
                ty: ty_l,
                predicate: predicate_l,
                base: base_l,
                equality: equality_l,
                ..
            },
            PropTermForm::IdElim {
                left: left_r,
                right: right_r,
                ty: ty_r,
                predicate: predicate_r,
                base: base_r,
                equality: equality_r,
                ..
            },
        ) => {
            compare((*left_l).into(), (*left_r).into())?
                && compare((*right_l).into(), (*right_r).into())?
                && compare((*ty_l).into(), (*ty_r).into())?
                && compare((*predicate_l).into(), (*predicate_r).into())?
                && compare((*base_l).into(), (*base_r).into())?
                && compare((*equality_l).into(), (*equality_r).into())?
        }
        (
            PropTermForm::TakeProp {
                domain: domain_l,
                proposition: proposition_l,
                map: map_l,
                existence: existence_l,
            },
            PropTermForm::TakeProp {
                domain: domain_r,
                proposition: proposition_r,
                map: map_r,
                existence: existence_r,
            },
        ) => {
            compare((*domain_l).into(), (*domain_r).into())?
                && compare((*proposition_l).into(), (*proposition_r).into())?
                && compare((*map_l).into(), (*map_r).into())?
                && compare((*existence_l).into(), (*existence_r).into())?
        }
        (
            PropTermForm::TakeEq {
                func: func_l,
                domain: domain_l,
                codomain: codomain_l,
                element: element_l,
                existence: existence_l,
                uniqueness: uniqueness_l,
            },
            PropTermForm::TakeEq {
                func: func_r,
                domain: domain_r,
                codomain: codomain_r,
                element: element_r,
                existence: existence_r,
                uniqueness: uniqueness_r,
            },
        ) => {
            compare((*func_l).into(), (*func_r).into())?
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*codomain_l).into(), (*codomain_r).into())?
                && compare((*element_l).into(), (*element_r).into())?
                && compare((*existence_l).into(), (*existence_r).into())?
                && compare((*uniqueness_l).into(), (*uniqueness_r).into())?
        }
        (
            PropTermForm::SetExt {
                left: left_l,
                right: right_l,
                left_to_right: left_to_right_l,
                right_to_left: right_to_left_l,
            },
            PropTermForm::SetExt {
                left: left_r,
                right: right_r,
                left_to_right: left_to_right_r,
                right_to_left: right_to_left_r,
            },
        ) => {
            compare((*left_l).into(), (*left_r).into())?
                && compare((*right_l).into(), (*right_r).into())?
                && compare((*left_to_right_l).into(), (*left_to_right_r).into())?
                && compare((*right_to_left_l).into(), (*right_to_left_r).into())?
        }
        (
            PropTermForm::FunExt {
                left: left_l,
                right: right_l,
                pointwise: pointwise_l,
            },
            PropTermForm::FunExt {
                left: left_r,
                right: right_r,
                pointwise: pointwise_r,
            },
        ) => {
            compare((*left_l).into(), (*left_r).into())?
                && compare((*right_l).into(), (*right_r).into())?
                && compare((*pointwise_l).into(), (*pointwise_r).into())?
        }
        (
            PropTermForm::ClassicalIndefiniteChoice {
                domain: domain_l,
                family: family_l,
                inhabited: inhabited_l,
            },
            PropTermForm::ClassicalIndefiniteChoice {
                domain: domain_r,
                family: family_r,
                inhabited: inhabited_r,
            },
        ) => {
            compare((*domain_l).into(), (*domain_r).into())?
                && compare((*family_l).into(), (*family_r).into())?
                && compare((*inhabited_l).into(), (*inhabited_r).into())?
        }
        (
            PropTermForm::AccIntro {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                step: step_l,
                state: state_l,
                predecessors: predecessors_l,
            },
            PropTermForm::AccIntro {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                step: step_r,
                state: state_r,
                predecessors: predecessors_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*step_l).into(), (*step_r).into())?
                && compare((*state_l).into(), (*state_r).into())?
                && compare((*predecessors_l).into(), (*predecessors_r).into())?
        }
        (
            PropTermForm::AccDescent {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                step: step_l,
                from: from_l,
                to: to_l,
                accessibility: accessibility_l,
                transition: transition_l,
            },
            PropTermForm::AccDescent {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                step: step_r,
                from: from_r,
                to: to_r,
                accessibility: accessibility_r,
                transition: transition_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*step_l).into(), (*step_r).into())?
                && compare((*from_l).into(), (*from_r).into())?
                && compare((*to_l).into(), (*to_r).into())?
                && compare((*accessibility_l).into(), (*accessibility_r).into())?
                && compare((*transition_l).into(), (*transition_r).into())?
        }
        (
            PropTermForm::IndCtor {
                inductive: inductive_l,
                constructor: constructor_l,
                parameters: parameters_l,
            },
            PropTermForm::IndCtor {
                inductive: inductive_r,
                constructor: constructor_r,
                parameters: parameters_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && constructor_l == constructor_r
                && parameters_l.len() == parameters_r.len())
            {
                return Ok(false);
            }
            for (left, right) in parameters_l.iter().zip(parameters_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            PropTermForm::IndElim {
                inductive: inductive_l,
                motive_vars: motive_vars_l,
                scrutinee: scrutinee_l,
                motive_domains: motive_domains_l,
                motive_body: motive_body_l,
                cases: cases_l,
            },
            PropTermForm::IndElim {
                inductive: inductive_r,
                motive_vars: motive_vars_r,
                scrutinee: scrutinee_r,
                motive_domains: motive_domains_r,
                motive_body: motive_body_r,
                cases: cases_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && motive_vars_l.len() == motive_vars_r.len()
                && compare((*scrutinee_l).into(), (*scrutinee_r).into())?
                && motive_domains_l.len() == motive_domains_r.len()
                && compare((*motive_body_l).into(), (*motive_body_r).into())?
                && cases_l.len() == cases_r.len())
            {
                return Ok(false);
            }
            for (left, right) in motive_domains_l.iter().zip(motive_domains_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            for (left, right) in cases_l.iter().zip(cases_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        _ => false,
    })
}
fn compare_prop_type(
    arena: &Arena,
    left: PropType,
    right: PropType,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (PropTypeForm::Bound { index: index_l }, PropTypeForm::Bound { index: index_r }) => {
            index_l == index_r
        }
        (
            PropTypeForm::ModuleParam {
                parameter: parameter_l,
            },
            PropTypeForm::ModuleParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            PropTypeForm::Constant {
                definition: definition_l,
            },
            PropTypeForm::Constant {
                definition: definition_r,
            },
        ) => definition_l == definition_r,
        (
            PropTypeForm::ProdTerm {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            PropTypeForm::ProdTerm {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            PropTypeForm::ProdType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            PropTypeForm::ProdType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            PropTypeForm::LambdaTerm {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            PropTypeForm::LambdaTerm {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            PropTypeForm::LambdaType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            PropTypeForm::LambdaType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            PropTypeForm::AppTerm {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            PropTypeForm::AppTerm {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            PropTypeForm::AppType {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            PropTypeForm::AppType {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            PropTypeForm::Pred {
                superset: superset_l,
                subset: subset_l,
                element: element_l,
            },
            PropTypeForm::Pred {
                superset: superset_r,
                subset: subset_r,
                element: element_r,
            },
        ) => {
            compare((*superset_l).into(), (*superset_r).into())?
                && compare((*subset_l).into(), (*subset_r).into())?
                && compare((*element_l).into(), (*element_r).into())?
        }
        (
            PropTypeForm::Equal {
                left: left_l,
                right: right_l,
            },
            PropTypeForm::Equal {
                left: left_r,
                right: right_r,
            },
        ) => {
            compare((*left_l).into(), (*left_r).into())?
                && compare((*right_l).into(), (*right_r).into())?
        }
        (PropTypeForm::Exists { set: set_l }, PropTypeForm::Exists { set: set_r }) => {
            compare((*set_l).into(), (*set_r).into())?
        }
        (
            PropTypeForm::Acc {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                step: step_l,
                state: state_l,
            },
            PropTypeForm::Acc {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                step: step_r,
                state: state_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*step_l).into(), (*step_r).into())?
                && compare((*state_l).into(), (*state_r).into())?
        }
        (
            PropTypeForm::Recursor {
                rule: rule_l,
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                motive: motive_l,
                on_continue: on_continue_l,
                on_finish: on_finish_l,
                scrutinee: scrutinee_l,
                ..
            },
            PropTypeForm::Recursor {
                rule: rule_r,
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                motive: motive_r,
                on_continue: on_continue_r,
                on_finish: on_finish_r,
                scrutinee: scrutinee_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*motive_l).into(), (*motive_r).into())?
                && compare((*on_continue_l).into(), (*on_continue_r).into())?
                && compare((*on_finish_l).into(), (*on_finish_r).into())?
                && compare((*scrutinee_l).into(), (*scrutinee_r).into())?
        }
        (
            PropTypeForm::IndType {
                inductive: inductive_l,
                parameters: parameters_l,
            },
            PropTypeForm::IndType {
                inductive: inductive_r,
                parameters: parameters_r,
            },
        ) => {
            if !(inductive_l == inductive_r && parameters_l.len() == parameters_r.len()) {
                return Ok(false);
            }
            for (left, right) in parameters_l.iter().zip(parameters_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            PropTypeForm::IndCtor {
                inductive: inductive_l,
                constructor: constructor_l,
                parameters: parameters_l,
            },
            PropTypeForm::IndCtor {
                inductive: inductive_r,
                constructor: constructor_r,
                parameters: parameters_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && constructor_l == constructor_r
                && parameters_l.len() == parameters_r.len())
            {
                return Ok(false);
            }
            for (left, right) in parameters_l.iter().zip(parameters_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            PropTypeForm::IndElim {
                inductive: inductive_l,
                motive_vars: motive_vars_l,
                scrutinee: scrutinee_l,
                motive_domains: motive_domains_l,
                motive_body: motive_body_l,
                cases: cases_l,
            },
            PropTypeForm::IndElim {
                inductive: inductive_r,
                motive_vars: motive_vars_r,
                scrutinee: scrutinee_r,
                motive_domains: motive_domains_r,
                motive_body: motive_body_r,
                cases: cases_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && motive_vars_l.len() == motive_vars_r.len()
                && compare((*scrutinee_l).into(), (*scrutinee_r).into())?
                && motive_domains_l.len() == motive_domains_r.len()
                && compare((*motive_body_l).into(), (*motive_body_r).into())?
                && cases_l.len() == cases_r.len())
            {
                return Ok(false);
            }
            for (left, right) in motive_domains_l.iter().zip(motive_domains_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            for (left, right) in cases_l.iter().zip(cases_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        _ => false,
    })
}
fn compare_prop_kind(
    arena: &Arena,
    left: PropKind,
    right: PropKind,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (PropKindForm::Base, PropKindForm::Base) => true,
        (
            PropKindForm::ProdTerm {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            PropKindForm::ProdTerm {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            PropKindForm::ProdType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            PropKindForm::ProdType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            PropKindForm::IndType {
                inductive: inductive_l,
                parameters: parameters_l,
            },
            PropKindForm::IndType {
                inductive: inductive_r,
                parameters: parameters_r,
            },
        ) => {
            if !(inductive_l == inductive_r && parameters_l.len() == parameters_r.len()) {
                return Ok(false);
            }
            for (left, right) in parameters_l.iter().zip(parameters_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            PropKindForm::ModuleParam {
                parameter: parameter_l,
            },
            PropKindForm::ModuleParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            PropKindForm::Constant {
                definition: definition_l,
            },
            PropKindForm::Constant {
                definition: definition_r,
            },
        ) => definition_l == definition_r,
        _ => false,
    })
}
fn compare_value_term(
    arena: &Arena,
    left: ValueTerm,
    right: ValueTerm,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (ValueTermForm::Bound { index: index_l }, ValueTermForm::Bound { index: index_r }) => {
            index_l == index_r
        }
        (
            ValueTermForm::ModuleParam {
                parameter: parameter_l,
            },
            ValueTermForm::ModuleParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            ValueTermForm::Constant {
                definition: definition_l,
            },
            ValueTermForm::Constant {
                definition: definition_r,
            },
        ) => definition_l == definition_r,
        (
            ValueTermForm::ThunkValue {
                computation: computation_l,
            },
            ValueTermForm::ThunkValue {
                computation: computation_r,
            },
        ) => compare((*computation_l).into(), (*computation_r).into())?,
        (
            ValueTermForm::Continue {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                next: next_l,
            },
            ValueTermForm::Continue {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                next: next_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*next_l).into(), (*next_r).into())?
        }
        (
            ValueTermForm::Finish {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                output: output_l,
            },
            ValueTermForm::Finish {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                output: output_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*output_l).into(), (*output_r).into())?
        }
        (
            ValueTermForm::InductiveConstructor {
                inductive: inductive_l,
                constructor: constructor_l,
                parameters: parameters_l,
                fields: fields_l,
            },
            ValueTermForm::InductiveConstructor {
                inductive: inductive_r,
                constructor: constructor_r,
                parameters: parameters_r,
                fields: fields_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && constructor_l == constructor_r
                && parameters_l.len() == parameters_r.len()
                && fields_l.len() == fields_r.len())
            {
                return Ok(false);
            }
            for (left, right) in parameters_l.iter().zip(parameters_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            for (left, right) in fields_l.iter().zip(fields_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        _ => false,
    })
}
fn compare_value_type(
    arena: &Arena,
    left: ValueType,
    right: ValueType,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (ValueTypeForm::Bound { index: index_l }, ValueTypeForm::Bound { index: index_r }) => {
            index_l == index_r
        }
        (
            ValueTypeForm::ModuleParam {
                parameter: parameter_l,
            },
            ValueTypeForm::ModuleParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            ValueTypeForm::Constant {
                definition: definition_l,
            },
            ValueTypeForm::Constant {
                definition: definition_r,
            },
        ) => definition_l == definition_r,
        (
            ValueTypeForm::Thunk {
                computation_ty: computation_ty_l,
            },
            ValueTypeForm::Thunk {
                computation_ty: computation_ty_r,
            },
        ) => compare((*computation_ty_l).into(), (*computation_ty_r).into())?,
        (
            ValueTypeForm::RunStep {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
            },
            ValueTypeForm::RunStep {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
        }
        (
            ValueTypeForm::Inductive {
                inductive: inductive_l,
                parameters: parameters_l,
            },
            ValueTypeForm::Inductive {
                inductive: inductive_r,
                parameters: parameters_r,
            },
        ) => {
            if !(inductive_l == inductive_r && parameters_l.len() == parameters_r.len()) {
                return Ok(false);
            }
            for (left, right) in parameters_l.iter().zip(parameters_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            ValueTypeForm::LambdaType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            ValueTypeForm::LambdaType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            ValueTypeForm::AppType {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            ValueTypeForm::AppType {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        _ => false,
    })
}
fn compare_value_kind(
    arena: &Arena,
    left: ValueKind,
    right: ValueKind,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (ValueKindForm::Base, ValueKindForm::Base) => true,
        (
            ValueKindForm::ProdType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            ValueKindForm::ProdType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        _ => false,
    })
}
fn compare_computation_term(
    arena: &Arena,
    left: ComputationTerm,
    right: ComputationTerm,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (
            ComputationTermForm::ModuleParam {
                parameter: parameter_l,
            },
            ComputationTermForm::ModuleParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            ComputationTermForm::Constant {
                definition: definition_l,
            },
            ComputationTermForm::Constant {
                definition: definition_r,
            },
        ) => definition_l == definition_r,
        (
            ComputationTermForm::Return { value: value_l },
            ComputationTermForm::Return { value: value_r },
        ) => compare((*value_l).into(), (*value_r).into())?,
        (
            ComputationTermForm::Force { value: value_l },
            ComputationTermForm::Force { value: value_r },
        ) => compare((*value_l).into(), (*value_r).into())?,
        (
            ComputationTermForm::LambdaTerm {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            ComputationTermForm::LambdaTerm {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            ComputationTermForm::LambdaType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            ComputationTermForm::LambdaType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            ComputationTermForm::AppTerm {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            ComputationTermForm::AppTerm {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            ComputationTermForm::AppType {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            ComputationTermForm::AppType {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        (
            ComputationTermForm::Sequence {
                value_ty: value_ty_l,
                computation: computation_l,
                body: body_l,
                ..
            },
            ComputationTermForm::Sequence {
                value_ty: value_ty_r,
                computation: computation_r,
                body: body_r,
                ..
            },
        ) => {
            compare((*value_ty_l).into(), (*value_ty_r).into())?
                && compare((*computation_l).into(), (*computation_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            ComputationTermForm::ValueLet {
                value_ty: value_ty_l,
                value: value_l,
                body: body_l,
                ..
            },
            ComputationTermForm::ValueLet {
                value_ty: value_ty_r,
                value: value_r,
                body: body_r,
                ..
            },
        ) => {
            compare((*value_ty_l).into(), (*value_ty_r).into())?
                && compare((*value_l).into(), (*value_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            ComputationTermForm::Case {
                inductive: inductive_l,
                binders: binders_l,
                result_ty: result_ty_l,
                scrutinee: scrutinee_l,
                branches: branches_l,
            },
            ComputationTermForm::Case {
                inductive: inductive_r,
                binders: binders_r,
                result_ty: result_ty_r,
                scrutinee: scrutinee_r,
                branches: branches_r,
            },
        ) => {
            if !(inductive_l == inductive_r
                && binders_l
                    .iter()
                    .map(Vec::len)
                    .eq(binders_r.iter().map(Vec::len))
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*scrutinee_l).into(), (*scrutinee_r).into())?
                && branches_l.len() == branches_r.len())
            {
                return Ok(false);
            }
            for (left, right) in branches_l.iter().zip(branches_r) {
                if !compare((*left).into(), (*right).into())? {
                    return Ok(false);
                }
            }
            true
        }
        (
            ComputationTermForm::Run {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                step: step_l,
                initial: initial_l,
            },
            ComputationTermForm::Run {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                step: step_r,
                initial: initial_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*step_l).into(), (*step_r).into())?
                && compare((*initial_l).into(), (*initial_r).into())?
        }
        (
            ComputationTermForm::RunCase {
                state_ty: state_ty_l,
                result_ty: result_ty_l,
                step: step_l,
                initial: initial_l,
                transition: transition_l,
            },
            ComputationTermForm::RunCase {
                state_ty: state_ty_r,
                result_ty: result_ty_r,
                step: step_r,
                initial: initial_r,
                transition: transition_r,
            },
        ) => {
            compare((*state_ty_l).into(), (*state_ty_r).into())?
                && compare((*result_ty_l).into(), (*result_ty_r).into())?
                && compare((*step_l).into(), (*step_r).into())?
                && compare((*initial_l).into(), (*initial_r).into())?
                && compare((*transition_l).into(), (*transition_r).into())?
        }
        _ => false,
    })
}
fn compare_computation_type(
    arena: &Arena,
    left: ComputationType,
    right: ComputationType,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (
            ComputationTypeForm::Bound { index: index_l },
            ComputationTypeForm::Bound { index: index_r },
        ) => index_l == index_r,
        (
            ComputationTypeForm::ModuleParam {
                parameter: parameter_l,
            },
            ComputationTypeForm::ModuleParam {
                parameter: parameter_r,
            },
        ) => parameter_l == parameter_r,
        (
            ComputationTypeForm::Constant {
                definition: definition_l,
            },
            ComputationTypeForm::Constant {
                definition: definition_r,
            },
        ) => definition_l == definition_r,
        (
            ComputationTypeForm::ReturnType {
                value_ty: value_ty_l,
            },
            ComputationTypeForm::ReturnType {
                value_ty: value_ty_r,
            },
        ) => compare((*value_ty_l).into(), (*value_ty_r).into())?,
        (
            ComputationTypeForm::ProdTerm {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            ComputationTypeForm::ProdTerm {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            ComputationTypeForm::ProdType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            ComputationTypeForm::ProdType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            ComputationTypeForm::LambdaType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            ComputationTypeForm::LambdaType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        (
            ComputationTypeForm::AppType {
                rule: rule_l,
                function: function_l,
                argument: argument_l,
            },
            ComputationTypeForm::AppType {
                rule: rule_r,
                function: function_r,
                argument: argument_r,
            },
        ) => {
            rule_l == rule_r
                && compare((*function_l).into(), (*function_r).into())?
                && compare((*argument_l).into(), (*argument_r).into())?
        }
        _ => false,
    })
}
fn compare_computation_kind(
    arena: &Arena,
    left: ComputationKind,
    right: ComputationKind,
    compare: &mut dyn FnMut(Expression, Expression) -> Result<bool, String>,
) -> Result<bool, String> {
    let left = arena.read(left);
    let right = arena.read(right);
    Ok(match (&left.form, &right.form) {
        (ComputationKindForm::Base, ComputationKindForm::Base) => true,
        (
            ComputationKindForm::ProdType {
                rule: rule_l,
                domain: domain_l,
                body: body_l,
                ..
            },
            ComputationKindForm::ProdType {
                rule: rule_r,
                domain: domain_r,
                body: body_r,
                ..
            },
        ) => {
            rule_l == rule_r
                && compare((*domain_l).into(), (*domain_r).into())?
                && compare((*body_l).into(), (*body_r).into())?
        }
        _ => false,
    })
}
