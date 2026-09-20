//! Independent formation and typing checks for indexed syntax.
use super::{calculus::*, construction as build, environment::*, sort::*, structure, syntax::*};
use crate::ids::*;
pub struct Checker<'a> {
    pub env: &'a Environment,
    pub context: Context,
    inference_depth: usize,
    checking_context: bool,
    validated_context: Option<Vec<Expression>>,
}

impl<'a> Checker<'a> {
    pub fn new(env: &'a Environment, context: Context) -> Self {
        Self {
            env,
            context,
            inference_depth: 0,
            checking_context: false,
            validated_context: None,
        }
    }
    fn arena(&self) -> &Arena {
        &self.env.arena
    }
    pub fn check_context(&mut self) -> Result<(), String> {
        let key = self
            .context
            .iter()
            .map(|b| b.classifier.clone())
            .collect::<Vec<_>>();
        if self.validated_context.as_ref() == Some(&key) {
            return Ok(());
        }
        if let Some(first) = key.first() {
            let program = self.arena().sort(first.clone()).is_program();
            if key
                .iter()
                .any(|e| self.arena().sort(e.clone()).is_program() != program)
            {
                return Err("Set/Prop and Program contexts are separate".into());
            }
        }
        let was_checking = self.checking_context;
        self.checking_context = true;
        let entries = std::mem::take(&mut self.context);
        let result = (|| {
            for entry in &entries {
                self.formation(entry.classifier.clone())?;
                self.context.push(entry.clone())
            }
            Ok(())
        })();
        self.context = entries;
        self.checking_context = was_checking;
        if result.is_ok() {
            self.validated_context = Some(key)
        }
        result
    }
    fn under<T>(
        &mut self,
        var: SymbolId,
        classifier: Expression,
        f: impl FnOnce(&mut Self) -> Result<T, String>,
    ) -> Result<T, String> {
        self.context.push(Binding { var, classifier });
        let result = f(self);
        self.context.pop();
        result
    }
    pub fn formation(&mut self, e: Expression) -> Result<Sort, String> {
        match self.infer(e)? {
            Classifier::Upper(b) => Ok(Sort::Upper(b)),
            Classifier::Expression(k) => {
                let k = whnf(self.env, k)?;
                if structure::is_base(self.arena(), k.clone()) {
                    Ok(Sort::Base(self.arena().sort(k)))
                } else {
                    Err("expected a type of base kind".into())
                }
            }
        }
    }
    pub fn infer_set_term(&mut self, t: SetTerm) -> Result<SetType, String> {
        self.inferred(t.into())?.try_into()
    }
    pub fn infer_set_type(&mut self, t: SetType) -> Result<SetKind, String> {
        self.inferred(t.into())?.try_into()
    }
    pub fn check_set_kind(&mut self, k: SetKind) -> Result<(), String> {
        self.formation(k.into()).map(|_| ())
    }
    pub fn infer_value_term(&mut self, t: ValueTerm) -> Result<ValueType, String> {
        self.inferred(t.into())?.try_into()
    }
    pub fn infer_computation_term(
        &mut self,
        t: ComputationTerm,
    ) -> Result<ComputationType, String> {
        self.inferred(t.into())?.try_into()
    }
    pub fn infer_prop_term(&mut self, t: PropTerm) -> Result<PropType, String> {
        self.inferred(t.into())?.try_into()
    }
    pub fn infer_prop_type(&mut self, t: PropType) -> Result<PropKind, String> {
        self.inferred(t.into())?.try_into()
    }
    pub fn check_prop_kind(&mut self, k: PropKind) -> Result<(), String> {
        self.formation(k.into()).map(|_| ())
    }
    pub fn infer_value_type(&mut self, t: ValueType) -> Result<ValueKind, String> {
        self.inferred(t.into())?.try_into()
    }
    pub fn check_value_kind(&mut self, k: ValueKind) -> Result<(), String> {
        self.formation(k.into()).map(|_| ())
    }
    pub fn infer_computation_type(
        &mut self,
        t: ComputationType,
    ) -> Result<ComputationKind, String> {
        self.inferred(t.into())?.try_into()
    }
    pub fn check_computation_kind(&mut self, k: ComputationKind) -> Result<(), String> {
        self.formation(k.into()).map(|_| ())
    }
    pub fn infer_program_term(&mut self, t: ProgramTerm) -> Result<ProgramType, String> {
        self.inferred(t.into())?.try_into()
    }
    pub fn infer_program_type(&mut self, t: ProgramType) -> Result<ProgramKind, String> {
        self.inferred(t.into())?.try_into()
    }
    pub fn check_program_kind(&mut self, k: ProgramKind) -> Result<(), String> {
        self.formation(k.into()).map(|_| ())
    }
    pub fn inferred(&mut self, e: Expression) -> Result<Expression, String> {
        match self.infer(e)? {
            Classifier::Expression(t) => Ok(t),
            Classifier::Upper(_) => Err("kind has a formation sort, not an expression type".into()),
        }
    }
    pub fn check(
        &mut self,
        e: impl Into<Expression>,
        expected: impl Into<Classifier>,
    ) -> Result<(), String> {
        let e = e.into();
        let expected = expected.into();
        let inferred = self.infer(e)?;
        match (inferred, expected) {
            (Classifier::Upper(a), Classifier::Upper(b)) if a == b => Ok(()),
            (Classifier::Expression(a), Classifier::Expression(b)) => {
                self.formation(b.clone())?;
                if self.weaken(a.clone(), b.clone())? {
                    Ok(())
                } else {
                    Err(format!(
                        "types are not convertible in the same family and level\ninferred: {}\nexpected: {}",
                        super::printing::format_expression(self.env, whnf(self.env, a)?),
                        super::printing::format_expression(self.env, whnf(self.env, b)?)
                    ))
                }
            }
            _ => Err("judgement classification mismatch".into()),
        }
    }
    fn base_type(&mut self, e: Expression) -> Result<BaseSort, String> {
        match self.formation(e)? {
            Sort::Base(b) => Ok(b),
            _ => Err("expected a type, found a kind".into()),
        }
    }
    fn set_type(&mut self, e: Expression) -> Result<usize, String> {
        match self.base_type(e)? {
            BaseSort::Set(i) => Ok(i),
            _ => Err("expected Set(i)".into()),
        }
    }
    fn proposition(&mut self, e: Expression) -> Result<(), String> {
        if self.base_type(e)? == BaseSort::Prop {
            Ok(())
        } else {
            Err("expected proposition".into())
        }
    }
    fn arrow(&mut self, domain: Expression, codomain: Expression) -> Result<Expression, String> {
        let body = shift(self.arena(), codomain, 1, 0)?;
        self.product(SymbolId::ANONYMOUS, domain, body)
    }
    pub fn infer(&mut self, e: impl Into<Expression>) -> Result<Classifier, String> {
        let e = e.into();
        if self.inference_depth == 0 && !self.checking_context {
            self.check_context()?
        }
        // Closed annotations must not be rechecked under every use-site telescope.
        if !self.context.is_empty()
            && structure::annotation(self.arena(), e.clone()).is_some()
            && locally_closed(self.arena(), e.clone())
        {
            return Checker::new(self.env, vec![]).infer(e);
        }
        let key = (
            e.clone(),
            self.context.iter().map(|b| b.classifier.clone()).collect(),
        );
        if let Some(result) = self.env.inference_cache.borrow().get(&key) {
            return Ok(result.clone());
        }
        self.inference_depth += 1;
        let result = self.infer_inner(e);
        self.inference_depth -= 1;
        let result = result?;
        self.env
            .inference_cache
            .borrow_mut()
            .insert(key, result.clone());
        Ok(result)
    }
    fn validate_inferred(&self, e: Expression, ty: Expression) -> Result<(), String> {
        let expected = match e.family().stage() {
            Stage::Term => Stage::Type,
            Stage::Type => Stage::Kind,
            Stage::Kind => return Err("kind must have an upper-sort classifier".into()),
        };
        if ty.family().stage() != expected || self.arena().sort(e) != self.arena().sort(ty) {
            return Err("node sort index disagrees with its inferred classifier".into());
        }
        Ok(())
    }
    fn closed_program_type(&self, p: Expression) -> Result<(), String> {
        if !matches!(self.arena().sort(p.clone()), BaseSort::Computation(_))
            || !closed_in_environment(self.env, p.clone())
        {
            return Err("Box requires a closed computation type".into());
        }
        Checker::new(self.env, vec![]).base_type(p)?;
        Ok(())
    }
    fn lifted(&self, e: Expression, n: usize) -> Result<Expression, String> {
        shift(self.arena(), e, n, 0)
    }
    fn check_arguments(&mut self, args: &[Expression], telescope: &Context) -> Result<(), String> {
        if args.len() != telescope.len() {
            return Err("parameter count mismatch".into());
        }
        for (i, (arg, binder)) in args.iter().zip(telescope).enumerate() {
            let ty = instantiate_telescope(self.env, binder.classifier.clone(), &args[..i])?;
            self.check(arg.clone(), ty)?;
        }
        Ok(())
    }
    fn apply_motive(&mut self, motive: &Motive, args: &[Expression]) -> Result<Expression, String> {
        if args.len() != motive.domains.len() {
            return Err("motive argument count mismatch".into());
        }
        for (i, (arg, ty)) in args.iter().zip(&motive.domains).enumerate() {
            self.check(
                arg.clone(),
                instantiate_telescope(self.env, ty.clone(), &args[..i])?,
            )?;
        }
        instantiate_telescope(self.env, motive.body.clone(), args)
    }
    fn lift_motive(&self, m: &Motive) -> Result<Motive, String> {
        Ok(Motive {
            domains: m
                .domains
                .iter()
                .enumerate()
                .map(|(i, e)| shift(self.arena(), e, 1, i))
                .collect::<Result<_, _>>()?,
            body: shift(self.arena(), m.body.clone(), 1, m.domains.len())?,
        })
    }
    fn infer_inner(&mut self, e: Expression) -> Result<Classifier, String> {
        match e {
            Expression::SetTerm(h) => self.infer_set_term_node(h),
            Expression::SetType(h) => self.infer_set_type_node(h),
            Expression::SetKind(h) => self.infer_set_kind_node(h),
            Expression::PropTerm(h) => self.infer_prop_term_node(h),
            Expression::PropType(h) => self.infer_prop_type_node(h),
            Expression::PropKind(h) => self.infer_prop_kind_node(h),
            Expression::ValueTerm(h) => self.infer_value_term_node(h),
            Expression::ValueType(h) => self.infer_value_type_node(h),
            Expression::ValueKind(h) => self.infer_value_kind_node(h),
            Expression::ComputationTerm(h) => self.infer_computation_term_node(h),
            Expression::ComputationType(h) => self.infer_computation_type_node(h),
            Expression::ComputationKind(h) => self.infer_computation_kind_node(h),
        }
    }
    fn infer_set_term_node(&mut self, h: SetTerm) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        let inferred = match self.arena().get(h.clone()).form {
            SetTermForm::Bound { index } => self.infer_bound(e.clone(), index)?,
            SetTermForm::ModuleParam { parameter } => self.infer_module_param(parameter)?,
            SetTermForm::Annotated { body, classifier } => {
                return self.infer_annotation(e, body.into(), classifier);
            }
            SetTermForm::ReflectedProgramParam { parameter } => {
                self.infer_reflected_program_param(parameter)?
            }
            SetTermForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            SetTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            SetTermForm::AppTerm {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
            SetTermForm::AppType {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
            SetTermForm::Subset {
                var,
                set,
                predicate,
            } => self.infer_subset(var, set.into(), predicate.into())?,
            SetTermForm::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => self.infer_subset_intro(
                superset.into(),
                subset.into(),
                element.into(),
                proof.into(),
            )?,
            SetTermForm::Continue {
                state_ty,
                result_ty,
                next,
            } => self.infer_continue(state_ty.into(), result_ty.into(), next.into())?,
            SetTermForm::Finish {
                state_ty,
                result_ty,
                output,
            } => self.infer_finish(state_ty.into(), result_ty.into(), output.into())?,
            SetTermForm::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => self.infer_set_run(
                state_ty.into(),
                result_ty.into(),
                step.into(),
                initial.into(),
                accessibility.into(),
            )?,
            SetTermForm::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => self.infer_set_run_case(
                state_ty.into(),
                result_ty.into(),
                step.into(),
                initial.into(),
                transition.into(),
                accessibility.into(),
                transition_equality.into(),
            )?,
            SetTermForm::Recursor {
                rule,
                var,
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => self.infer_recursor(
                rule,
                var,
                state_ty.into(),
                result_ty.into(),
                motive.into(),
                on_continue.into(),
                on_finish.into(),
                scrutinee.into(),
            )?,
            SetTermForm::BoxProgram {
                program_ty,
                program,
            } => self.infer_box_program(program_ty.into(), program.into())?,
            SetTermForm::ForceBox { program_ty, boxed } => {
                self.infer_force_box(program_ty.into(), boxed.into())?
            }
            SetTermForm::BoxApp {
                rule,
                domain,
                codomain,
                function,
                argument,
            } => self.infer_box_app(
                rule,
                domain.into(),
                codomain.into(),
                function.into(),
                argument.into(),
            )?,
            SetTermForm::BoxTypeApp {
                rule,
                var,
                domain,
                codomain,
                function,
                argument,
            } => self.infer_box_type_app(
                rule,
                var,
                domain.into(),
                codomain.into(),
                function.into(),
                argument.into(),
            )?,
            SetTermForm::TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
            } => self.infer_take_set(
                domain.into(),
                codomain.into(),
                map.into(),
                existence.into(),
                uniqueness.into(),
            )?,
            SetTermForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => self.infer_ind_ctor(inductive, constructor, parameters)?,
            SetTermForm::IndElim {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                cases,
            } => self.infer_ind_elim(
                inductive,
                motive_vars,
                scrutinee.into(),
                motive_domains,
                motive_body.into(),
                cases,
            )?,
            SetTermForm::Case {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                branches,
            } => self.infer_inductive_case(
                inductive,
                motive_vars,
                scrutinee.into(),
                motive_domains,
                motive_body.into(),
                branches,
            )?,
            SetTermForm::SetCase {
                inductive,
                binders,
                result_ty,
                scrutinee,
                branches,
            } => self.infer_set_case(
                inductive,
                binders,
                result_ty.into(),
                scrutinee.into(),
                branches,
            )?,
        };
        self.validate_inferred(e, inferred.clone())?;
        Ok(Classifier::Expression(inferred))
    }
    fn infer_set_type_node(&mut self, h: SetType) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        let inferred = match self.arena().get(h.clone()).form {
            SetTypeForm::Bound { index } => self.infer_bound(e.clone(), index)?,
            SetTypeForm::ModuleParam { parameter } => self.infer_module_param(parameter)?,
            SetTypeForm::Annotated { body, classifier } => {
                return self.infer_annotation(e, body.into(), classifier);
            }
            SetTypeForm::ReflectedProgramParam { parameter } => {
                self.infer_reflected_program_param(parameter)?
            }
            SetTypeForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => return self.infer_product(e, rule, var, domain.into(), body.into()),
            SetTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => return self.infer_product(e, rule, var, domain.into(), body.into()),
            SetTypeForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            SetTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            SetTypeForm::AppTerm {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
            SetTypeForm::AppType {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
            SetTypeForm::PowerSet { set } => self.infer_power_set(set.into())?,
            SetTypeForm::TypeLift { superset, subset } => {
                self.infer_type_lift(superset.into(), subset.into())?
            }
            SetTypeForm::RunStep {
                state_ty,
                result_ty,
            } => self.infer_run_step(state_ty.into(), result_ty.into())?,
            SetTypeForm::BoxType { program_ty } => self.infer_box_type(program_ty.into())?,
            SetTypeForm::Recursor {
                rule,
                var,
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => self.infer_recursor(
                rule,
                var,
                state_ty.into(),
                result_ty.into(),
                motive.into(),
                on_continue.into(),
                on_finish.into(),
                scrutinee.into(),
            )?,
            SetTypeForm::IndType {
                inductive,
                parameters,
            } => return self.infer_ind_type(e, inductive, parameters),
            SetTypeForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => self.infer_ind_ctor(inductive, constructor, parameters)?,
            SetTypeForm::IndElim {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                cases,
            } => self.infer_ind_elim(
                inductive,
                motive_vars,
                scrutinee.into(),
                motive_domains,
                motive_body.into(),
                cases,
            )?,
            SetTypeForm::Case {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                branches,
            } => self.infer_inductive_case(
                inductive,
                motive_vars,
                scrutinee.into(),
                motive_domains,
                motive_body.into(),
                branches,
            )?,
        };
        self.validate_inferred(e, inferred.clone())?;
        Ok(Classifier::Expression(inferred))
    }
    fn infer_set_kind_node(&mut self, h: SetKind) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        let inferred = match self.arena().get(h.clone()).form {
            SetKindForm::Base => return Ok(Classifier::Upper(self.arena().sort(e))),
            SetKindForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => return self.infer_product(e, rule, var, domain.into(), body.into()),
            SetKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => return self.infer_product(e, rule, var, domain.into(), body.into()),
            SetKindForm::IndType {
                inductive,
                parameters,
            } => return self.infer_ind_type(e, inductive, parameters),
            SetKindForm::ModuleParam { parameter } => self.infer_module_param(parameter)?,
            SetKindForm::Annotated { body, classifier } => {
                return self.infer_annotation(e, body.into(), classifier);
            }
        };
        self.validate_inferred(e, inferred.clone())?;
        Ok(Classifier::Expression(inferred))
    }
    fn infer_prop_term_node(&mut self, h: PropTerm) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        let inferred = match self.arena().get(h.clone()).form {
            PropTermForm::Bound { index } => self.infer_bound(e.clone(), index)?,
            PropTermForm::ModuleParam { parameter } => self.infer_module_param(parameter)?,
            PropTermForm::Annotated { body, classifier } => {
                return self.infer_annotation(e, body.into(), classifier);
            }
            PropTermForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            PropTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            PropTermForm::AppTerm {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
            PropTermForm::AppType {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
            PropTermForm::Recursor {
                rule,
                var,
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => self.infer_recursor(
                rule,
                var,
                state_ty.into(),
                result_ty.into(),
                motive.into(),
                on_continue.into(),
                on_finish.into(),
                scrutinee.into(),
            )?,
            PropTermForm::IdRefl { element } => self.infer_id_refl(element.into())?,
            PropTermForm::ExistsIntro { element, set } => {
                self.infer_exists_intro(element.into(), set.into())?
            }
            PropTermForm::SubsetElim {
                element,
                subset,
                superset,
            } => self.infer_subset_elim(element.into(), subset.into(), superset.into())?,
            PropTermForm::IdElim {
                var,
                left,
                right,
                ty,
                predicate,
                base,
                equality,
            } => self.infer_id_elim(
                var,
                left.into(),
                right.into(),
                ty.into(),
                predicate.into(),
                base.into(),
                equality.into(),
            )?,
            PropTermForm::TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => self.infer_take_prop(
                domain.into(),
                proposition.into(),
                map.into(),
                existence.into(),
            )?,
            PropTermForm::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
            } => self.infer_take_eq(
                func.into(),
                domain.into(),
                codomain.into(),
                element.into(),
                existence.into(),
                uniqueness.into(),
            )?,
            PropTermForm::SetExt {
                left,
                right,
                left_to_right,
                right_to_left,
            } => self.infer_set_ext(
                left.into(),
                right.into(),
                left_to_right.into(),
                right_to_left.into(),
            )?,
            PropTermForm::FunExt {
                left,
                right,
                pointwise,
            } => self.infer_fun_ext(left.into(), right.into(), pointwise.into())?,
            PropTermForm::ClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            } => self.infer_classical_indefinite_choice(
                domain.into(),
                family.into(),
                inhabited.into(),
            )?,
            PropTermForm::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
            } => self.infer_acc_intro(
                state_ty.into(),
                result_ty.into(),
                step.into(),
                state.into(),
                predecessors.into(),
            )?,
            PropTermForm::AccDescent {
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
            } => self.infer_acc_descent(
                state_ty.into(),
                result_ty.into(),
                step.into(),
                from.into(),
                to.into(),
                accessibility.into(),
                transition.into(),
            )?,
            PropTermForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => self.infer_ind_ctor(inductive, constructor, parameters)?,
            PropTermForm::IndElim {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                cases,
            } => self.infer_ind_elim(
                inductive,
                motive_vars,
                scrutinee.into(),
                motive_domains,
                motive_body.into(),
                cases,
            )?,
            PropTermForm::Case {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                branches,
            } => self.infer_inductive_case(
                inductive,
                motive_vars,
                scrutinee.into(),
                motive_domains,
                motive_body.into(),
                branches,
            )?,
        };
        self.validate_inferred(e, inferred.clone())?;
        Ok(Classifier::Expression(inferred))
    }
    fn infer_prop_type_node(&mut self, h: PropType) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        let inferred = match self.arena().get(h.clone()).form {
            PropTypeForm::Bound { index } => self.infer_bound(e.clone(), index)?,
            PropTypeForm::ModuleParam { parameter } => self.infer_module_param(parameter)?,
            PropTypeForm::Annotated { body, classifier } => {
                return self.infer_annotation(e, body.into(), classifier);
            }
            PropTypeForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => return self.infer_product(e, rule, var, domain.into(), body.into()),
            PropTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => return self.infer_product(e, rule, var, domain.into(), body.into()),
            PropTypeForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            PropTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            PropTypeForm::AppTerm {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
            PropTypeForm::AppType {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
            PropTypeForm::Pred {
                superset,
                subset,
                element,
            } => self.infer_pred(superset.into(), subset.into(), element.into())?,
            PropTypeForm::Equal { left, right } => self.infer_equal(left.into(), right.into())?,
            PropTypeForm::Exists { set } => self.infer_exists(set.into())?,
            PropTypeForm::Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => self.infer_acc(state_ty.into(), result_ty.into(), step.into(), state.into())?,
            PropTypeForm::Recursor {
                rule,
                var,
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => self.infer_recursor(
                rule,
                var,
                state_ty.into(),
                result_ty.into(),
                motive.into(),
                on_continue.into(),
                on_finish.into(),
                scrutinee.into(),
            )?,
            PropTypeForm::IndType {
                inductive,
                parameters,
            } => return self.infer_ind_type(e, inductive, parameters),
            PropTypeForm::IndCtor {
                inductive,
                constructor,
                parameters,
            } => self.infer_ind_ctor(inductive, constructor, parameters)?,
            PropTypeForm::IndElim {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                cases,
            } => self.infer_ind_elim(
                inductive,
                motive_vars,
                scrutinee.into(),
                motive_domains,
                motive_body.into(),
                cases,
            )?,
            PropTypeForm::Case {
                inductive,
                motive_vars,
                scrutinee,
                motive_domains,
                motive_body,
                branches,
            } => self.infer_inductive_case(
                inductive,
                motive_vars,
                scrutinee.into(),
                motive_domains,
                motive_body.into(),
                branches,
            )?,
        };
        self.validate_inferred(e, inferred.clone())?;
        Ok(Classifier::Expression(inferred))
    }
    fn infer_prop_kind_node(&mut self, h: PropKind) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        let inferred = match self.arena().get(h.clone()).form {
            PropKindForm::Base => return Ok(Classifier::Upper(self.arena().sort(e))),
            PropKindForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => return self.infer_product(e, rule, var, domain.into(), body.into()),
            PropKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => return self.infer_product(e, rule, var, domain.into(), body.into()),
            PropKindForm::IndType {
                inductive,
                parameters,
            } => return self.infer_ind_type(e, inductive, parameters),
            PropKindForm::ModuleParam { parameter } => self.infer_module_param(parameter)?,
            PropKindForm::Annotated { body, classifier } => {
                return self.infer_annotation(e, body.into(), classifier);
            }
        };
        self.validate_inferred(e, inferred.clone())?;
        Ok(Classifier::Expression(inferred))
    }
    fn infer_value_term_node(&mut self, h: ValueTerm) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        let inferred = match self.arena().get(h.clone()).form {
            ValueTermForm::Bound { index } => self.infer_bound(e.clone(), index)?,
            ValueTermForm::ModuleParam { parameter } => self.infer_module_param(parameter)?,
            ValueTermForm::Annotated { body, classifier } => {
                return self.infer_annotation(e, body.into(), classifier);
            }
            ValueTermForm::ThunkValue { computation } => {
                self.infer_thunk_value(computation.into())?
            }
            ValueTermForm::Continue {
                state_ty,
                result_ty,
                next,
            } => self.infer_continue(state_ty.into(), result_ty.into(), next.into())?,
            ValueTermForm::Finish {
                state_ty,
                result_ty,
                output,
            } => self.infer_finish(state_ty.into(), result_ty.into(), output.into())?,
            ValueTermForm::InductiveConstructor {
                inductive,
                constructor,
                parameters,
                fields,
            } => self.infer_inductive_constructor(inductive, constructor, parameters, fields)?,
        };
        self.validate_inferred(e, inferred.clone())?;
        Ok(Classifier::Expression(inferred))
    }
    fn infer_value_type_node(&mut self, h: ValueType) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        let inferred = match self.arena().get(h.clone()).form {
            ValueTypeForm::Bound { index } => self.infer_bound(e.clone(), index)?,
            ValueTypeForm::ModuleParam { parameter } => self.infer_module_param(parameter)?,
            ValueTypeForm::Annotated { body, classifier } => {
                return self.infer_annotation(e, body.into(), classifier);
            }
            ValueTypeForm::Thunk { computation_ty } => self.infer_thunk(computation_ty.into())?,
            ValueTypeForm::RunStep {
                state_ty,
                result_ty,
            } => self.infer_run_step(state_ty.into(), result_ty.into())?,
            ValueTypeForm::Inductive {
                inductive,
                parameters,
            } => self.infer_inductive(inductive, parameters)?,
            ValueTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            ValueTypeForm::AppType {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
        };
        self.validate_inferred(e, inferred.clone())?;
        Ok(Classifier::Expression(inferred))
    }
    fn infer_value_kind_node(&mut self, h: ValueKind) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        match self.arena().get(h.clone()).form {
            ValueKindForm::Base => Ok(Classifier::Upper(self.arena().sort(e))),
            ValueKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => self.infer_product(e, rule, var, domain.into(), body.into()),
        }
    }
    fn infer_computation_term_node(&mut self, h: ComputationTerm) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        let inferred = match self.arena().get(h.clone()).form {
            ComputationTermForm::ModuleParam { parameter } => self.infer_module_param(parameter)?,
            ComputationTermForm::Annotated { body, classifier } => {
                return self.infer_annotation(e, body.into(), classifier);
            }
            ComputationTermForm::Return { value } => self.infer_return(value.into())?,
            ComputationTermForm::Force { value } => self.infer_force(value.into())?,
            ComputationTermForm::LambdaTerm {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            ComputationTermForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            ComputationTermForm::AppTerm {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
            ComputationTermForm::AppType {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
            ComputationTermForm::Sequence {
                var,
                value_ty,
                computation,
                body,
            } => self.infer_sequence(var, value_ty.into(), computation.into(), body.into())?,
            ComputationTermForm::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => self.infer_value_let(var, value_ty.into(), value.into(), body.into())?,
            ComputationTermForm::Case {
                inductive,
                binders,
                result_ty,
                scrutinee,
                branches,
            } => self.infer_case(
                inductive,
                binders,
                result_ty.into(),
                scrutinee.into(),
                branches,
            )?,
            ComputationTermForm::Run {
                state_ty,
                result_ty,
                step,
                initial,
                ..
            } => {
                self.check_run(
                    state_ty.into(),
                    result_ty.clone().into(),
                    step.into(),
                    initial.into(),
                )?;
                self.check_reflected_program_run(h)?;
                self.return_type(result_ty.into())?
            }
            ComputationTermForm::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                ..
            } => {
                let runstep = self.check_run(
                    state_ty.into(),
                    result_ty.clone().into(),
                    step.into(),
                    initial.into(),
                )?;
                self.check(transition, self.return_type(runstep)?)?;
                self.check_reflected_program_run(h)?;
                self.return_type(result_ty.into())?
            }
        };
        self.validate_inferred(e, inferred.clone())?;
        Ok(Classifier::Expression(inferred))
    }
    fn infer_computation_type_node(&mut self, h: ComputationType) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        let inferred = match self.arena().get(h.clone()).form {
            ComputationTypeForm::Bound { index } => self.infer_bound(e.clone(), index)?,
            ComputationTypeForm::ModuleParam { parameter } => self.infer_module_param(parameter)?,
            ComputationTypeForm::Annotated { body, classifier } => {
                return self.infer_annotation(e, body.into(), classifier);
            }
            ComputationTypeForm::ReturnType { value_ty } => {
                self.infer_return_type(value_ty.into())?
            }
            ComputationTypeForm::ProdTerm {
                rule,
                var,
                domain,
                body,
            } => return self.infer_product(e, rule, var, domain.into(), body.into()),
            ComputationTypeForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => return self.infer_product(e, rule, var, domain.into(), body.into()),
            ComputationTypeForm::LambdaType {
                rule,
                var,
                domain,
                body,
            } => self.infer_lambda(e.clone(), rule, var, domain.into(), body.into())?,
            ComputationTypeForm::AppType {
                rule,
                function,
                argument,
            } => self.infer_application(e.clone(), rule, function.into(), argument.into())?,
        };
        self.validate_inferred(e, inferred.clone())?;
        Ok(Classifier::Expression(inferred))
    }
    fn infer_computation_kind_node(&mut self, h: ComputationKind) -> Result<Classifier, String> {
        let e: Expression = h.clone().into();
        match self.arena().get(h.clone()).form {
            ComputationKindForm::Base => Ok(Classifier::Upper(self.arena().sort(e))),
            ComputationKindForm::ProdType {
                rule,
                var,
                domain,
                body,
            } => self.infer_product(e, rule, var, domain.into(), body.into()),
        }
    }
    fn base_kind(&self, sort: BaseSort) -> Expression {
        build::base_kind(self.arena(), sort).expect("every sort has a base kind")
    }

    fn powerset(&self, set: Expression) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(SetTypeNode {
                level: self
                    .arena()
                    .sort(set.clone())
                    .level()
                    .ok_or("expected Set")?,
                form: SetTypeForm::PowerSet {
                    set: set.try_into()?,
                },
            })
            .into())
    }
    fn type_lift(&self, superset: Expression, subset: Expression) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(SetTypeNode {
                level: self
                    .arena()
                    .sort(superset.clone())
                    .level()
                    .ok_or("expected Set")?,
                form: SetTypeForm::TypeLift {
                    superset: superset.try_into()?,
                    subset: subset.try_into()?,
                },
            })
            .into())
    }
    fn predicate(
        &self,
        superset: Expression,
        subset: Expression,
        element: Expression,
    ) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(PropTypeNode {
                form: PropTypeForm::Pred {
                    superset: superset.try_into()?,
                    subset: subset.try_into()?,
                    element: element.try_into()?,
                },
            })
            .into())
    }
    fn equality(&self, left: Expression, right: Expression) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(PropTypeNode {
                form: PropTypeForm::Equal {
                    left: left.try_into()?,
                    right: right.try_into()?,
                },
            })
            .into())
    }
    fn exists(&self, set: Expression) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(PropTypeNode {
                form: PropTypeForm::Exists {
                    set: set.try_into()?,
                },
            })
            .into())
    }
    fn accessibility(
        &self,
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        state: Expression,
    ) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(PropTypeNode {
                form: PropTypeForm::Acc {
                    state_ty: state_ty.try_into()?,
                    result_ty: result_ty.try_into()?,
                    step: step.try_into()?,
                    state: state.try_into()?,
                },
            })
            .into())
    }
    fn return_type(&self, value_ty: Expression) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(ComputationTypeNode {
                level: self
                    .arena()
                    .sort(value_ty.clone())
                    .level()
                    .ok_or("expected value type")?,
                form: ComputationTypeForm::ReturnType {
                    value_ty: value_ty.try_into()?,
                },
            })
            .into())
    }
    fn thunk_type(&self, computation_ty: Expression) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(ValueTypeNode {
                level: self
                    .arena()
                    .sort(computation_ty.clone())
                    .level()
                    .ok_or("expected computation type")?,
                form: ValueTypeForm::Thunk {
                    computation_ty: computation_ty.try_into()?,
                },
            })
            .into())
    }
    fn box_type(&self, program_ty: Expression) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(SetTypeNode {
                level: self
                    .arena()
                    .sort(program_ty.clone())
                    .level()
                    .ok_or("expected Program type")?,
                form: SetTypeForm::BoxType {
                    program_ty: program_ty.try_into()?,
                },
            })
            .into())
    }
    fn runstep_type(
        &self,
        state_ty: Expression,
        result_ty: Expression,
    ) -> Result<Expression, String> {
        Ok(match self.arena().sort(state_ty.clone()) {
            BaseSort::Set(level) => self
                .arena()
                .alloc(SetTypeNode {
                    level,
                    form: SetTypeForm::RunStep {
                        state_ty: state_ty.try_into()?,
                        result_ty: result_ty.try_into()?,
                    },
                })
                .into(),
            BaseSort::Value(level) => self
                .arena()
                .alloc(ValueTypeNode {
                    level,
                    form: ValueTypeForm::RunStep {
                        state_ty: state_ty.try_into()?,
                        result_ty: result_ty.try_into()?,
                    },
                })
                .into(),
            _ => return Err("expected Set or value type".into()),
        })
    }
    fn continue_term(
        &self,
        state_ty: Expression,
        result_ty: Expression,
        next: Expression,
    ) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(SetTermNode {
                level: self
                    .arena()
                    .sort(state_ty.clone())
                    .level()
                    .ok_or("expected Set")?,
                form: SetTermForm::Continue {
                    state_ty: state_ty.try_into()?,
                    result_ty: result_ty.try_into()?,
                    next: next.try_into()?,
                },
            })
            .into())
    }
    fn finish_term(
        &self,
        state_ty: Expression,
        result_ty: Expression,
        output: Expression,
    ) -> Result<Expression, String> {
        Ok(self
            .arena()
            .alloc(SetTermNode {
                level: self
                    .arena()
                    .sort(state_ty.clone())
                    .level()
                    .ok_or("expected Set")?,
                form: SetTermForm::Finish {
                    state_ty: state_ty.try_into()?,
                    result_ty: result_ty.try_into()?,
                    output: output.try_into()?,
                },
            })
            .into())
    }
    fn product(
        &mut self,
        var: SymbolId,
        domain: Expression,
        body: Expression,
    ) -> Result<Expression, String> {
        let s = self.formation(domain.clone())?;
        let t = self.under(var, domain.clone(), |ch| ch.formation(body.clone()))?;
        build::product(self.arena(), ProductRule::new(s, t)?, var, domain, body)
    }
    fn application(
        &mut self,
        function: Expression,
        argument: Expression,
    ) -> Result<Expression, String> {
        let ty = self.inferred(function.clone())?;
        let product = self.expose_product(ty)?;
        let product = structure::product(self.arena(), product).ok_or("expected a product")?;
        self.check(argument.clone(), product.domain)?;
        build::apply(self.arena(), product.rule, function, argument)
    }
    fn expose_product(&self, mut ty: Expression) -> Result<Expression, String> {
        loop {
            ty = whnf(self.env, ty)?;
            if structure::product(self.arena(), ty.clone()).is_some() {
                return Ok(ty);
            }
            if let Some(superset) = structure::lifted_superset(self.arena(), ty) {
                ty = superset.into();
            } else {
                return Err("expected a product".into());
            }
        }
    }
    fn weaken(&self, a: Expression, b: Expression) -> Result<bool, String> {
        if convertible(self.env, a.clone(), b.clone())? {
            return Ok(true);
        }
        if a.family() != b.family() || self.arena().sort(a.clone()) != self.arena().sort(b.clone())
        {
            return Ok(false);
        }
        let a = whnf(self.env, a)?;
        let b = whnf(self.env, b)?;
        if let Some(superset) = structure::lifted_superset(self.arena(), a.clone()) {
            return self.weaken(superset.into(), b);
        }
        match (
            structure::product(self.arena(), a),
            structure::product(self.arena(), b),
        ) {
            (Some(a), Some(b))
                if a.rule == b.rule
                    && convertible(self.env, a.domain.clone(), b.domain.clone())? =>
            {
                self.weaken(a.body, b.body)
            }
            _ => Ok(false),
        }
    }
    fn common_carrier(
        &mut self,
        left: Expression,
        right: Expression,
    ) -> Result<Expression, String> {
        let left = self.inferred(left)?;
        let right = self.inferred(right)?;
        let base = |mut e| -> Result<Expression, String> {
            loop {
                e = whnf(self.env, e)?;
                if let Some(superset) = structure::lifted_superset(self.arena(), e.clone()) {
                    e = superset.into();
                } else {
                    return Ok(e);
                }
            }
        };
        let left = base(left)?;
        if !convertible(self.env, left.clone(), base(right)?)? {
            return Err("different equality carriers".into());
        }
        self.set_type(left.clone())?;
        Ok(left)
    }
    fn quantified(
        &mut self,
        domain: Expression,
        body: impl FnOnce(&mut Self, Expression) -> Result<Expression, String>,
    ) -> Result<Expression, String> {
        let sigma = self.formation(domain.clone())?;
        let stage = if sigma.is_upper() {
            Stage::Type
        } else {
            Stage::Term
        };
        let var = build::bound(self.arena(), sigma.base(), stage, 0)?;
        let body = self.under(SymbolId::ANONYMOUS, domain.clone(), |ch| body(ch, var))?;
        self.product(SymbolId::ANONYMOUS, domain, body)
    }
    fn transition(
        &mut self,
        state: Expression,
        result: Expression,
        step: Expression,
        from: Expression,
        to: Expression,
    ) -> Result<Expression, String> {
        let applied = self.application(step, from)?;
        self.equality(applied, self.continue_term(state, result, to)?)
    }

    fn infer_bound(&mut self, e: Expression, index: usize) -> Result<Expression, String> {
        let offset = index
            .checked_add(1)
            .ok_or("bound variable outside context")?;
        let entry = self
            .context
            .get(
                self.context
                    .len()
                    .checked_sub(offset)
                    .ok_or("bound variable outside context")?,
            )
            .ok_or("bound variable outside context")?;
        let classifier = shift(self.arena(), entry.classifier.clone(), offset, 0)?;
        if self.arena().sort(e.clone()).is_program()
            && e.family().stage() != Stage::Term
            && classifier.family().stage() != Stage::Kind
        {
            return Err("Program type depends on a value variable".into());
        }
        Ok(classifier)
    }
    fn infer_module_param(&mut self, parameter: ModuleParamId) -> Result<Expression, String> {
        Ok(self
            .env
            .parameter(parameter)
            .ok_or("unknown module parameter")?
            .classifier
            .clone())
    }
    fn infer_reflected_program_param(
        &mut self,
        parameter: ModuleParamId,
    ) -> Result<Expression, String> {
        super::reflection::reflect_program_expression(
            self.env,
            self.env
                .parameter(parameter)
                .ok_or("unknown reflected parameter")?
                .classifier
                .clone(),
        )
    }
    fn infer_annotation(
        &mut self,
        e: Expression,
        body: Expression,
        classifier: Classifier,
    ) -> Result<Classifier, String> {
        match classifier {
            Classifier::Expression(ref ty) => {
                self.validate_inferred(e, ty.clone())?;
                self.formation(ty.clone())?;
            }
            Classifier::Upper(sort)
                if e.family().stage() == Stage::Kind && self.arena().sort(e) == sort => {}
            _ => return Err("annotation classification mismatch".into()),
        }
        self.check(body, classifier.clone())?;
        Ok(classifier)
    }
    fn infer_product(
        &mut self,
        e: Expression,
        rule: ProductRule,
        var: SymbolId,
        domain: Expression,
        body: Expression,
    ) -> Result<Classifier, String> {
        rule.validate()?;
        let s = self.formation(domain.clone())?;
        let t = self.under(var, domain, |ch| ch.formation(body.clone()))?;
        let sort = self.arena().sort(e.clone());
        if rule.domain != s
            || rule.body != t
            || rule.result.base() != sort
            || rule.result.is_upper() != (e.family().stage() == Stage::Kind)
        {
            return Err("product rule annotation does not match its children".into());
        }
        if matches!(sort, BaseSort::Computation(_))
            && !s.is_upper()
            && contains_bound(self.arena(), body, 0)
        {
            return Err("Program function codomain depends on its value argument".into());
        }
        if e.family().stage() == Stage::Kind {
            Ok(Classifier::Upper(sort))
        } else {
            Ok(Classifier::Expression(self.base_kind(sort)))
        }
    }
    fn infer_lambda(
        &mut self,
        e: Expression,
        rule: ProductRule,
        var: SymbolId,
        domain: Expression,
        body: Expression,
    ) -> Result<Expression, String> {
        rule.validate()?;
        let s = self.formation(domain.clone())?;
        let (body_ty, t) = self.under(var, domain.clone(), |ch| {
            let ty = ch.inferred(body)?;
            Ok((ty.clone(), ch.formation(ty)?))
        })?;
        if s != rule.domain
            || t != rule.body
            || self.arena().sort(e.clone()) != rule.result.base()
            || rule.result.is_upper() != (e.family().stage() == Stage::Type)
        {
            return Err("lambda rule annotation mismatch".into());
        }
        self.product(var, domain, body_ty)
    }
    fn infer_application(
        &mut self,
        e: Expression,
        rule: ProductRule,
        function: Expression,
        argument: Expression,
    ) -> Result<Expression, String> {
        rule.validate()?;
        let ty = self.inferred(function)?;
        let ty = self.expose_product(ty)?;
        let p = structure::product(self.arena(), ty).ok_or("expected a product")?;
        if p.rule != rule
            || self.arena().sort(e.clone()) != rule.body.base()
            || rule.body.is_upper() != (e.family().stage() == Stage::Type)
        {
            return Err("application rule annotation mismatch".into());
        }
        self.check(argument.clone(), p.domain)?;
        substitute_with_reflection(self.env, p.body, argument)
    }
    fn infer_power_set(&mut self, set: Expression) -> Result<Expression, String> {
        self.set_type(set.clone())?;
        Ok(self.base_kind(self.arena().sort(set)))
    }
    fn infer_subset(
        &mut self,
        var: SymbolId,
        set: Expression,
        predicate: Expression,
    ) -> Result<Expression, String> {
        self.set_type(set.clone())?;
        self.under(var, set.clone(), |ch| ch.proposition(predicate))?;
        self.powerset(set)
    }
    fn infer_type_lift(
        &mut self,
        superset: Expression,
        subset: Expression,
    ) -> Result<Expression, String> {
        self.set_type(superset.clone())?;
        self.check(subset, self.powerset(superset.clone())?)?;
        Ok(self.base_kind(self.arena().sort(superset)))
    }
    fn infer_pred(
        &mut self,
        superset: Expression,
        subset: Expression,
        element: Expression,
    ) -> Result<Expression, String> {
        self.infer_type_lift(superset.clone(), subset)?;
        self.check(element, superset)?;
        Ok(self.base_kind(BaseSort::Prop))
    }
    fn infer_subset_intro(
        &mut self,
        superset: Expression,
        subset: Expression,
        element: Expression,
        proof: Expression,
    ) -> Result<Expression, String> {
        self.infer_pred(superset.clone(), subset.clone(), element.clone())?;
        self.check(
            proof,
            self.predicate(superset.clone(), subset.clone(), element)?,
        )?;
        self.type_lift(superset, subset)
    }
    fn infer_equal(&mut self, left: Expression, right: Expression) -> Result<Expression, String> {
        self.common_carrier(left, right)?;
        Ok(self.base_kind(BaseSort::Prop))
    }
    fn infer_exists(&mut self, set: Expression) -> Result<Expression, String> {
        self.set_type(set)?;
        Ok(self.base_kind(BaseSort::Prop))
    }
    fn infer_id_refl(&mut self, element: Expression) -> Result<Expression, String> {
        let ty = self.inferred(element.clone())?;
        self.set_type(ty)?;
        self.equality(element.clone(), element)
    }
    fn infer_exists_intro(
        &mut self,
        element: Expression,
        set: Expression,
    ) -> Result<Expression, String> {
        self.set_type(set.clone())?;
        self.check(element, set.clone())?;
        self.exists(set)
    }
    fn infer_subset_elim(
        &mut self,
        element: Expression,
        subset: Expression,
        superset: Expression,
    ) -> Result<Expression, String> {
        self.set_type(superset.clone())?;
        self.check(
            element.clone(),
            self.type_lift(superset.clone(), subset.clone())?,
        )?;
        self.predicate(superset, subset, element)
    }
    fn infer_id_elim(
        &mut self,
        var: SymbolId,
        left: Expression,
        right: Expression,
        ty: Expression,
        predicate: Expression,
        base: Expression,
        equality: Expression,
    ) -> Result<Expression, String> {
        self.set_type(ty.clone())?;
        self.check(left.clone(), ty.clone())?;
        self.check(right.clone(), ty.clone())?;
        self.under(var, ty, |ch| ch.proposition(predicate.clone()))?;
        self.check(
            base,
            substitute_with_reflection(self.env, predicate.clone(), left.clone())?,
        )?;
        self.check(equality, self.equality(left, right.clone())?)?;
        substitute_with_reflection(self.env, predicate, right)
    }
    fn check_runstep(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
    ) -> Result<Expression, String> {
        let b = self.base_type(state_ty.clone())?;
        if self.base_type(result_ty.clone())? != b
            || !matches!(b, BaseSort::Set(_) | BaseSort::Value(_))
        {
            return Err("RunStep types must share the same Set/value level".into());
        }
        self.runstep_type(state_ty, result_ty)
    }
    fn infer_run_step(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
    ) -> Result<Expression, String> {
        self.check_runstep(state_ty.clone(), result_ty)?;
        Ok(self.base_kind(self.arena().sort(state_ty)))
    }
    fn infer_continue(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
        next: Expression,
    ) -> Result<Expression, String> {
        let ty = self.check_runstep(state_ty.clone(), result_ty)?;
        self.check(next, state_ty)?;
        Ok(ty)
    }
    fn infer_finish(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
        output: Expression,
    ) -> Result<Expression, String> {
        let ty = self.check_runstep(state_ty, result_ty.clone())?;
        self.check(output, result_ty)?;
        Ok(ty)
    }
    fn check_run(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        initial: Expression,
    ) -> Result<Expression, String> {
        let runstep = self.check_runstep(state_ty.clone(), result_ty)?;
        let step_ty = if self.arena().sort(state_ty.clone()).is_program() {
            let result = self.return_type(runstep.clone())?;
            let arrow = self.arrow(state_ty.clone(), result)?;
            self.thunk_type(arrow)?
        } else {
            self.arrow(state_ty.clone(), runstep.clone())?
        };
        self.check(step, step_ty)?;
        self.check(initial, state_ty)?;
        Ok(runstep)
    }
    fn infer_acc(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        state: Expression,
    ) -> Result<Expression, String> {
        self.check_run(state_ty, result_ty, step, state)?;
        Ok(self.base_kind(BaseSort::Prop))
    }
    fn infer_set_run(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        initial: Expression,
        accessibility: Expression,
    ) -> Result<Expression, String> {
        self.check_run(
            state_ty.clone(),
            result_ty.clone(),
            step.clone(),
            initial.clone(),
        )?;
        self.check(
            accessibility,
            self.accessibility(state_ty, result_ty.clone(), step, initial)?,
        )?;
        Ok(result_ty)
    }
    fn infer_set_run_case(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        initial: Expression,
        transition: Expression,
        accessibility: Expression,
        transition_equality: Expression,
    ) -> Result<Expression, String> {
        let runstep = self.check_run(
            state_ty.clone(),
            result_ty.clone(),
            step.clone(),
            initial.clone(),
        )?;
        self.check(
            accessibility,
            self.accessibility(state_ty, result_ty.clone(), step.clone(), initial.clone())?,
        )?;
        self.check(transition.clone(), runstep)?;
        let applied = self.application(step, initial)?;
        self.check(transition_equality, self.equality(applied, transition)?)?;
        Ok(result_ty)
    }
    fn check_reflected_program_run(&self, term: ComputationTerm) -> Result<(), String> {
        let context = super::reflection::reflect_context(self.env, &self.context)?;
        let reflected = super::reflection::reflect_term(self.env, term.into())?;
        Checker::new(self.env, context).infer_set_term(reflected)?;
        Ok(())
    }
    fn infer_recursor(
        &mut self,
        rule: ProductRule,
        var: SymbolId,
        state_ty: Expression,
        result_ty: Expression,
        motive: Expression,
        on_continue: Expression,
        on_finish: Expression,
        scrutinee: Expression,
    ) -> Result<Expression, String> {
        let i = self.set_type(state_ty.clone())?;
        if self.set_type(result_ty.clone())? != i {
            return Err("RunStep types must share a level".into());
        }
        let step = self.runstep_type(state_ty.clone(), result_ty.clone())?;
        self.check(scrutinee.clone(), step.clone())?;
        let sigma = self.under(var, step, |ch| ch.formation(motive.clone()))?;
        if rule != ProductRule::new(Sort::Base(BaseSort::Set(i)), sigma)? {
            return Err("recursor rule mismatch".into());
        }
        let state = shift(self.arena(), state_ty.clone(), 1, 0)?;
        let result = shift(self.arena(), result_ty.clone(), 1, 0)?;
        let bound = build::bound(self.arena(), BaseSort::Set(i), Stage::Term, 0)?;
        let continue_value = self.continue_term(state.clone(), result.clone(), bound.clone())?;
        let finish_value = self.finish_term(state, result, bound)?;
        for (domain, branch, constructor) in [
            (state_ty, on_continue, continue_value),
            (result_ty, on_finish, finish_value),
        ] {
            let motive = shift(self.arena(), motive.clone(), 1, 1)?;
            let ty = substitute_with_reflection(self.env, motive, constructor)?;
            let expected = self.product(SymbolId::ANONYMOUS, domain, ty)?;
            self.check(branch, expected)?;
        }
        substitute_with_reflection(self.env, motive, scrutinee)
    }
    fn infer_thunk(&mut self, computation_ty: Expression) -> Result<Expression, String> {
        match self.base_type(computation_ty)? {
            BaseSort::Computation(i) => Ok(self.base_kind(BaseSort::Value(i))),
            _ => Err("U argument has wrong domain".into()),
        }
    }
    fn infer_return_type(&mut self, value_ty: Expression) -> Result<Expression, String> {
        match self.base_type(value_ty)? {
            BaseSort::Value(i) => Ok(self.base_kind(BaseSort::Computation(i))),
            _ => Err("F argument has wrong domain".into()),
        }
    }
    fn infer_thunk_value(&mut self, computation: Expression) -> Result<Expression, String> {
        let ty = self.inferred(computation)?;
        self.thunk_type(ty)
    }
    fn infer_return(&mut self, value: Expression) -> Result<Expression, String> {
        let ty = self.inferred(value)?;
        self.return_type(ty)
    }
    fn infer_force(&mut self, value: Expression) -> Result<Expression, String> {
        let ty = self.inferred(value)?;
        let ty: ValueType = whnf(self.env, ty)?.try_into()?;
        match self.arena().get(ty).form {
            ValueTypeForm::Thunk { computation_ty } => Ok(computation_ty.into()),
            _ => Err("force requires U(B)".into()),
        }
    }
    fn infer_value_binding(
        &mut self,
        var: SymbolId,
        value_ty: Expression,
        argument: Expression,
        body: Expression,
        sequence: bool,
    ) -> Result<Expression, String> {
        if !matches!(self.base_type(value_ty.clone())?, BaseSort::Value(_)) {
            return Err("value binder requires value type".into());
        }
        let expected = if sequence {
            self.return_type(value_ty.clone())?
        } else {
            value_ty.clone()
        };
        self.check(argument.clone(), expected)?;
        let ty = self.under(var, value_ty, |ch| ch.inferred(body))?;
        if contains_bound(self.arena(), ty.clone(), 0) {
            return Err("Program result type depends on value".into());
        }
        substitute_with_reflection(self.env, ty, argument)
    }
    fn infer_sequence(
        &mut self,
        var: SymbolId,
        value_ty: Expression,
        computation: Expression,
        body: Expression,
    ) -> Result<Expression, String> {
        self.infer_value_binding(var, value_ty, computation, body, true)
    }
    fn infer_value_let(
        &mut self,
        var: SymbolId,
        value_ty: Expression,
        value: Expression,
        body: Expression,
    ) -> Result<Expression, String> {
        self.infer_value_binding(var, value_ty, value, body, false)
    }
    fn infer_box_type(&mut self, program_ty: Expression) -> Result<Expression, String> {
        self.closed_program_type(program_ty.clone())?;
        Ok(self.base_kind(self.arena().sort(program_ty).reflected()))
    }
    fn infer_box_program(
        &mut self,
        program_ty: Expression,
        program: Expression,
    ) -> Result<Expression, String> {
        self.closed_program_type(program_ty.clone())?;
        if !closed_in_environment(self.env, program.clone()) {
            return Err("Box payload must be closed".into());
        }
        let mut closed = Checker::new(self.env, vec![]);
        closed.check(program.clone(), program_ty.clone())?;
        let reflected = super::reflection::reflect_program_expression(self.env, program)?;
        let reflected_ty =
            super::reflection::reflect_program_expression(self.env, program_ty.clone())?;
        closed.check(reflected, reflected_ty)?;
        self.box_type(program_ty)
    }
    fn infer_force_box(
        &mut self,
        program_ty: Expression,
        boxed: Expression,
    ) -> Result<Expression, String> {
        self.closed_program_type(program_ty.clone())?;
        self.check(boxed, self.box_type(program_ty.clone())?)?;
        super::reflection::reflect_program_expression(self.env, program_ty)
    }
    fn infer_box_application(
        &mut self,
        rule: ProductRule,
        var: SymbolId,
        domain: Expression,
        codomain: Expression,
        function: Expression,
        argument: Expression,
        type_application: bool,
    ) -> Result<Expression, String> {
        self.formation(domain.clone())?;
        let body = if type_application {
            codomain.clone()
        } else {
            shift(self.arena(), codomain.clone(), 1, 0)?
        };
        let p = self.product(var, domain.clone(), body)?;
        if structure::product(self.arena(), p.clone())
            .ok_or("expected product")?
            .rule
            != rule
        {
            return Err("boxed application rule mismatch".into());
        }
        self.closed_program_type(p.clone())?;
        self.check(function, self.box_type(p)?)?;
        let result = if type_application {
            if !closed_in_environment(self.env, argument.clone()) {
                return Err("boxed type argument must be closed".into());
            }
            self.check(argument.clone(), domain)?;
            substitute_with_reflection(self.env, codomain, argument)?
        } else {
            let argument_ty = self.return_type(domain)?;
            self.closed_program_type(argument_ty.clone())?;
            self.check(argument, self.box_type(argument_ty)?)?;
            codomain
        };
        self.box_type(result)
    }
    fn infer_box_app(
        &mut self,
        rule: ProductRule,
        domain: Expression,
        codomain: Expression,
        function: Expression,
        argument: Expression,
    ) -> Result<Expression, String> {
        self.infer_box_application(
            rule,
            SymbolId::ANONYMOUS,
            domain,
            codomain,
            function,
            argument,
            false,
        )
    }
    fn infer_box_type_app(
        &mut self,
        rule: ProductRule,
        var: SymbolId,
        domain: Expression,
        codomain: Expression,
        function: Expression,
        argument: Expression,
    ) -> Result<Expression, String> {
        self.infer_box_application(rule, var, domain, codomain, function, argument, true)
    }
    fn infer_take_set(
        &mut self,
        domain: Expression,
        codomain: Expression,
        map: Expression,
        existence: Expression,
        uniqueness: Expression,
    ) -> Result<Expression, String> {
        if self.set_type(codomain.clone())? != self.set_type(domain.clone())? {
            return Err("TakeSet domain/codomain level mismatch".into());
        }
        let map_ty = self.arrow(domain.clone(), codomain.clone())?;
        self.check(map.clone(), map_ty)?;
        self.check(existence, self.exists(domain.clone())?)?;
        let unique = self.quantified(domain.clone(), |ch, x| {
            let dom = ch.lifted(domain, 1)?;
            ch.quantified(dom, |ch, y| {
                let f = ch.lifted(map, 2)?;
                let x = ch.lifted(x, 1)?;
                let left = ch.application(f.clone(), x)?;
                let right = ch.application(f, y)?;
                ch.equality(left, right)
            })
        })?;
        self.check(uniqueness, unique)?;
        Ok(codomain)
    }
    fn infer_take_prop(
        &mut self,
        domain: Expression,
        proposition: Expression,
        map: Expression,
        existence: Expression,
    ) -> Result<Expression, String> {
        self.set_type(domain.clone())?;
        self.proposition(proposition.clone())?;
        let map_ty = self.arrow(domain.clone(), proposition.clone())?;
        self.check(map, map_ty)?;
        self.check(existence, self.exists(domain)?)?;
        Ok(proposition)
    }
    fn infer_take_eq(
        &mut self,
        func: Expression,
        domain: Expression,
        codomain: Expression,
        element: Expression,
        existence: Expression,
        uniqueness: Expression,
    ) -> Result<Expression, String> {
        let take = self.arena().alloc(SetTermNode {
            level: self
                .arena()
                .sort(codomain.clone())
                .level()
                .ok_or("expected Set")?,
            form: SetTermForm::TakeSet {
                domain: domain.clone().try_into()?,
                codomain: codomain.clone().try_into()?,
                map: func.clone().try_into()?,
                existence: existence.try_into()?,
                uniqueness: uniqueness.try_into()?,
            },
        });
        self.check(take.clone(), codomain)?;
        self.check(element.clone(), domain)?;
        let mapped = self.application(func, element)?;
        self.equality(take.into(), mapped)
    }
    fn infer_fun_ext(
        &mut self,
        left: Expression,
        right: Expression,
        pointwise: Expression,
    ) -> Result<Expression, String> {
        let ty = self.inferred(left.clone())?;
        self.set_type(ty.clone())?;
        let product = self.expose_product(ty.clone())?;
        let domain = structure::product(self.arena(), product)
            .ok_or("expected product")?
            .domain;
        self.check(right.clone(), ty)?;
        let expected = self.quantified(domain, |ch, x| {
            let left = ch.lifted(left.clone(), 1)?;
            let right = ch.lifted(right.clone(), 1)?;
            let left = ch.application(left, x.clone())?;
            let right = ch.application(right, x)?;
            ch.equality(left, right)
        })?;
        self.check(pointwise, expected)?;
        self.equality(left, right)
    }
    fn infer_set_ext(
        &mut self,
        left: Expression,
        right: Expression,
        left_to_right: Expression,
        right_to_left: Expression,
    ) -> Result<Expression, String> {
        let ty = self.inferred(left.clone())?;
        let carrier: Expression = structure::power_set(self.arena(), whnf(self.env, ty.clone())?)
            .ok_or("setext requires powerset elements")?
            .into();
        self.set_type(carrier.clone())?;
        self.check(right.clone(), ty)?;
        for (source, target, proof) in [
            (left.clone(), right.clone(), left_to_right),
            (right.clone(), left.clone(), right_to_left),
        ] {
            let direction = self.quantified(carrier.clone(), |ch, x| {
                let carrier = ch.lifted(carrier.clone(), 1)?;
                let source = ch.lifted(source, 1)?;
                let target = ch.lifted(target, 1)?;
                ch.arrow(
                    ch.predicate(carrier.clone(), source, x.clone())?,
                    ch.predicate(carrier, target, x)?,
                )
            })?;
            self.check(proof, direction)?;
        }
        self.equality(left, right)
    }
    fn infer_classical_indefinite_choice(
        &mut self,
        domain: Expression,
        family: Expression,
        inhabited: Expression,
    ) -> Result<Expression, String> {
        self.set_type(domain.clone())?;
        let ty = self.inferred(family.clone())?;
        let p = self.expose_product(ty)?;
        let p = structure::product(self.arena(), p).ok_or("expected product")?;
        if !convertible(self.env, p.domain, domain.clone())? {
            return Err("choice family domain mismatch".into());
        }
        let tail = whnf(self.env, p.body)?;
        if !structure::is_base(self.arena(), tail.clone())
            || !matches!(self.arena().sort(tail), BaseSort::Set(_))
        {
            return Err("choice family must return Set".into());
        }
        let exists = self.quantified(domain.clone(), |ch, x| {
            let f = ch.lifted(family.clone(), 1)?;
            let at = ch.application(f, x)?;
            ch.exists(at)
        })?;
        self.check(inhabited, exists)?;
        let choices = self.quantified(domain, |ch, x| {
            let f = ch.lifted(family, 1)?;
            ch.application(f, x)
        })?;
        self.exists(choices)
    }
    fn infer_acc_intro(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        state: Expression,
        predecessors: Expression,
    ) -> Result<Expression, String> {
        let acc = self.accessibility(
            state_ty.clone(),
            result_ty.clone(),
            step.clone(),
            state.clone(),
        )?;
        self.proposition(acc.clone())?;
        let expected = self.quantified(state_ty.clone(), |ch, x| {
            let a = ch.lifted(state_ty, 1)?;
            let b = ch.lifted(result_ty, 1)?;
            let f = ch.lifted(step, 1)?;
            let from = ch.lifted(state, 1)?;
            let transition = ch.transition(a.clone(), b.clone(), f.clone(), from, x.clone())?;
            ch.arrow(transition, ch.accessibility(a, b, f, x)?)
        })?;
        self.check(predecessors, expected)?;
        Ok(acc)
    }
    fn infer_acc_descent(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        from: Expression,
        to: Expression,
        accessibility: Expression,
        transition: Expression,
    ) -> Result<Expression, String> {
        let acc = self.accessibility(
            state_ty.clone(),
            result_ty.clone(),
            step.clone(),
            from.clone(),
        )?;
        self.proposition(acc.clone())?;
        self.check(to.clone(), state_ty.clone())?;
        self.check(accessibility, acc)?;
        let expected = self.transition(
            state_ty.clone(),
            result_ty.clone(),
            step.clone(),
            from,
            to.clone(),
        )?;
        self.check(transition, expected)?;
        self.accessibility(state_ty, result_ty, step, to)
    }

    fn infer_ind_type(
        &mut self,
        e: Expression,
        inductive: InductiveId,
        parameters: Vec<LogicalArgument>,
    ) -> Result<Classifier, String> {
        let spec = self
            .env
            .inductive(inductive)
            .ok_or("unknown inductive")?
            .clone();
        let parameters = expressions(&parameters);
        self.check_arguments(&parameters, &spec.parameters)?;
        if e.family().stage() == Stage::Kind {
            if spec.sort != Sort::Upper(self.arena().sort(e.clone())) {
                return Err("inductive kind index mismatch".into());
            }
            return Ok(Classifier::Upper(self.arena().sort(e)));
        }
        let ty = instantiate_telescope(self.env, spec.arity, &parameters)?;
        self.validate_inferred(e, ty.clone())?;
        Ok(Classifier::Expression(ty))
    }
    fn infer_ind_ctor(
        &mut self,
        inductive: InductiveId,
        constructor: usize,
        parameters: Vec<LogicalArgument>,
    ) -> Result<Expression, String> {
        let spec = self
            .env
            .inductive(inductive)
            .ok_or("unknown inductive")?
            .clone();
        let parameters = expressions(&parameters);
        self.check_arguments(&parameters, &spec.parameters)?;
        let classifier = spec
            .constructors
            .get(constructor)
            .ok_or("invalid constructor")?;
        instantiate_telescope(self.env, classifier.clone(), &parameters)
    }
    fn infer_inductive(
        &mut self,
        inductive: ProgramInductiveId,
        parameters: Vec<ProgramType>,
    ) -> Result<Expression, String> {
        let spec = self
            .env
            .datatype(inductive)
            .ok_or("unknown Program datatype")?
            .clone();
        self.check_arguments(&expressions(&parameters), &spec.parameters)?;
        Ok(self.base_kind(BaseSort::Value(spec.level)))
    }
    fn infer_inductive_constructor(
        &mut self,
        inductive: ProgramInductiveId,
        constructor: usize,
        parameters: Vec<ProgramType>,
        fields: Vec<ValueTerm>,
    ) -> Result<Expression, String> {
        let spec = self
            .env
            .datatype(inductive)
            .ok_or("unknown Program datatype")?
            .clone();
        let args = expressions(&parameters);
        self.check_arguments(&args, &spec.parameters)?;
        let declared = spec
            .constructors
            .get(constructor)
            .ok_or("invalid constructor")?;
        if declared.len() != fields.len() {
            return Err("constructor field count mismatch".into());
        }
        for (field, (_, ty)) in fields.iter().zip(declared) {
            self.check(
                field,
                instantiate_telescope(self.env, ty.clone().into(), &args)?,
            )?;
        }
        Ok(self
            .arena()
            .alloc(ValueTypeNode {
                level: spec.level,
                form: ValueTypeForm::Inductive {
                    inductive,
                    parameters,
                },
            })
            .into())
    }
    fn infer_case(
        &mut self,
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
        result_ty: Expression,
        scrutinee: Expression,
        branches: Vec<ComputationTerm>,
    ) -> Result<Expression, String> {
        self.check_case(
            inductive,
            binders,
            result_ty,
            scrutinee,
            expressions(&branches),
            false,
        )
    }
    fn infer_set_case(
        &mut self,
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
        result_ty: Expression,
        scrutinee: Expression,
        branches: Vec<SetTerm>,
    ) -> Result<Expression, String> {
        self.check_case(
            inductive,
            binders,
            result_ty,
            scrutinee,
            expressions(&branches),
            true,
        )
    }
    fn check_case(
        &mut self,
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
        result_ty: Expression,
        scrutinee: Expression,
        branches: Vec<Expression>,
        reflected: bool,
    ) -> Result<Expression, String> {
        let spec = self
            .env
            .datatype(inductive)
            .ok_or("unknown datatype")?
            .clone();
        self.base_type(result_ty.clone())?;
        let ty = self.inferred(scrutinee)?;
        let head = whnf(self.env, ty)?;
        let parameters = if reflected {
            let (id, parameters) = structure::inductive_type(self.arena(), head)
                .ok_or("case scrutinee datatype mismatch")?;
            if id != spec.reflected {
                return Err("case scrutinee datatype mismatch".into());
            }
            expressions(&parameters)
        } else {
            let (id, parameters) = structure::program_inductive(self.arena(), head)
                .ok_or("case scrutinee datatype mismatch")?;
            if id != inductive {
                return Err("case scrutinee datatype mismatch".into());
            }
            expressions(&parameters)
        };
        if binders.len() != spec.constructors.len() || branches.len() != binders.len() {
            return Err("case branch count mismatch".into());
        }
        for (i, fields) in spec.constructors.iter().enumerate() {
            if fields.len() != binders[i].len() {
                return Err("case branch binder count mismatch".into());
            }
            let mut branch = Checker::new(self.env, self.context.clone());
            for (j, (_, field)) in fields.iter().enumerate() {
                let field = if reflected {
                    super::reflection::reflect_type(self.env, field.clone().into())?.into()
                } else {
                    field.clone().into()
                };
                let ty = instantiate_telescope(self.env, field, &parameters)?;
                branch.context.push(Binding {
                    var: binders[i][j],
                    classifier: shift(self.arena(), ty, j, 0)?,
                });
            }
            branch.check(
                branches[i].clone(),
                shift(self.arena(), result_ty.clone(), fields.len(), 0)?,
            )?;
        }
        Ok(result_ty)
    }
    fn infer_ind_elim(
        &mut self,
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: Expression,
        motive_domains: Vec<LogicalExpression>,
        motive_body: Expression,
        cases: Vec<LogicalArgument>,
    ) -> Result<Expression, String> {
        self.infer_inductive_elimination(
            inductive,
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            cases,
            true,
        )
    }
    #[allow(clippy::too_many_arguments)]
    fn infer_inductive_elimination(
        &mut self,
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: Expression,
        motive_domains: Vec<LogicalExpression>,
        motive_body: Expression,
        cases: Vec<LogicalArgument>,
        recursive: bool,
    ) -> Result<Expression, String> {
        let spec = self
            .env
            .inductive(inductive)
            .ok_or("unknown inductive")?
            .clone();
        let scrutinee_ty = self.inferred(scrutinee.clone())?;
        let mut head = whnf(self.env, scrutinee_ty)?;
        while let Some(superset) = structure::lifted_superset(self.arena(), head.clone()) {
            head = whnf(self.env, superset.into())?;
        }
        let (head, args) = self.decompose_app(head);
        let (id, parameters) = structure::inductive_type(self.arena(), head)
            .ok_or("eliminator scrutinee datatype mismatch")?;
        if id != inductive {
            return Err("eliminator scrutinee datatype mismatch".into());
        }
        let params = expressions(&parameters);
        if cases.len() != spec.constructors.len() {
            return Err("eliminator case count mismatch".into());
        }
        let motive = Motive {
            domains: expressions(&motive_domains),
            body: motive_body,
        };
        if motive.domains.len() != motive_vars.len() || motive.domains.len() != args.len() + 1 {
            return Err("motive telescope length mismatch".into());
        }
        let mut local = Checker::new(self.env, self.context.clone());
        for (var, domain) in motive_vars.iter().zip(&motive.domains) {
            local.formation(domain.clone())?;
            local.context.push(Binding {
                var: *var,
                classifier: domain.clone(),
            });
        }
        let result_sort = local.formation(motive.body.clone())?;
        let permitted = match (spec.sort, result_sort) {
            (Sort::Base(BaseSort::Set(i)), Sort::Base(BaseSort::Set(j))) => i <= j,
            (_, Sort::Base(BaseSort::Prop))
            | (
                Sort::Base(BaseSort::Set(_)) | Sort::Upper(BaseSort::Prop),
                Sort::Upper(BaseSort::Prop),
            ) => true,
            _ => self.env.singleton_elimination(inductive),
        };
        if !permitted {
            return Err("forbidden large elimination".into());
        }
        let mut applied_args = args;
        applied_args.push(scrutinee);
        let applied = self.apply_motive(&motive, &applied_args)?;
        for (i, case) in cases.into_iter().enumerate() {
            let ctor_ty = instantiate_telescope(self.env, spec.constructors[i].clone(), &params)?;
            let sigma = self.formation(ctor_ty.clone())?;
            let ctor = build::inductive_constructor(
                self.arena(),
                sigma.base(),
                if sigma.is_upper() {
                    Stage::Type
                } else {
                    Stage::Term
                },
                inductive,
                i,
                parameters.clone(),
            )?;
            let expected = if recursive {
                self.case_type(
                    inductive,
                    spec.constructors[i].clone(),
                    ctor_ty,
                    ctor,
                    &motive,
                )?
            } else {
                self.case_match_type(ctor_ty, ctor, &motive)?
            };
            self.check(case, expected)?;
        }
        Ok(applied)
    }
    fn infer_inductive_case(
        &mut self,
        inductive: InductiveId,
        motive_vars: Vec<SymbolId>,
        scrutinee: Expression,
        motive_domains: Vec<LogicalExpression>,
        motive_body: Expression,
        branches: Vec<LogicalArgument>,
    ) -> Result<Expression, String> {
        self.infer_inductive_elimination(
            inductive,
            motive_vars,
            scrutinee,
            motive_domains,
            motive_body,
            branches,
            false,
        )
    }
    fn case_match_type(
        &mut self,
        constructor_ty: Expression,
        constructor: Expression,
        motive: &Motive,
    ) -> Result<Expression, String> {
        let constructor_ty = whnf(self.env, constructor_ty)?;
        if let Some(product) = structure::product(self.arena(), constructor_ty.clone()) {
            return self.quantified(product.domain, |ch, field| {
                let constructor = ch.application(ch.lifted(constructor, 1)?, field)?;
                let motive = ch.lift_motive(motive)?;
                ch.case_match_type(product.body, constructor, &motive)
            });
        }
        let (_, mut args) = self.decompose_app(constructor_ty);
        args.push(constructor);
        self.apply_motive(motive, &args)
    }
    fn decompose_app(&self, e: Expression) -> (Expression, Vec<Expression>) {
        decompose_application(self.arena(), e)
    }
    fn recursive_hypothesis(
        &mut self,
        ind: InductiveId,
        ty: Expression,
        x: Expression,
        motive: &Motive,
    ) -> Result<Option<Expression>, String> {
        let ty = whnf(self.env, ty)?;
        if let Some(product) = structure::product(self.arena(), ty.clone()) {
            let mut found = false;
            let result = self.quantified(product.domain, |ch, arg| {
                let x = ch.lifted(x, 1)?;
                let x = ch.application(x, arg)?;
                let motive = ch.lift_motive(motive)?;
                match ch.recursive_hypothesis(ind, product.body, x, &motive)? {
                    Some(ih) => {
                        found = true;
                        Ok(ih)
                    }
                    None => Ok(ch.base_kind(BaseSort::Prop)),
                }
            })?;
            return Ok(found.then_some(result));
        }
        let (head, mut args) = self.decompose_app(ty);
        if !structure::inductive_type(self.arena(), head).is_some_and(|(id, _)| id == ind) {
            return Ok(None);
        }
        args.push(x);
        self.apply_motive(motive, &args).map(Some)
    }
    fn case_type(
        &mut self,
        ind: InductiveId,
        declared_ty: Expression,
        ty: Expression,
        ctor: Expression,
        motive: &Motive,
    ) -> Result<Expression, String> {
        let ty = whnf(self.env, ty)?;
        if let Some(product) = structure::product(self.arena(), ty.clone()) {
            let declared = structure::product(self.arena(), whnf(self.env, declared_ty.clone())?)
                .ok_or("expected declared constructor product")?;
            let recursive = recursive_constructor_field(self.env, ind, declared.domain.clone())?;
            return self.quantified(product.domain.clone(), |ch, x| {
                let ctor = ch.lifted(ctor, 1)?;
                let ctor = ch.application(ctor, x.clone())?;
                let motive = ch.lift_motive(motive)?;
                let tail = ch.case_type(ind, declared.body, product.body, ctor, &motive)?;
                let domain = ch.lifted(product.domain.clone(), 1)?;
                if recursive && let Some(ih) = ch.recursive_hypothesis(ind, domain, x, &motive)? {
                    ch.arrow(ih, tail)
                } else {
                    Ok(tail)
                }
            });
        }
        let (_, mut args) = self.decompose_app(ty);
        args.push(ctor);
        self.apply_motive(motive, &args)
    }
}
struct Motive {
    domains: Vec<Expression>,
    body: Expression,
}
