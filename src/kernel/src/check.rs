//! Independent formation and typing checks for indexed syntax.
use super::{calculus::*, environment::*, sort::*, syntax::*};
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
            .map(|b| b.classifier)
            .collect::<Vec<_>>();
        if self.validated_context.as_ref() == Some(&key) {
            return Ok(());
        }
        if let Some(first) = key.first() {
            let program = self.arena().sort(*first).is_program();
            if key
                .iter()
                .any(|e| self.arena().sort(*e).is_program() != program)
            {
                return Err("Set/Prop and Program contexts are separate".into());
            }
        }
        let was_checking = self.checking_context;
        self.checking_context = true;
        let entries = std::mem::take(&mut self.context);
        let result = (|| {
            for entry in &entries {
                self.formation(entry.classifier)?;
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
                let d = self.arena().data(k);
                if k.family().stage() == Stage::Kind && d.op == Op::Base {
                    Ok(Sort::Base(d.sort))
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
                self.formation(b)?;
                if self.weaken(a, b)? {
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

    fn weaken(&self, a: Expression, b: Expression) -> Result<bool, String> {
        if convertible(self.env, a, b)? {
            return Ok(true);
        }
        if a.family() != b.family() || self.arena().sort(a) != self.arena().sort(b) {
            return Ok(false);
        }
        let a = whnf(self.env, a)?;
        let b = whnf(self.env, b)?;
        let d = self.arena().data(a);
        let e = self.arena().data(b);
        if d.op == Op::TypeLift {
            return self.weaken(d.child(0), b);
        }
        match (&d.op, &e.op) {
            (Op::ProdTerm { rule: r, .. }, Op::ProdTerm { rule: s, .. })
            | (Op::ProdType { rule: r, .. }, Op::ProdType { rule: s, .. })
                if r == s && convertible(self.env, d.child(0), e.child(0))? =>
            {
                self.weaken(d.child(1), e.child(1))
            }
            _ => Ok(false),
        }
    }

    fn base_kind(&self, b: BaseSort) -> Expression {
        node(self.arena(), Family::at(b, Stage::Kind), b, Op::Base, &[])
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

    fn make(
        &self,
        sort: BaseSort,
        stage: Stage,
        op: Op,
        children: &[(Expression, usize)],
    ) -> Expression {
        node(self.arena(), Family::at(sort, stage), sort, op, children)
    }

    fn type_node(&self, sort: BaseSort, op: Op, args: &[Expression]) -> Expression {
        self.make(
            sort,
            Stage::Type,
            op,
            &args.iter().map(|&e| (e, 0)).collect::<Vec<_>>(),
        )
    }

    fn product(
        &mut self,
        var: SymbolId,
        domain: Expression,
        body: Expression,
    ) -> Result<Expression, String> {
        let s = self.formation(domain)?;
        let t = self.under(var, domain, |c| c.formation(body))?;
        let rule = ProductRule::new(s, t)?;
        Ok(self.make(
            rule.result.base(),
            if rule.result.is_upper() {
                Stage::Kind
            } else {
                Stage::Type
            },
            if s.is_upper() {
                Op::ProdType { var, rule }
            } else {
                Op::ProdTerm { var, rule }
            },
            &[(domain, 0), (body, 1)],
        ))
    }

    fn arrow(&mut self, domain: Expression, codomain: Expression) -> Result<Expression, String> {
        let body = shift(self.arena(), codomain, 1, 0)?;
        self.product(SymbolId::ANONYMOUS, domain, body)
    }

    fn application(
        &mut self,
        function: Expression,
        argument: Expression,
    ) -> Result<Expression, String> {
        let ty = self.inferred(function)?;
        let ty = self.expose_product(ty)?;
        let d = self.arena().data(ty);
        let rule = match d.op {
            Op::ProdTerm { rule, .. } | Op::ProdType { rule, .. } => rule,
            _ => unreachable!(),
        };
        self.check(argument, d.child(0))?;
        Ok(apply(self.arena(), rule, function, argument))
    }

    fn expose_product(&self, mut ty: Expression) -> Result<Expression, String> {
        loop {
            ty = whnf(self.env, ty)?;
            let d = self.arena().data(ty);
            match d.op {
                Op::ProdTerm { .. } | Op::ProdType { .. } => return Ok(ty),
                Op::TypeLift => ty = d.child(0),
                _ => return Err("expected a product".into()),
            }
        }
    }

    fn common_carrier(&mut self, l: Expression, r: Expression) -> Result<Expression, String> {
        let l = self.inferred(l)?;
        let r = self.inferred(r)?;
        let base = |mut e| -> Result<Expression, String> {
            loop {
                e = whnf(self.env, e)?;
                let d = self.arena().data(e);
                if d.op == Op::TypeLift {
                    e = d.child(0)
                } else {
                    return Ok(e);
                }
            }
        };
        let l = base(l)?;
        let r = base(r)?;
        if !convertible(self.env, l, r)? {
            return Err("different equality carriers".into());
        }
        self.set_type(l)?;
        Ok(l)
    }

    pub fn infer(&mut self, e: impl Into<Expression>) -> Result<Classifier, String> {
        let e = e.into();
        if self.inference_depth == 0 && !self.checking_context {
            self.check_context()?
        }
        let key = (e, self.context.iter().map(|b| b.classifier).collect());
        if let Some(&result) = self.env.inference_cache.borrow().get(&key) {
            return Ok(result);
        }
        self.inference_depth += 1;
        let result = self.infer_inner(e);
        self.inference_depth -= 1;
        let result = result?;
        self.env.inference_cache.borrow_mut().insert(key, result);
        Ok(result)
    }

    fn infer_inner(&mut self, e: Expression) -> Result<Classifier, String> {
        let d = self.arena().data(e);
        let sort = d.sort;
        let stage = e.family().stage();
        if Family::at(sort, stage) != e.family() {
            return Err("node sort does not match its arena partition".into());
        }
        let c = |i| d.child(i);
        let inferred = match d.op.clone() {
            Op::Base => {
                if stage != Stage::Kind {
                    return Err("base sorts belong to kind syntax".into());
                }
                return Ok(Classifier::Upper(sort));
            }
            Op::Bound { index } => {
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
                let classifier = shift(self.arena(), entry.classifier, offset, 0)?;
                if sort.is_program()
                    && stage != Stage::Term
                    && classifier.family().stage() != Stage::Kind
                {
                    return Err("Program type depends on a value variable".into());
                }
                classifier
            }
            Op::ModuleParam { parameter } => {
                self.env
                    .parameter(parameter)
                    .ok_or("unknown module parameter")?
                    .classifier
            }
            Op::ReflectedProgramParam { parameter } => {
                let ty = self
                    .env
                    .parameter(parameter)
                    .ok_or("unknown reflected parameter")?
                    .classifier;
                super::reflection::reflect(self.env, ty)?
            }
            Op::Constant { definition } => match self
                .env
                .definition(definition)
                .ok_or("unknown definition")?
                .classifier
            {
                Classifier::Expression(t) => t,
                Classifier::Upper(b) => {
                    if stage == Stage::Kind && sort == b {
                        return Ok(Classifier::Upper(b));
                    }
                    return Err("constant classification mismatch".into());
                }
            },
            Op::ProdTerm { rule, var } | Op::ProdType { rule, var } => {
                rule.validate()?;
                let s = self.formation(c(0))?;
                let t = self.under(var, c(0), |ch| ch.formation(c(1)))?;
                if rule.domain != s
                    || rule.body != t
                    || rule.result.base() != sort
                    || rule.result.is_upper() != (stage == Stage::Kind)
                {
                    return Err("product rule annotation does not match its children".into());
                }
                if matches!(sort, BaseSort::Computation(_))
                    && !s.is_upper()
                    && contains_bound(self.arena(), c(1), 0)
                {
                    return Err("Program function codomain depends on its value argument".into());
                }
                if stage == Stage::Kind {
                    return Ok(Classifier::Upper(sort));
                }
                self.base_kind(sort)
            }
            Op::LambdaTerm { rule, var } | Op::LambdaType { rule, var } => {
                rule.validate()?;
                let s = self.formation(c(0))?;
                let (body_ty, t) = self.under(var, c(0), |ch| {
                    let body_ty = ch.inferred(c(1))?;
                    let t = ch.formation(body_ty)?;
                    Ok((body_ty, t))
                })?;
                if s != rule.domain
                    || t != rule.body
                    || sort != rule.result.base()
                    || rule.result.is_upper() != (stage == Stage::Type)
                {
                    return Err("lambda rule annotation mismatch".into());
                }
                self.product(var, c(0), body_ty)?
            }
            Op::AppTerm { rule } | Op::AppType { rule } => {
                rule.validate()?;
                let fty = self.inferred(c(0))?;
                let p = self.expose_product(fty)?;
                let p = self.arena().data(p);
                let expected = match p.op {
                    Op::ProdTerm { rule, .. } | Op::ProdType { rule, .. } => rule,
                    _ => unreachable!(),
                };
                if expected != rule
                    || sort != rule.body.base()
                    || rule.body.is_upper() != (stage == Stage::Type)
                {
                    return Err("application rule annotation mismatch".into());
                }
                self.check(c(1), p.child(0))?;
                substitute(self.arena(), p.child(1), c(1))?
            }
            Op::PowerSet => {
                self.set_type(c(0))?;
                self.base_kind(self.arena().sort(c(0)))
            }
            Op::Subset { var } => {
                self.set_type(c(0))?;
                self.under(var, c(0), |ch| ch.proposition(c(1)))?;
                self.type_node(self.arena().sort(c(0)), Op::PowerSet, &[c(0)])
            }
            Op::TypeLift | Op::Pred | Op::SubsetIntro => {
                self.set_type(c(0))?;
                let power = self.type_node(self.arena().sort(c(0)), Op::PowerSet, &[c(0)]);
                self.check(c(1), power)?;
                match d.op {
                    Op::TypeLift => self.base_kind(self.arena().sort(c(0))),
                    Op::Pred => {
                        self.check(c(2), c(0))?;
                        self.base_kind(BaseSort::Prop)
                    }
                    _ => {
                        self.check(c(2), c(0))?;
                        let p = self.type_node(BaseSort::Prop, Op::Pred, &[c(0), c(1), c(2)]);
                        self.check(c(3), p)?;
                        self.type_node(self.arena().sort(c(0)), Op::TypeLift, &[c(0), c(1)])
                    }
                }
            }
            Op::Equal => {
                self.common_carrier(c(0), c(1))?;
                self.base_kind(BaseSort::Prop)
            }
            Op::Exists => {
                self.set_type(c(0))?;
                self.base_kind(BaseSort::Prop)
            }
            Op::IdRefl => {
                let ty = self.inferred(c(0))?;
                self.set_type(ty)?;
                self.type_node(BaseSort::Prop, Op::Equal, &[c(0), c(0)])
            }
            Op::ExistsIntro => {
                self.set_type(c(1))?;
                self.check(c(0), c(1))?;
                self.type_node(BaseSort::Prop, Op::Exists, &[c(1)])
            }
            Op::SubsetElim => {
                self.set_type(c(2))?;
                let lifted = self.type_node(self.arena().sort(c(2)), Op::TypeLift, &[c(2), c(1)]);
                self.check(c(0), lifted)?;
                self.type_node(BaseSort::Prop, Op::Pred, &[c(2), c(1), c(0)])
            }
            Op::IdElim { var } => {
                self.set_type(c(2))?;
                self.check(c(0), c(2))?;
                self.check(c(1), c(2))?;
                self.under(var, c(2), |ch| ch.proposition(c(3)))?;
                self.check(c(4), substitute(self.arena(), c(3), c(0))?)?;
                let eq = self.type_node(BaseSort::Prop, Op::Equal, &[c(0), c(1)]);
                self.check(c(5), eq)?;
                substitute(self.arena(), c(3), c(1))?
            }
            Op::RunStep
            | Op::Continue
            | Op::Finish
            | Op::Acc
            | Op::SetRun
            | Op::SetRunCase
            | Op::Run
            | Op::RunCase => self.infer_recursion(&d)?,
            Op::Recursor { rule, var } => {
                let i = self.set_type(c(0))?;
                if self.set_type(c(1))? != i {
                    return Err("RunStep types must share a level".into());
                }
                let step = self.type_node(BaseSort::Set(i), Op::RunStep, &[c(0), c(1)]);
                self.check(c(5), step)?;
                let sigma = self.under(var, step, |ch| ch.formation(c(2)))?;
                if rule != ProductRule::new(Sort::Base(BaseSort::Set(i)), sigma)? {
                    return Err("recursor rule mismatch".into());
                }
                for (domain, branch, op) in [(c(0), c(3), Op::Continue), (c(1), c(4), Op::Finish)] {
                    let state = shift(self.arena(), c(0), 1, 0)?;
                    let result = shift(self.arena(), c(1), 1, 0)?;
                    let bound =
                        self.make(BaseSort::Set(i), Stage::Term, Op::Bound { index: 0 }, &[]);
                    let ctor = self.make(
                        BaseSort::Set(i),
                        Stage::Term,
                        op,
                        &[(state, 0), (result, 0), (bound, 0)],
                    );
                    let motive = shift(self.arena(), c(2), 1, 1)?;
                    let ty = substitute(self.arena(), motive, ctor)?;
                    let expected = self.product(SymbolId::ANONYMOUS, domain, ty)?;
                    self.check(branch, expected)?;
                }
                substitute(self.arena(), c(2), c(5))?
            }
            Op::Thunk | Op::ReturnType => {
                let b = self.base_type(c(0))?;
                let target = match (d.op, b) {
                    (Op::Thunk, BaseSort::Computation(i)) => BaseSort::Value(i),
                    (Op::ReturnType, BaseSort::Value(i)) => BaseSort::Computation(i),
                    _ => return Err("F/U argument has wrong domain".into()),
                };
                self.base_kind(target)
            }
            Op::ThunkValue => {
                let ty = self.inferred(c(0))?;
                let i = self
                    .arena()
                    .sort(ty)
                    .level()
                    .ok_or("expected computation")?;
                self.type_node(BaseSort::Value(i), Op::Thunk, &[ty])
            }
            Op::Return => {
                let ty = self.inferred(c(0))?;
                let i = self.arena().sort(ty).level().ok_or("expected value")?;
                self.type_node(BaseSort::Computation(i), Op::ReturnType, &[ty])
            }
            Op::Force => {
                let ty = self.inferred(c(0))?;
                let ty = whnf(self.env, ty)?;
                let ty = self.arena().data(ty);
                if ty.op != Op::Thunk {
                    return Err("force requires U(B)".into());
                }
                ty.child(0)
            }
            Op::Sequence { var } | Op::ValueLet { var } => {
                let b = self.base_type(c(0))?;
                if !matches!(b, BaseSort::Value(_)) {
                    return Err("value binder requires value type".into());
                }
                let expected = if matches!(d.op, Op::Sequence { .. }) {
                    self.type_node(
                        BaseSort::Computation(b.level().unwrap()),
                        Op::ReturnType,
                        &[c(0)],
                    )
                } else {
                    c(0)
                };
                self.check(c(1), expected)?;
                let ty = self.under(var, c(0), |ch| ch.inferred(c(2)))?;
                if contains_bound(self.arena(), ty, 0) {
                    return Err("Program result type depends on value".into());
                }
                // An unused slot is removed by substitution; its argument is never inspected.
                substitute(self.arena(), ty, c(1))?
            }
            Op::BoxType => {
                self.closed_program_type(c(0))?;
                self.base_kind(self.arena().sort(c(0)).reflected())
            }
            Op::BoxProgram => {
                self.closed_program_type(c(0))?;
                if !closed_in_environment(self.env, c(1)) || !closed_in_environment(self.env, c(2))
                {
                    return Err("Box payload must be closed".into());
                }
                let mut closed = Checker::new(self.env, vec![]);
                closed.check(c(1), c(0))?;
                let reflected_ty = super::reflection::reflect(self.env, c(0))?;
                closed.check(c(2), reflected_ty)?;
                super::reflection::reflect_with_certificate(self.env, c(1), c(2).try_into()?)?;
                self.type_node(self.arena().sort(c(0)).reflected(), Op::BoxType, &[c(0)])
            }
            Op::ForceBox => {
                self.closed_program_type(c(0))?;
                let boxed =
                    self.type_node(self.arena().sort(c(0)).reflected(), Op::BoxType, &[c(0)]);
                self.check(c(1), boxed)?;
                super::reflection::reflect(self.env, c(0))?
            }
            Op::BoxApp { rule } | Op::BoxTypeApp { rule, .. } => {
                let type_application = matches!(d.op, Op::BoxTypeApp { .. });
                let var = match d.op {
                    Op::BoxTypeApp { var, .. } => var,
                    _ => SymbolId::ANONYMOUS,
                };
                self.formation(c(0))?;
                let body = if type_application {
                    c(1)
                } else {
                    shift(self.arena(), c(1), 1, 0)?
                };
                let p = self.product(var, c(0), body)?;
                let pd = self.arena().data(p);
                let r = match pd.op {
                    Op::ProdType { rule, .. } | Op::ProdTerm { rule, .. } => rule,
                    _ => unreachable!(),
                };
                if r != rule {
                    return Err("boxed application rule mismatch".into());
                }
                self.closed_program_type(p)?;
                let function_box =
                    self.type_node(self.arena().sort(p).reflected(), Op::BoxType, &[p]);
                self.check(c(2), function_box)?;
                let result = if type_application {
                    if !closed_in_environment(self.env, c(3)) {
                        return Err("boxed type argument must be closed".into());
                    }
                    self.check(c(3), c(0))?;
                    substitute(self.arena(), c(1), c(3))?
                } else {
                    self.closed_program_type(c(0))?;
                    let arg_box =
                        self.type_node(self.arena().sort(c(0)).reflected(), Op::BoxType, &[c(0)]);
                    self.check(c(3), arg_box)?;
                    c(1)
                };
                self.type_node(
                    self.arena().sort(result).reflected(),
                    Op::BoxType,
                    &[result],
                )
            }
            Op::IndType { .. }
            | Op::IndCtor { .. }
            | Op::IndElim { .. }
            | Op::Inductive { .. }
            | Op::InductiveConstructor { .. }
            | Op::Case { .. }
            | Op::SetCase { .. } => return self.infer_inductive(e, &d),
            Op::TakeSet
            | Op::TakeProp
            | Op::TakeEq
            | Op::SetExt
            | Op::FunExt
            | Op::ClassicalIndefiniteChoice
            | Op::AccIntro
            | Op::AccDescent => self.infer_proof(&d)?,
        };
        self.validate_inferred(e, inferred)?;
        Ok(Classifier::Expression(inferred))
    }

    fn validate_inferred(&mut self, e: Expression, ty: Expression) -> Result<(), String> {
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

    fn closed_program_type(&mut self, p: Expression) -> Result<(), String> {
        if !self.arena().sort(p).is_program() || !closed_in_environment(self.env, p) {
            return Err("Box requires a closed Program type".into());
        }
        Checker::new(self.env, vec![]).base_type(p)?;
        Ok(())
    }

    fn infer_recursion(&mut self, d: &Data) -> Result<Expression, String> {
        let c = |i| d.child(i);
        let b = self.base_type(c(0))?;
        if self.base_type(c(1))? != b || !matches!(b, BaseSort::Set(_) | BaseSort::Value(_)) {
            return Err("RunStep types must share the same Set/value level".into());
        }
        let runstep = self.type_node(b, Op::RunStep, &[c(0), c(1)]);
        match d.op {
            Op::RunStep => return Ok(self.base_kind(b)),
            Op::Continue => {
                self.check(c(2), c(0))?;
                return Ok(runstep);
            }
            Op::Finish => {
                self.check(c(2), c(1))?;
                return Ok(runstep);
            }
            _ => {}
        }
        let program = matches!(b, BaseSort::Value(_));
        let step_ty = if program {
            let ret = self.type_node(
                BaseSort::Computation(b.level().unwrap()),
                Op::ReturnType,
                &[runstep],
            );
            let arrow = self.arrow(c(0), ret)?;
            self.type_node(b, Op::Thunk, &[arrow])
        } else {
            self.arrow(c(0), runstep)?
        };
        self.check(c(2), step_ty)?;
        self.check(c(3), c(0))?;
        if d.op == Op::Acc {
            return Ok(self.base_kind(BaseSort::Prop));
        }
        if !program {
            let acc = self.type_node(BaseSort::Prop, Op::Acc, &[c(0), c(1), c(2), c(3)]);
            self.check(c(if d.op == Op::SetRun { 4 } else { 5 }), acc)?;
            if d.op == Op::SetRunCase {
                self.check(c(4), runstep)?;
                let applied = self.application(c(2), c(3))?;
                let eq = self.type_node(BaseSort::Prop, Op::Equal, &[applied, c(4)]);
                self.check(c(6), eq)?;
            }
            Ok(c(1))
        } else {
            if d.op == Op::RunCase {
                let transition = self.type_node(
                    BaseSort::Computation(b.level().unwrap()),
                    Op::ReturnType,
                    &[runstep],
                );
                self.check(c(4), transition)?;
            }
            Ok(self.type_node(
                BaseSort::Computation(b.level().unwrap()),
                Op::ReturnType,
                &[c(1)],
            ))
        }
    }

    fn quantified(
        &mut self,
        domain: Expression,
        body: impl FnOnce(&mut Self, Expression) -> Result<Expression, String>,
    ) -> Result<Expression, String> {
        let sigma = self.formation(domain)?;
        let stage = if sigma.is_upper() {
            Stage::Type
        } else {
            Stage::Term
        };
        let var = self.make(sigma.base(), stage, Op::Bound { index: 0 }, &[]);
        let result = self.under(SymbolId::ANONYMOUS, domain, |ch| body(ch, var))?;
        self.product(SymbolId::ANONYMOUS, domain, result)
    }

    fn lifted(&self, e: Expression, n: usize) -> Result<Expression, String> {
        shift(self.arena(), e, n, 0)
    }

    fn equality(&self, left: Expression, right: Expression) -> Expression {
        self.type_node(BaseSort::Prop, Op::Equal, &[left, right])
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
        let ctor = self.make(
            self.arena().sort(state),
            Stage::Term,
            Op::Continue,
            &[(state, 0), (result, 0), (to, 0)],
        );
        Ok(self.equality(applied, ctor))
    }

    fn infer_proof(&mut self, d: &Data) -> Result<Expression, String> {
        let c = |i| d.child(i);
        match d.op {
            Op::TakeSet | Op::TakeProp => {
                self.set_type(c(0))?;
                if d.op == Op::TakeSet {
                    if self.set_type(c(1))? != self.set_type(c(0))? {
                        return Err("TakeSet domain/codomain level mismatch".into());
                    }
                } else {
                    self.proposition(c(1))?
                }
                let map_ty = self.arrow(c(0), c(1))?;
                self.check(c(2), map_ty)?;
                let exists = self.type_node(BaseSort::Prop, Op::Exists, &[c(0)]);
                self.check(c(3), exists)?;
                if d.op == Op::TakeSet {
                    let unique = self.quantified(c(0), |ch, x| {
                        let dom = ch.lifted(c(0), 1)?;
                        ch.quantified(dom, |ch, y| {
                            let f = ch.lifted(c(2), 2)?;
                            let x = ch.lifted(x, 1)?;
                            let l = ch.application(f, x)?;
                            let r = ch.application(f, y)?;
                            Ok(ch.equality(l, r))
                        })
                    })?;
                    self.check(c(4), unique)?;
                }
                Ok(c(1))
            }
            Op::TakeEq => {
                let take = self.make(
                    self.arena().sort(c(2)),
                    Stage::Term,
                    Op::TakeSet,
                    &[(c(1), 0), (c(2), 0), (c(0), 0), (c(4), 0), (c(5), 0)],
                );
                self.check(take, c(2))?;
                self.check(c(3), c(1))?;
                let mapped = self.application(c(0), c(3))?;
                Ok(self.equality(take, mapped))
            }
            Op::FunExt => {
                let ty = self.inferred(c(0))?;
                self.set_type(ty)?;
                let p = self.expose_product(ty)?;
                let dom = self.arena().data(p).child(0);
                self.check(c(1), ty)?;
                let pointwise = self.quantified(dom, |ch, x| {
                    let l = ch.lifted(c(0), 1)?;
                    let r = ch.lifted(c(1), 1)?;
                    let l = ch.application(l, x)?;
                    let r = ch.application(r, x)?;
                    Ok(ch.equality(l, r))
                })?;
                self.check(c(2), pointwise)?;
                Ok(self.equality(c(0), c(1)))
            }
            Op::SetExt => {
                let ty = self.inferred(c(0))?;
                let head = whnf(self.env, ty)?;
                let power = self.arena().data(head);
                if power.op != Op::PowerSet {
                    return Err("setext requires powerset elements".into());
                }
                let carrier = power.child(0);
                self.set_type(carrier)?;
                self.check(c(1), ty)?;
                for (source, target, proof) in [(c(0), c(1), c(2)), (c(1), c(0), c(3))] {
                    let direction = self.quantified(carrier, |ch, x| {
                        let carrier = ch.lifted(carrier, 1)?;
                        let source = ch.lifted(source, 1)?;
                        let target = ch.lifted(target, 1)?;
                        let p = ch.type_node(BaseSort::Prop, Op::Pred, &[carrier, source, x]);
                        let q = ch.type_node(BaseSort::Prop, Op::Pred, &[carrier, target, x]);
                        ch.arrow(p, q)
                    })?;
                    self.check(proof, direction)?;
                }
                Ok(self.equality(c(0), c(1)))
            }
            Op::ClassicalIndefiniteChoice => {
                self.set_type(c(0))?;
                let ty = self.inferred(c(1))?;
                let p = self.expose_product(ty)?;
                let p = self.arena().data(p);
                if !convertible(self.env, p.child(0), c(0))? {
                    return Err("choice family domain mismatch".into());
                }
                let tail = whnf(self.env, p.child(1))?;
                let tail = self.arena().data(tail);
                if tail.op != Op::Base || !matches!(tail.sort, BaseSort::Set(_)) {
                    return Err("choice family must return Set".into());
                }
                let exists = self.quantified(c(0), |ch, x| {
                    let f = ch.lifted(c(1), 1)?;
                    let at = ch.application(f, x)?;
                    Ok(ch.type_node(BaseSort::Prop, Op::Exists, &[at]))
                })?;
                self.check(c(2), exists)?;
                let choices = self.quantified(c(0), |ch, x| {
                    let f = ch.lifted(c(1), 1)?;
                    ch.application(f, x)
                })?;
                Ok(self.type_node(BaseSort::Prop, Op::Exists, &[choices]))
            }
            Op::AccIntro | Op::AccDescent => {
                let acc = self.type_node(BaseSort::Prop, Op::Acc, &[c(0), c(1), c(2), c(3)]);
                self.proposition(acc)?;
                if d.op == Op::AccIntro {
                    let predecessors = self.quantified(c(0), |ch, x| {
                        let a = ch.lifted(c(0), 1)?;
                        let b = ch.lifted(c(1), 1)?;
                        let f = ch.lifted(c(2), 1)?;
                        let from = ch.lifted(c(3), 1)?;
                        let tr = ch.transition(a, b, f, from, x)?;
                        let acc = ch.type_node(BaseSort::Prop, Op::Acc, &[a, b, f, x]);
                        ch.arrow(tr, acc)
                    })?;
                    self.check(c(4), predecessors)?;
                    Ok(acc)
                } else {
                    self.check(c(4), c(0))?;
                    self.check(c(5), acc)?;
                    let transition = self.transition(c(0), c(1), c(2), c(3), c(4))?;
                    self.check(c(6), transition)?;
                    Ok(self.type_node(BaseSort::Prop, Op::Acc, &[c(0), c(1), c(2), c(4)]))
                }
            }
            _ => Err("not a proof constructor".into()),
        }
    }

    fn check_arguments(&mut self, args: &[Expression], telescope: &Context) -> Result<(), String> {
        if args.len() != telescope.len() {
            return Err("parameter count mismatch".into());
        }
        for (i, (arg, binder)) in args.iter().zip(telescope).enumerate() {
            let ty = instantiate_telescope(self.arena(), binder.classifier, &args[..i])?;
            self.check(*arg, ty)?;
        }
        Ok(())
    }

    fn infer_inductive(&mut self, e: Expression, d: &Data) -> Result<Classifier, String> {
        let c = |i| d.child(i);
        let ty = match d.op.clone() {
            Op::IndType { inductive } | Op::IndCtor { inductive, .. } => {
                let spec = self
                    .env
                    .inductive(inductive)
                    .ok_or("unknown inductive")?
                    .clone();
                let parameters = d.children(0);
                self.check_arguments(&parameters, &spec.parameters)?;
                let classifier = match d.op {
                    Op::IndCtor { constructor, .. } => *spec
                        .constructors
                        .get(constructor)
                        .ok_or("invalid constructor")?,
                    _ => spec.arity,
                };
                // Kind-level inductive names have an upper-sort classifier rather than an arity expression.
                if matches!(d.op, Op::IndType { .. }) && e.family().stage() == Stage::Kind {
                    if spec.sort != Sort::Upper(d.sort) {
                        return Err("inductive kind index mismatch".into());
                    }
                    return Ok(Classifier::Upper(d.sort));
                }
                instantiate_telescope(self.arena(), classifier, &parameters)?
            }
            Op::Inductive { inductive } | Op::InductiveConstructor { inductive, .. } => {
                let spec = self
                    .env
                    .datatype(inductive)
                    .ok_or("unknown Program datatype")?
                    .clone();
                let parameters = d.children(0);
                self.check_arguments(&parameters, &spec.parameters)?;
                if let Op::InductiveConstructor { constructor, .. } = d.op {
                    let fields = spec
                        .constructors
                        .get(constructor)
                        .ok_or("invalid constructor")?;
                    let args = d.children(1);
                    if fields.len() != args.len() {
                        return Err("constructor field count mismatch".into());
                    }
                    for (&arg, (_, ty)) in args.iter().zip(fields) {
                        self.check(
                            arg,
                            instantiate_telescope(self.arena(), (*ty).into(), &parameters)?,
                        )?
                    }
                    let data = Data {
                        sort: BaseSort::Value(spec.level),
                        op: Op::Inductive { inductive },
                        fields: vec![d.fields[0].clone()],
                    };
                    self.arena().store(Family::ValueType, data)
                } else {
                    self.base_kind(BaseSort::Value(spec.level))
                }
            }
            Op::Case {
                inductive,
                ref binders,
            }
            | Op::SetCase {
                inductive,
                ref binders,
            } => {
                let spec = self
                    .env
                    .datatype(inductive)
                    .ok_or("unknown datatype")?
                    .clone();
                self.base_type(c(0))?;
                let scrutinee_ty = self.inferred(c(1))?;
                let head = whnf(self.env, scrutinee_ty)?;
                let head = self.arena().data(head);
                let parameters = match (&d.op, &head.op) {
                    (Op::Case { .. }, Op::Inductive { inductive: id }) if *id == inductive => {
                        head.children(0)
                    }
                    (Op::SetCase { .. }, Op::IndType { inductive: id })
                        if *id == spec.reflected =>
                    {
                        head.children(0)
                    }
                    _ => return Err("case scrutinee datatype mismatch".into()),
                };
                if binders.len() != spec.constructors.len() || d.fields[2].len() != binders.len() {
                    return Err("case branch count mismatch".into());
                }
                for (i, fields) in spec.constructors.iter().enumerate() {
                    if fields.len() != binders[i].len() {
                        return Err("case branch binder count mismatch".into());
                    }
                    let mut branch = Checker::new(self.env, self.context.clone());
                    for (j, (_, field)) in fields.iter().enumerate() {
                        let field = if matches!(d.op, Op::SetCase { .. }) {
                            super::reflection::reflect(self.env, (*field).into())?
                        } else {
                            (*field).into()
                        };
                        let ty = instantiate_telescope(self.arena(), field, &parameters)?;
                        let ty = shift(self.arena(), ty, j, 0)?;
                        branch.context.push(Binding {
                            var: binders[i][j],
                            classifier: ty,
                        });
                    }
                    let ty = shift(self.arena(), c(0), fields.len(), 0)?;
                    branch.check(d.fields[2][i].expression, ty)?;
                }
                c(0)
            }
            Op::IndElim {
                inductive,
                ref motive_vars,
            } => {
                let spec = self
                    .env
                    .inductive(inductive)
                    .ok_or("unknown inductive")?
                    .clone();
                let scrutinee_ty = self.inferred(c(0))?;
                let mut head = whnf(self.env, scrutinee_ty)?;
                while self.arena().data(head).op == Op::TypeLift {
                    head = whnf(self.env, self.arena().data(head).child(0))?;
                }
                let (head, args) = self.decompose_app(head);
                let hd = self.arena().data(head);
                if !matches!(hd.op,Op::IndType{inductive:i} if i==inductive) {
                    return Err("eliminator scrutinee datatype mismatch".into());
                }
                let params = hd.children(0);
                let cases = d.children(3);
                if cases.len() != spec.constructors.len() {
                    return Err("eliminator case count mismatch".into());
                }
                let motive = Motive {
                    domains: d.children(1),
                    body: c(2),
                };
                if motive.domains.len() != motive_vars.len()
                    || motive.domains.len() != args.len() + 1
                {
                    return Err("motive telescope length mismatch".into());
                }
                let mut local = Checker::new(self.env, self.context.clone());
                for (var, domain) in motive_vars.iter().zip(&motive.domains) {
                    local.formation(*domain)?;
                    local.context.push(Binding {
                        var: *var,
                        classifier: *domain,
                    });
                }
                let result_sort = local.formation(motive.body)?;
                let permitted = match (spec.sort, result_sort) {
                    (_, Sort::Base(BaseSort::Prop)) => true,
                    (Sort::Base(BaseSort::Set(i)), Sort::Base(BaseSort::Set(j))) => i <= j,
                    (Sort::Base(BaseSort::Set(_)), Sort::Upper(BaseSort::Prop)) => true,
                    (Sort::Upper(BaseSort::Prop), Sort::Upper(BaseSort::Prop)) => true,
                    _ => self.env.singleton_elimination(inductive),
                };
                if !permitted {
                    return Err("forbidden large elimination".into());
                }
                let mut applied_args = args;
                applied_args.push(c(0));
                let applied = self.apply_motive(&motive, &applied_args)?;
                for (i, case) in cases.into_iter().enumerate() {
                    let ctor_ty =
                        instantiate_telescope(self.arena(), spec.constructors[i], &params)?;
                    let sigma = self.formation(ctor_ty)?;
                    let ctor = self.arena().store(
                        Family::at(
                            sigma.base(),
                            if sigma.is_upper() {
                                Stage::Type
                            } else {
                                Stage::Term
                            },
                        ),
                        Data {
                            sort: sigma.base(),
                            op: Op::IndCtor {
                                inductive,
                                constructor: i,
                            },
                            fields: vec![
                                params
                                    .iter()
                                    .map(|&expression| Child {
                                        depth: 0,
                                        expression,
                                    })
                                    .collect(),
                            ],
                        },
                    );
                    let expected = self.case_type(inductive, ctor_ty, ctor, &motive)?;
                    self.check(case, expected)?;
                }
                applied
            }
            _ => unreachable!(),
        };
        self.validate_inferred(e, ty)?;
        Ok(Classifier::Expression(ty))
    }

    fn decompose_app(&self, mut e: Expression) -> (Expression, Vec<Expression>) {
        let mut args = vec![];
        loop {
            let d = self.arena().data(e);
            if matches!(d.op, Op::AppTerm { .. } | Op::AppType { .. }) {
                args.push(d.child(1));
                e = d.child(0)
            } else {
                args.reverse();
                return (e, args);
            }
        }
    }

    fn apply_motive(&mut self, motive: &Motive, args: &[Expression]) -> Result<Expression, String> {
        if args.len() != motive.domains.len() {
            return Err("motive argument count mismatch".into());
        }
        for (i, (&arg, &ty)) in args.iter().zip(&motive.domains).enumerate() {
            self.check(arg, instantiate_telescope(self.arena(), ty, &args[..i])?)?;
        }
        instantiate_telescope(self.arena(), motive.body, args)
    }

    fn lift_motive(&self, m: &Motive) -> Result<Motive, String> {
        Ok(Motive {
            domains: m
                .domains
                .iter()
                .enumerate()
                .map(|(i, &e)| shift(self.arena(), e, 1, i))
                .collect::<Result<_, _>>()?,
            body: shift(self.arena(), m.body, 1, m.domains.len())?,
        })
    }

    fn recursive_hypothesis(
        &mut self,
        ind: InductiveId,
        ty: Expression,
        x: Expression,
        motive: &Motive,
    ) -> Result<Option<Expression>, String> {
        let ty = whnf(self.env, ty)?;
        let d = self.arena().data(ty);
        if matches!(d.op, Op::ProdTerm { .. } | Op::ProdType { .. }) {
            let mut found = false;
            let result = self.quantified(d.child(0), |ch, arg| {
                let x = ch.lifted(x, 1)?;
                let x = ch.application(x, arg)?;
                let motive = ch.lift_motive(motive)?;
                match ch.recursive_hypothesis(ind, d.child(1), x, &motive)? {
                    Some(ih) => {
                        found = true;
                        Ok(ih)
                    }
                    None => Ok(ch.base_kind(BaseSort::Prop)),
                }
            })?;
            return Ok(found.then_some(result));
        }
        let (h, mut args) = self.decompose_app(ty);
        if !matches!(self.arena().data(h).op,Op::IndType{inductive} if inductive==ind) {
            return Ok(None);
        }
        args.push(x);
        self.apply_motive(motive, &args).map(Some)
    }

    fn case_type(
        &mut self,
        ind: InductiveId,
        ty: Expression,
        ctor: Expression,
        motive: &Motive,
    ) -> Result<Expression, String> {
        let ty = whnf(self.env, ty)?;
        let d = self.arena().data(ty);
        if matches!(d.op, Op::ProdTerm { .. } | Op::ProdType { .. }) {
            let domain = d.child(0);
            return self.quantified(domain, |ch, x| {
                let ctor = ch.lifted(ctor, 1)?;
                let ctor = ch.application(ctor, x)?;
                let motive = ch.lift_motive(motive)?;
                let tail = ch.case_type(ind, d.child(1), ctor, &motive)?;
                let dom = ch.lifted(domain, 1)?;
                if let Some(ih) = ch.recursive_hypothesis(ind, dom, x, &motive)? {
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
