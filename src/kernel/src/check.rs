//! Formation and typing for the shared PTS syntax.
use crate::{
    calculus::*,
    environment::Environment,
    ids::{InductiveId, ProgramInductiveId, SymbolId},
    metavariables::{Error, MetaContext},
    sort::{BaseSort, Sort},
    syntax::*,
};

pub struct Checker<'a> {
    env: &'a Environment,
    pub metas: &'a mut MetaContext,
    context: Context,
    // The interned telescope and meta presence are extended once per binder.
    context_states: Vec<(crate::sharing::ContextId, bool)>,
    pub(crate) solving: bool,
}
impl<'a> Checker<'a> {
    pub fn new(env: &'a Environment, metas: &'a mut MetaContext, context: Context) -> Self {
        Self {
            env,
            metas,
            context,
            context_states: Vec::new(),
            solving: false,
        }
    }
    pub fn context(&self) -> &Context {
        &self.context
    }
    fn context_state(&mut self) -> (crate::sharing::ContextId, bool) {
        let (mut id, mut has_metas) = self.context_states.last().copied().unwrap_or_default();
        // Closed terms need no context key. Intern only prefixes used by an open term.
        for binding in &self.context[self.context_states.len()..] {
            id = self.env.contexts.borrow_mut().push(id, binding.ty);
            has_metas |= self.arena().contains_meta(binding.ty);
            self.context_states.push((id, has_metas));
        }
        (id, has_metas)
    }
    fn push_binding(&mut self, binding: Binding) {
        self.context.push(binding);
    }
    fn truncate_context(&mut self, length: usize) {
        self.context.truncate(length);
        self.context_states.truncate(length);
    }
    fn arena(&self) -> &Arena {
        &self.env.arena
    }
    fn head(&self, e: Expression) -> Result<Expression, Error> {
        Ok(self.env.erased_head(self.metas.zonk(self.arena(), e)?)?)
    }
    fn base(&self, sort: BaseSort) -> Expression {
        self.arena().sort(Sort::Base(sort))
    }
    fn alloc(&self, node: Node) -> Expression {
        self.arena().alloc(node)
    }
    fn under<T>(
        &mut self,
        var: SymbolId,
        ty: Expression,
        f: impl FnOnce(&mut Self) -> Result<T, Error>,
    ) -> Result<T, Error> {
        self.push_binding(Binding { var, ty });
        let result = f(self);
        self.truncate_context(self.context.len() - 1);
        result
    }
    pub fn check_context(&mut self) -> Result<(), Error> {
        if !self.solving {
            self.metas
                .require_solved(self.arena(), self.context.iter().map(|b| b.ty))?;
        }
        let context = std::mem::take(&mut self.context);
        let states = std::mem::take(&mut self.context_states);
        let result = (|| {
            for binding in &context {
                self.formation(binding.ty)?;
                self.push_binding(binding.clone());
            }
            Ok(())
        })();
        self.context = context;
        self.context_states = states;
        result
    }
    #[tracing::instrument(target = "ref_type::typing", level = "debug", name = "kernel_infer", skip_all, fields(?term))]
    pub fn infer(&mut self, term: Expression) -> Result<Expression, Error> {
        self.metas.require_solved(
            self.arena(),
            std::iter::once(term).chain(self.context.iter().map(|b| b.ty)),
        )?;
        self.check_context()?;
        let ty = self.infer_open(term)?;
        self.metas.require_solved(self.arena(), [ty])?;
        self.metas.zonk(self.arena(), ty)
    }
    #[tracing::instrument(target = "ref_type::typing", level = "debug", name = "kernel_check", skip_all, fields(?term, ?expected))]
    pub fn check(&mut self, term: Expression, expected: Expression) -> Result<(), Error> {
        self.metas.require_solved(
            self.arena(),
            [term, expected]
                .into_iter()
                .chain(self.context.iter().map(|b| b.ty)),
        )?;
        self.check_context()?;
        self.check_open(term, expected)
    }
    pub(crate) fn validate(&mut self, term: Expression) -> Result<(), Error> {
        self.metas.require_solved(
            self.arena(),
            std::iter::once(term).chain(self.context.iter().map(|b| b.ty)),
        )?;
        self.check_context()?;
        if matches!(
            self.arena().get(self.head(term)?),
            Node::Sort(Sort::Upper(_))
        ) {
            return Ok(());
        }
        self.infer_open(term).map(|_| ())
    }
    pub fn motive_type(&mut self, motive: Expression) -> Result<Expression, Error> {
        self.check_context()?;
        self.metas.require_solved(
            self.arena(),
            std::iter::once(motive).chain(self.context.iter().map(|b| b.ty)),
        )?;
        let mark = self.context.len();
        let mut binders = vec![];
        let mut body = motive;
        let result = (|| {
            while let Node::Lambda {
                mode: Mode::Pure,
                var,
                domain,
                body: next,
            } = self.arena().get(body)
            {
                self.formation(domain)?;
                self.push_binding(Binding { var, ty: domain });
                binders.push((var, domain));
                body = next;
            }
            let mut ty = self.infer_open(body)?;
            for (var, domain) in binders.into_iter().rev() {
                ty = self.alloc(Node::Product {
                    var,
                    domain,
                    body: ty,
                });
            }
            Ok(ty)
        })();
        self.truncate_context(mark);
        result
    }
    pub(crate) fn formation(&mut self, e: Expression) -> Result<Sort, Error> {
        let ty = self.infer_open(e)?;
        match self.arena().get(self.head(ty)?) {
            Node::Sort(sort) => Ok(sort),
            _ => Err("expected a sort".into()),
        }
    }
    fn type_sort(&mut self, e: Expression) -> Result<BaseSort, Error> {
        match self.formation(e)? {
            Sort::Base(sort) => Ok(sort),
            _ => Err("expected a type of base kind".into()),
        }
    }
    fn set_type(&mut self, e: Expression) -> Result<usize, Error> {
        match self.type_sort(e)? {
            BaseSort::Set(level) => Ok(level),
            _ => Err("expected Set(i)".into()),
        }
    }
    fn proposition(&mut self, e: Expression) -> Result<(), Error> {
        if self.type_sort(e)? == BaseSort::Prop {
            Ok(())
        } else {
            Err("expected proposition".into())
        }
    }
    fn program_type(&mut self, e: Expression, computation: bool) -> Result<usize, Error> {
        let sort = self.type_sort(e)?;
        match (sort, computation) {
            (BaseSort::Computation(i), true) | (BaseSort::Value(i), false) => {
                self.type_dependencies(e)?;
                Ok(i)
            }
            _ => Err("incorrect Program type sort".into()),
        }
    }
    fn type_dependencies(&mut self, e: Expression) -> Result<(), Error> {
        let e = self.metas.zonk(self.arena(), e)?;
        fn indices(
            arena: &Arena,
            e: Expression,
            depth: usize,
            out: &mut std::collections::HashSet<usize>,
        ) {
            if let Node::Bound(i) = *arena.read(e)
                && i >= depth
            {
                out.insert(i - depth);
            }
            for (child, binders) in arena.children(e) {
                indices(arena, child, depth + binders, out);
            }
        }
        let mut pending = vec![e];
        let mut seen = std::collections::HashSet::new();
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            if let Node::Parameter(id) = self.arena().get(term) {
                let ty = self.env.parameter(id).ok_or("unknown module parameter")?;
                if !matches!(
                    self.formation(ty)?,
                    Sort::Upper(BaseSort::Value(_) | BaseSort::Computation(_))
                ) {
                    return Err("Program type depends on a value parameter".into());
                }
            }
            pending.extend(self.arena().children(term).into_iter().map(|(e, _)| e));
        }
        let mut used = std::collections::HashSet::new();
        indices(self.arena(), e, 0, &mut used);
        for index in used {
            let position = self
                .context
                .len()
                .checked_sub(index + 1)
                .ok_or("bound variable outside context")?;
            let binding = self.context[position].clone();
            let mut prefix = Checker::new(self.env, self.metas, self.context[..position].to_vec());
            if !matches!(
                prefix.formation(binding.ty)?,
                Sort::Upper(BaseSort::Value(_) | BaseSort::Computation(_))
            ) {
                return Err("Program type depends on a value variable".into());
            }
        }
        Ok(())
    }
    fn equal(&self, left: Expression, right: Expression) -> Result<bool, Error> {
        let left = self.metas.zonk(self.arena(), left)?;
        let right = self.metas.zonk(self.arena(), right)?;
        Ok(crate::reduction::erased_convertible(self.env, left, right)?)
    }
    fn weaken(&self, left: Expression, right: Expression) -> Result<bool, Error> {
        if self.equal(left, right)? {
            return Ok(true);
        }
        match (
            self.arena().get(self.head(left)?),
            self.arena().get(self.head(right)?),
        ) {
            (Node::TypeLift { superset, .. }, _) => self.weaken(superset, right),
            (
                Node::Product {
                    domain: a, body: b, ..
                },
                Node::Product {
                    domain: c, body: d, ..
                },
            ) if self.equal(a, c)? => self.weaken(b, d),
            _ => Ok(false),
        }
    }
    pub(crate) fn check_open(
        &mut self,
        term: Expression,
        expected: Expression,
    ) -> Result<(), Error> {
        if self.solving {
            if let Node::ChoiceEq { set, .. } = self.arena().get(term)
                && matches!(self.arena().get(self.head(set)?), Node::Meta { .. })
                && let Node::Equal { right, .. } = self.arena().get(self.head(expected)?)
                && let Node::Choice {
                    set: chosen_set, ..
                } = self.arena().get(self.head(right)?)
            {
                self.metas.unify(self.env, &self.context, set, chosen_set)?;
            }
            if let Node::Meta { id, arguments } = self.arena().get(term) {
                self.metas.expect(self.env, id, &arguments, expected)?;
            }
            if let Node::Lambda {
                mode,
                var,
                domain,
                body,
            } = self.arena().get(term)
                && let Node::Product {
                    domain: input,
                    body: output,
                    ..
                } = self.arena().get(self.head(expected)?)
            {
                self.metas.unify(self.env, &self.context, domain, input)?;
                self.under(var, input, |ch| ch.check_open(body, output))?;
                self.metas
                    .constrain(crate::metavariables::Constraint::Validate {
                        context: self.context.clone(),
                        term,
                        expected: Some(expected),
                    });
                let _ = mode;
                return Ok(());
            }
        }
        let inferred = self.infer_open(term)?;
        if !self.solving
            && !matches!(
                self.arena().get(self.head(expected)?),
                Node::Sort(Sort::Upper(_))
            )
        {
            self.formation(expected)?;
        }
        let metas = self.metas.unresolved(self.arena(), [inferred, expected])?;
        if metas.is_empty() && self.weaken(inferred, expected)? {
            return Ok(());
        }
        if !metas.is_empty() {
            if self.solving {
                self.metas
                    .unify(self.env, &self.context, inferred, expected)?;
                return Ok(());
            }
            return Err(Error::Unresolved {
                metas,
                constraints: 0,
            });
        }
        if std::env::var_os("REF_TYPE_DEBUG_CONVERSION").is_some()
            && let Ok(Some((path, left, right))) = crate::reduction::first_difference(
                self.env,
                self.metas.zonk(self.arena(), inferred)?,
                self.metas.zonk(self.arena(), expected)?,
            )
        {
            eprintln!(
                "conversion difference {path:?}: {:?} != {:?}",
                self.arena().get(left),
                self.arena().get(right)
            );
            fn show(a: &Arena, e: Expression, depth: usize, remaining: &mut usize) {
                if depth > 9 || *remaining == 0 {
                    return;
                }
                *remaining -= 1;
                eprintln!("{} {e:?}: {:?}", " ".repeat(depth), a.get(e));
                for (child, _) in a.children(e) {
                    show(a, child, depth + 1, remaining);
                }
            }
            show(self.arena(), left, 0, &mut 50);
            show(self.arena(), right, 0, &mut 50);
        }
        Err(Error::TypeMismatch(Box::new(
            crate::metavariables::TypeMismatch {
                arena: self.env.arena.clone(),
                context: self.context.clone(),
                term,
                inferred,
                expected,
                frames: Vec::new(),
            },
        )))
    }
    fn arrow(&self, domain: Expression, codomain: Expression) -> Result<Expression, Error> {
        Ok(self.alloc(Node::Product {
            var: SymbolId::ANONYMOUS,
            domain,
            body: shift(self.arena(), codomain, 1, 0)?,
        }))
    }
    fn arguments(&mut self, arguments: &[Expression], context: &Context) -> Result<(), Error> {
        if arguments.len() != context.len() {
            return Err("parameter count mismatch".into());
        }
        for (i, binding) in context.iter().enumerate() {
            self.check_open(
                arguments[i],
                self.env.instantiate(binding.ty, &arguments[..i])?,
            )?;
        }
        Ok(())
    }
    fn product(&self, ty: Expression) -> Result<(Expression, Expression), Error> {
        match self.arena().get(self.head(ty)?) {
            Node::Product { domain, body, .. } => Ok((domain, body)),
            Node::TypeLift { superset, .. } => self.product(superset),
            _ => Err("expected a product".into()),
        }
    }
    fn runstep(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
        program: bool,
    ) -> Result<Expression, Error> {
        if self.solving
            && !self
                .metas
                .unresolved(self.arena(), [state_ty, result_ty])?
                .is_empty()
        {
            return Ok(self.alloc(if program {
                Node::ProgramRunStep {
                    state_ty,
                    result_ty,
                }
            } else {
                Node::RunStep {
                    state_ty,
                    result_ty,
                }
            }));
        }
        let state = self.type_sort(state_ty)?;
        let result = self.type_sort(result_ty)?;
        if state != result
            || !matches!(
                (state, program),
                (BaseSort::Set(_), false) | (BaseSort::Value(_), true)
            )
        {
            return Err("recursion types must inhabit the same Set(i) or value universe".into());
        }
        Ok(self.alloc(if program {
            Node::ProgramRunStep {
                state_ty,
                result_ty,
            }
        } else {
            Node::RunStep {
                state_ty,
                result_ty,
            }
        }))
    }
    fn carrier(&mut self, term: Expression) -> Result<Expression, Error> {
        let mut ty = self.infer_open(term)?;
        loop {
            ty = self.head(ty)?;
            match self.arena().get(ty) {
                Node::TypeLift { superset, .. } => ty = superset,
                _ => {
                    if !self.solving {
                        self.set_type(ty)?;
                    }
                    return Ok(ty);
                }
            }
        }
    }
    pub(crate) fn infer_open(&mut self, term: Expression) -> Result<Expression, Error> {
        // These rules depend on one binding at most, not on the whole telescope.
        if matches!(
            *self.arena().read(term),
            Node::Bound(_) | Node::Sort(_) | Node::Parameter(_)
        ) {
            return self.infer_framed(term);
        }
        let closed = self.arena().max_loose_bound(term).is_none();
        let complete = !self.arena().contains_meta(term) && (closed || !self.context_state().1);
        if !complete {
            if self.solving {
                return self.infer_framed(term);
            }
            let context = self.context_state().0;
            if let Some(&ty) = self.metas.inferred.get(&(context, term)) {
                return Ok(ty);
            }
            let result = self.infer_framed(term);
            if let Ok(ty) = result {
                self.metas.inferred.insert((context, term), ty);
            }
            return result;
        }
        let context = if closed {
            crate::sharing::ContextId::default()
        } else {
            self.context_state().0
        };
        if let Some(&ty) = self.env.inferred.borrow().get(&(context, term)) {
            return Ok(ty);
        }
        let solving = std::mem::replace(&mut self.solving, false);
        let result = self.infer_framed(term);
        self.solving = solving;
        if let Ok(ty) = result {
            self.env.inferred.borrow_mut().insert((context, term), ty);
        }
        result
    }
    fn infer_framed(&mut self, term: Expression) -> Result<Expression, Error> {
        self.infer_rule(term).map_err(|error| {
            let node = format!("{:?}", self.arena().get(term));
            let name = node.split([' ', '(']).next().unwrap_or("expression");
            error.at(format!("rule: {name:?}"))
        })
    }
    fn check_at(
        &mut self,
        phase: &str,
        term: Expression,
        expected: Expression,
    ) -> Result<(), Error> {
        self.check_open(term, expected)
            .map_err(|error| error.at(phase))
    }
    fn infer_rule(&mut self, term: Expression) -> Result<Expression, Error> {
        let result = match self.arena().get(term) {
            Node::Ascribe { term, ty } => {
                self.check_open(term, ty)?;
                ty
            }
            Node::Parameter(id) => self.env.parameter(id).ok_or("unknown module parameter")?,
            Node::Sort(Sort::Base(sort)) => self.arena().sort(Sort::Upper(sort)),
            Node::Sort(Sort::Upper(_)) => return Err("upper sort has no classifier".into()),
            Node::Bound(index) => {
                let offset = index
                    .checked_add(1)
                    .ok_or("bound variable outside context")?;
                let position = self
                    .context
                    .len()
                    .checked_sub(offset)
                    .ok_or("bound variable outside context")?;
                self.env.shifted(self.context[position].ty, offset)?
            }
            Node::Definition { id, arguments } => {
                let definition = self.env.definition(id)?;
                self.arguments(&arguments, &definition.context)?;
                self.env.instantiate(definition.ty, &arguments)?
            }
            Node::Meta { id, arguments } => {
                let entry = self.metas.entry(id)?;
                let context = entry.context.clone();
                let expected = entry.expected;
                let assignment = entry.assignment;
                self.arguments(&arguments, &context)?;
                let expected = match expected {
                    Some(ty) => ty,
                    None if self.solving && assignment.is_some() => {
                        let mut checker = Checker::new(self.env, self.metas, context.clone());
                        checker.solving = true;
                        let ty = checker.infer_open(assignment.unwrap())?;
                        self.metas.expect(
                            self.env,
                            id,
                            &arguments,
                            self.env.instantiate(ty, &arguments)?,
                        )?;
                        ty
                    }
                    None if self.solving => self.metas.ensure_type(&self.env.arena, id)?,
                    None => {
                        let value = assignment.ok_or(Error::Unresolved {
                            metas: vec![id],
                            constraints: 0,
                        })?;
                        let ty = Checker::new(self.env, self.metas, context).infer(value)?;
                        return Ok(self.env.instantiate(ty, &arguments)?);
                    }
                };
                if !self.solving
                    && let Some(value) = assignment
                {
                    Checker::new(self.env, self.metas, context).check(value, expected)?;
                }
                self.env.instantiate(expected, &arguments)?
            }
            Node::Product { var, domain, body } => {
                let a = self.formation(domain)?;
                let b = self.under(var, domain, |c| c.formation(body))?;
                let result = a.product(b).ok_or("no product rule for these sorts")?;
                if result.base().is_program() {
                    self.type_dependencies(term)?;
                }
                self.arena().sort(result)
            }
            Node::Lambda {
                mode,
                var,
                domain,
                body,
            } => {
                if !self.solving {
                    self.formation(domain)?;
                }
                let ty = self.under(var, domain, |c| c.infer_open(body))?;
                let product = self.alloc(Node::Product {
                    var,
                    domain,
                    body: ty,
                });
                if !self.solving {
                    let sort = self.formation(product)?;
                    if (mode == Mode::Computation)
                        != matches!(sort, Sort::Base(BaseSort::Computation(_)))
                    {
                        return Err("lambda evaluation mode mismatch".into());
                    }
                }
                product
            }
            Node::App {
                mode,
                function,
                argument,
            } => {
                let ty = self.infer_open(function)?;
                let (domain, body) = match self.product(ty) {
                    Ok(product) => product,
                    Err(_)
                        if self.solving
                            && !self.metas.unresolved(self.arena(), [ty])?.is_empty() =>
                    {
                        // Refine a type hole in its declaration context. The
                        // application context can contain a function whose type
                        // is this very hole, making fresh children cyclic.
                        let (mut context, arguments, target) =
                            match self.arena().get(self.head(ty)?) {
                                Node::Meta { id, arguments } => {
                                    let context = self.metas.entry(id)?.context.clone();
                                    let target = self.alloc(Node::Meta {
                                        id,
                                        arguments: (0..context.len())
                                            .rev()
                                            .map(|i| self.arena().bound(i))
                                            .collect(),
                                    });
                                    (context, arguments, target)
                                }
                                _ => (
                                    self.context.clone(),
                                    (0..self.context.len())
                                        .rev()
                                        .map(|i| self.arena().bound(i))
                                        .collect(),
                                    ty,
                                ),
                            };
                        let declaration = context.clone();
                        let domain = self.metas.fresh(&self.env.arena, context.clone(), None);
                        context.push(Binding {
                            var: SymbolId::ANONYMOUS,
                            ty: domain,
                        });
                        let body = self.metas.fresh(&self.env.arena, context, None);
                        let product = self.alloc(Node::Product {
                            var: SymbolId::ANONYMOUS,
                            domain,
                            body,
                        });
                        // Solve the declaration before instantiating it: an
                        // occurrence such as ?T[x, x] is not a pattern spine.
                        self.metas.unify(self.env, &declaration, target, product)?;
                        let product = self.env.instantiate(product, &arguments)?;
                        self.product(product)?
                    }
                    Err(error) => return Err(error),
                };
                self.check_at("check argument type for application", argument, domain)?;
                if !self.solving {
                    // Inference has already established that `ty` is a product.
                    // Every product rule with a logical domain has a logical result;
                    // checking its domain avoids rechecking the entire dependent tail
                    // after each argument in a long application spine.
                    let domain_sort = self.formation(domain)?;
                    let computation = domain_sort.base().is_program()
                        && matches!(self.formation(ty)?, Sort::Base(BaseSort::Computation(_)));
                    if (mode == Mode::Computation) != computation {
                        return Err("application evaluation mode mismatch".into());
                    }
                }
                self.env.instantiate(body, &[argument])?
            }
            Node::Reflect { term } => {
                let ty = self.infer_open(term)?;
                let sort = match self.arena().get(self.head(ty)?) {
                    Node::Sort(Sort::Upper(sort)) => sort,
                    _ => self.formation(ty)?.base(),
                };
                if !sort.is_program() {
                    return Err(format!(
                        "reflection requires a Program expression: {:?} : {:?} ({sort:?})",
                        self.arena().get(term),
                        self.arena().get(ty)
                    )
                    .into());
                }
                self.alloc(Node::Reflect { term: ty })
            }
            Node::PowerSet { set } => {
                let i = self.set_type(set)?;
                self.base(BaseSort::Set(i))
            }
            Node::Subset {
                var,
                set,
                predicate,
            } => {
                self.set_type(set)?;
                self.under(var, set, |c| c.proposition(predicate))
                    .map_err(|e| e.at("check predicate"))?;
                self.alloc(Node::PowerSet { set })
            }
            Node::TypeLift { superset, subset } => {
                let i = self.set_type(superset)?;
                self.check_open(subset, self.alloc(Node::PowerSet { set: superset }))?;
                self.base(BaseSort::Set(i))
            }
            Node::Pred {
                superset,
                subset,
                element,
            } => {
                self.set_type(superset)?;
                self.check_open(subset, self.alloc(Node::PowerSet { set: superset }))?;
                self.check_at("check element", element, superset)?;
                self.base(BaseSort::Prop)
            }
            Node::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => {
                let ty = self.alloc(Node::TypeLift { superset, subset });
                self.formation(ty)?;
                self.check_at("check element", element, superset)?;
                self.check_at(
                    "check membership proof",
                    proof,
                    self.alloc(Node::Pred {
                        superset,
                        subset,
                        element,
                    }),
                )?;
                ty
            }
            Node::SubsetElim {
                superset,
                subset,
                element,
            } => {
                let ty = self.alloc(Node::TypeLift { superset, subset });
                self.formation(ty)?;
                self.check_at("check subset elimination", element, ty)?;
                self.alloc(Node::Pred {
                    superset,
                    subset,
                    element,
                })
            }
            Node::Equal { left, right } => {
                let a = self.carrier(left)?;
                let b = self.carrier(right)?;
                if self.solving {
                    self.metas.unify(self.env, &self.context, a, b)?;
                } else if !self.equal(a, b)? {
                    return Err("different equality carriers".into());
                }
                self.base(BaseSort::Prop)
            }
            Node::IdRefl { element } => {
                self.carrier(element)?;
                self.alloc(Node::Equal {
                    left: element,
                    right: element,
                })
            }
            Node::Exists { set } => {
                self.set_type(set)?;
                self.base(BaseSort::Prop)
            }
            Node::ExistsIntro { element, set } => {
                self.set_type(set)?;
                self.check_at("check element", element, set)?;
                self.alloc(Node::Exists { set })
            }
            Node::IdElim {
                var,
                left,
                right,
                ty,
                predicate,
                base,
                equality,
            } => {
                if !self.solving {
                    self.set_type(ty)?;
                }
                self.check_open(left, ty)?;
                self.check_open(right, ty)?;
                self.under(var, ty, |c| c.proposition(predicate))?;
                self.check_at(
                    "check base",
                    base,
                    self.env.instantiate(predicate, &[left])?,
                )?;
                self.check_at(
                    "check equality proof",
                    equality,
                    self.alloc(Node::Equal { left, right }),
                )?;
                self.env.instantiate(predicate, &[right])?
            }
            Node::RunStep {
                state_ty,
                result_ty,
            } => {
                self.runstep(state_ty, result_ty, false)?;
                let i = self.set_type(state_ty)?;
                self.base(BaseSort::Set(i))
            }
            Node::ProgramRunStep {
                state_ty,
                result_ty,
            } => {
                self.runstep(state_ty, result_ty, true)?;
                let i = self.program_type(state_ty, false)?;
                self.base(BaseSort::Value(i))
            }
            Node::Continue {
                state_ty,
                result_ty,
                next,
            } => {
                if !self.solving {
                    self.runstep(state_ty, result_ty, false)?;
                }
                self.check_at("check next state", next, state_ty)?;
                self.runstep(state_ty, result_ty, false)?
            }
            Node::Finish {
                state_ty,
                result_ty,
                output,
            } => {
                if !self.solving {
                    self.runstep(state_ty, result_ty, false)?;
                }
                self.check_at("check output", output, result_ty)?;
                self.runstep(state_ty, result_ty, false)?
            }
            Node::ProgramContinue {
                state_ty,
                result_ty,
                next,
            } => {
                if !self.solving {
                    self.runstep(state_ty, result_ty, true)?;
                }
                self.check_at("check next state", next, state_ty)?;
                self.runstep(state_ty, result_ty, true)?
            }
            Node::ProgramFinish {
                state_ty,
                result_ty,
                output,
            } => {
                if !self.solving {
                    self.runstep(state_ty, result_ty, true)?;
                }
                self.check_at("check output", output, result_ty)?;
                self.runstep(state_ty, result_ty, true)?
            }
            Node::Thunk { computation_ty } => {
                let i = self.program_type(computation_ty, true)?;
                self.base(BaseSort::Value(i))
            }
            Node::ReturnType { value_ty } => {
                let i = self.program_type(value_ty, false)?;
                self.base(BaseSort::Computation(i))
            }
            Node::ThunkValue { computation } => {
                let computation_ty = self.infer_open(computation)?;
                if !self.solving {
                    self.program_type(computation_ty, true)?;
                }
                self.alloc(Node::Thunk { computation_ty })
            }
            Node::Return { value } => {
                let value_ty = self.infer_open(value)?;
                if !self.solving {
                    self.program_type(value_ty, false)?;
                }
                self.alloc(Node::ReturnType { value_ty })
            }
            Node::Force { value } => {
                let ty = self.infer_open(value)?;
                match self.arena().get(self.head(ty)?) {
                    Node::Thunk { computation_ty } => computation_ty,
                    _ => return Err("force requires U(B)".into()),
                }
            }
            Node::Sequence {
                var,
                value_ty,
                computation,
                body,
            } => {
                if !self.solving {
                    self.program_type(value_ty, false)?;
                }
                self.check_open(computation, self.alloc(Node::ReturnType { value_ty }))?;
                let ty = self.under(var, value_ty, |c| c.infer_open(body))?;
                if !self.solving {
                    self.under(var, value_ty, |c| c.program_type(ty, true))?;
                }
                self.env.instantiate(ty, &[computation])?
            }
            Node::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                if !self.solving {
                    self.program_type(value_ty, false)?;
                }
                self.check_open(value, value_ty)?;
                let ty = self.under(var, value_ty, |c| c.infer_open(body))?;
                if !self.solving {
                    self.under(var, value_ty, |c| c.program_type(ty, true))?;
                }
                self.env.instantiate(ty, &[value])?
            }
            Node::IndType {
                inductive,
                parameters,
            } => {
                let spec = self.env.inductive(inductive).ok_or("unknown inductive")?;
                self.arguments(&parameters, &spec.parameters)?;
                if spec.sort.is_upper() {
                    self.arena().sort(spec.sort)
                } else {
                    self.env.instantiate(spec.arity, &parameters)?
                }
            }
            Node::IndCtor {
                inductive,
                constructor,
                parameters,
            } => {
                let spec = self.env.inductive(inductive).ok_or("unknown inductive")?;
                self.arguments(&parameters, &spec.parameters)?;
                let ty = *spec
                    .constructors
                    .get(constructor)
                    .ok_or("unknown constructor")?;
                self.env.instantiate(ty, &parameters)?
            }
            Node::Inductive {
                inductive,
                parameters,
            } => {
                let spec = self.env.datatype(inductive).ok_or("unknown datatype")?;
                self.arguments(&parameters, &spec.parameters)?;
                self.base(BaseSort::Value(spec.level))
            }
            Node::InductiveConstructor {
                inductive,
                constructor,
                parameters,
                fields,
            } => {
                let spec = self.env.datatype(inductive).ok_or("unknown datatype")?;
                self.arguments(&parameters, &spec.parameters)?;
                let telescope = spec
                    .constructors
                    .get(constructor)
                    .ok_or("unknown constructor")?;
                if fields.len() != telescope.len() {
                    return Err("constructor field count mismatch".into());
                }
                for (field, binding) in fields.iter().zip(telescope) {
                    self.check_open(*field, self.env.instantiate(binding.ty, &parameters)?)?;
                }
                self.alloc(Node::Inductive {
                    inductive,
                    parameters,
                })
            }
            node => return self.infer_extended(node),
        };
        Ok(result)
    }

    fn infer_extended(&mut self, node: Node) -> Result<Expression, Error> {
        match node {
            Node::Choice {
                set,
                existence,
                uniqueness,
            } => self.infer_choice(set, existence, uniqueness),
            Node::TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => self.infer_take_prop(domain, proposition, map, existence),
            Node::ChoiceEq {
                set,
                element,
                existence,
                uniqueness,
            } => {
                let choice = self.alloc(Node::Choice {
                    set,
                    existence,
                    uniqueness,
                });
                self.check_open(choice, set)?;
                self.check_at("check element", element, set)?;
                self.equality(element, choice)
            }
            Node::FunExt {
                left,
                right,
                pointwise,
            } => {
                let ty = self.infer_open(left)?;
                self.set_type(ty)?;
                let (domain, _) = self.product(ty)?;
                self.check_open(right, ty)?;
                let expected = self.quantified(domain, |ch, x| {
                    ch.equality(
                        ch.application(ch.lifted(left, 1)?, x)?,
                        ch.application(ch.lifted(right, 1)?, x)?,
                    )
                })?;
                self.check_at("check pointwise equality", pointwise, expected)?;
                self.equality(left, right)
            }
            Node::SetExt {
                left,
                right,
                left_to_right,
                right_to_left,
            } => {
                let ty = self.infer_open(left)?;
                let Node::PowerSet { set } = self.arena().get(self.head(ty)?) else {
                    return Err("setext requires powerset elements".into());
                };
                self.set_type(set)?;
                self.check_open(right, ty)?;
                for (source, target, proof, phase) in [
                    (left, right, left_to_right, "check forward inclusion"),
                    (right, left, right_to_left, "check backward inclusion"),
                ] {
                    let expected = self.quantified(set, |ch, x| {
                        let set = ch.lifted(set, 1)?;
                        ch.arrow(
                            ch.predicate(set, ch.lifted(source, 1)?, x)?,
                            ch.predicate(set, ch.lifted(target, 1)?, x)?,
                        )
                    })?;
                    self.check_at(phase, proof, expected)?;
                }
                self.equality(left, right)
            }
            Node::ClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            } => {
                self.set_type(domain)?;
                let ty = self.infer_open(family)?;
                let (input, body) = self.product(ty)?;
                if !self.equal(input, domain)? {
                    return Err("choice family domain mismatch".into());
                }
                if !matches!(
                    self.arena().get(self.head(body)?),
                    Node::Sort(Sort::Base(BaseSort::Set(_)))
                ) {
                    return Err("choice family must return Set".into());
                }
                let exists = self.quantified(domain, |ch, x| {
                    ch.exists(ch.application(ch.lifted(family, 1)?, x)?)
                })?;
                self.check_at("check pointwise inhabitation", inhabited, exists)?;
                let choices =
                    self.quantified(domain, |ch, x| ch.application(ch.lifted(family, 1)?, x))?;
                self.exists(choices)
            }
            Node::SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => {
                self.check_run(state_ty, result_ty, step, initial, false)?;
                self.check_at(
                    "check accessibility proof",
                    accessibility,
                    self.accessibility(state_ty, result_ty, step, initial)?,
                )?;
                Ok(result_ty)
            }
            Node::SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => {
                let runstep = self.check_run(state_ty, result_ty, step, initial, false)?;
                self.check_at(
                    "check accessibility proof",
                    accessibility,
                    self.accessibility(state_ty, result_ty, step, initial)?,
                )?;
                self.check_at("check recursive transition", transition, runstep)?;
                self.check_at(
                    "check transition equality proof",
                    transition_equality,
                    self.equality(self.application(step, initial)?, transition)?,
                )?;
                Ok(result_ty)
            }
            Node::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => {
                self.check_run(state_ty, result_ty, step, initial, true)?;
                let proof = self.accessibility(
                    self.reflect(state_ty),
                    self.reflect(result_ty),
                    self.reflect(step),
                    self.reflect(initial),
                )?;
                self.check_at("check accessibility proof", accessibility, proof)?;
                Ok(self.alloc(Node::ReturnType {
                    value_ty: result_ty,
                }))
            }
            Node::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => {
                let runstep = self.check_run(state_ty, result_ty, step, initial, true)?;
                self.check_at(
                    "check recursive transition",
                    transition,
                    self.alloc(Node::ReturnType { value_ty: runstep }),
                )?;
                let proof = self.accessibility(
                    self.reflect(state_ty),
                    self.reflect(result_ty),
                    self.reflect(step),
                    self.reflect(initial),
                )?;
                self.check_at("check accessibility proof", accessibility, proof)?;
                self.check_at(
                    "check transition equality proof",
                    transition_equality,
                    self.equality(
                        self.application(self.reflect(step), self.reflect(initial))?,
                        self.reflect(transition),
                    )?,
                )?;
                Ok(self.alloc(Node::ReturnType {
                    value_ty: result_ty,
                }))
            }
            Node::SetStepMatch {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
            } => {
                let step = self.runstep(state_ty, result_ty, false)?;
                let motive_ty = self.motive_type(motive)?;
                let (domain, codomain) = self.product(motive_ty)?;
                if !self.equal(domain, step)? {
                    return Err("step match motive domain mismatch".into());
                }
                let Node::Sort(sigma) = self.arena().get(self.head(codomain)?) else {
                    return Err("step match motive must return a classifier".into());
                };
                let i = self.set_type(state_ty)?;
                Sort::Base(BaseSort::Set(i))
                    .product(sigma)
                    .ok_or("invalid step match motive sort")?;
                let state = self.lifted(state_ty, 1)?;
                let result = self.lifted(result_ty, 1)?;
                let x = self.arena().bound(0);
                let cont = self.alloc(Node::Continue {
                    state_ty: state,
                    result_ty: result,
                    next: x,
                });
                let finish = self.alloc(Node::Finish {
                    state_ty: state,
                    result_ty: result,
                    output: x,
                });
                for (domain, branch, ctor) in [
                    (state_ty, on_continue, cont),
                    (result_ty, on_finish, finish),
                ] {
                    let body = self.head(self.application(self.lifted(motive, 1)?, ctor)?)?;
                    self.check_open(
                        branch,
                        self.alloc(Node::Product {
                            var: SymbolId::ANONYMOUS,
                            domain,
                            body,
                        }),
                    )?;
                }
                let body =
                    self.head(self.application(self.lifted(motive, 1)?, self.arena().bound(0))?)?;
                Ok(self.alloc(Node::Product {
                    var: SymbolId::ANONYMOUS,
                    domain: step,
                    body,
                }))
            }
            Node::ProgramStepMatch {
                state_ty,
                result_ty,
                computation_ty,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                let runstep = self.runstep(state_ty, result_ty, true)?;
                self.check_open(scrutinee, runstep)?;
                self.program_type(computation_ty, true)?;
                for (domain, branch) in [(state_ty, on_continue), (result_ty, on_finish)] {
                    let codomain = self.lifted(computation_ty, 1)?;
                    let expected = self.alloc(Node::Product {
                        var: SymbolId::ANONYMOUS,
                        domain,
                        body: codomain,
                    });
                    self.check_at("check RunStep branch", branch, expected)?;
                }
                Ok(computation_ty)
            }
            Node::BoxType { program_ty } => {
                let i = self.closed_program_type(program_ty)?;
                Ok(self.base(BaseSort::Set(i)))
            }
            Node::BoxProgram {
                program_ty,
                program,
            } => {
                self.closed_program_type(program_ty)?;
                if max_loose_bound(self.arena(), program).is_some()
                    || self.env.contains_parameter(program)
                {
                    return Err("Box payload must be closed".into());
                }
                let mut closed = Checker::new(self.env, self.metas, vec![]);
                closed.check_open(program, program_ty)?;
                closed.check_open(closed.reflect(program), closed.reflect(program_ty))?;
                Ok(self.alloc(Node::BoxType { program_ty }))
            }
            Node::ForceBox { program_ty, boxed } => {
                self.closed_program_type(program_ty)?;
                self.check_open(boxed, self.alloc(Node::BoxType { program_ty }))?;
                Ok(self.reflect(program_ty))
            }
            Node::BoxApp { function, argument } => {
                let ty = self.infer_open(function)?;
                let Node::BoxType { program_ty } = self.arena().get(self.head(ty)?) else {
                    return Err("boxed application requires Box(A -> B)".into());
                };
                self.closed_program_type(program_ty)?;
                let (domain, body) = self.product(program_ty)?;
                self.program_type(domain, false)?;
                let input = self.alloc(Node::ReturnType { value_ty: domain });
                self.check_at(
                    "check argument type for application",
                    argument,
                    self.alloc(Node::BoxType { program_ty: input }),
                )?;
                let codomain = self.env.instantiate(body, &[argument])?;
                self.closed_program_type(codomain)?;
                Ok(self.alloc(Node::BoxType {
                    program_ty: codomain,
                }))
            }
            Node::BoxTypeApp { function, argument } => {
                let ty = self.infer_open(function)?;
                let Node::BoxType { program_ty } = self.arena().get(self.head(ty)?) else {
                    return Err("boxed type application requires a boxed type abstraction".into());
                };
                self.closed_program_type(program_ty)?;
                let (domain, codomain) = self.product(program_ty)?;
                if !matches!(
                    self.formation(domain)?,
                    Sort::Upper(BaseSort::Value(_) | BaseSort::Computation(_))
                ) {
                    return Err("Box type binder requires Program kind".into());
                }
                if max_loose_bound(self.arena(), argument).is_some() {
                    return Err("boxed type argument must be closed".into());
                }
                self.check_at("check argument type for application", argument, domain)?;
                let program_ty = self.env.instantiate(codomain, &[argument])?;
                Ok(self.alloc(Node::BoxType { program_ty }))
            }
            Node::IndElim {
                motive_bindings,
                inductive,
                scrutinee,
                motive,
                cases,
            } => self.inductive_elimination(
                inductive,
                scrutinee,
                Some(motive_bindings),
                motive,
                cases,
                true,
            ),
            Node::Case {
                inductive,
                scrutinee,
                motive,
                branches,
            } => self.inductive_elimination(inductive, scrutinee, None, motive, branches, false),
            Node::SetCase {
                inductive,
                binders,
                scrutinee,
                branches,
            } => self.check_case(inductive, binders, scrutinee, branches, true),
            Node::ProgramCase {
                inductive,
                binders,
                scrutinee,
                branches,
            } => self.check_case(inductive, binders, scrutinee, branches, false),
            _ => unreachable!("primitive handled by infer_open"),
        }
    }
    fn infer_choice(
        &mut self,
        set: Expression,
        existence: Expression,
        uniqueness: Expression,
    ) -> Result<Expression, Error> {
        self.set_type(set)?;
        self.check_at("check existence", existence, self.exists(set)?)?;
        let unique = self.quantified(set, |ch, x| {
            let set = ch.lifted(set, 1)?;
            ch.quantified(set, |ch, y| ch.equality(ch.lifted(x, 1)?, y))
        })?;
        self.check_at("check uniqueness", uniqueness, unique)?;
        Ok(set)
    }
    fn infer_take_prop(
        &mut self,
        domain: Expression,
        proposition: Expression,
        map: Expression,
        existence: Expression,
    ) -> Result<Expression, Error> {
        self.set_type(domain)?;
        self.proposition(proposition)?;
        let map_ty = self.arrow(domain, proposition)?;
        self.check_at("check map", map, map_ty)?;
        self.check_at("check existence", existence, self.exists(domain)?)?;
        Ok(proposition)
    }
    fn apply_motive(&mut self, motive: &Motive, args: &[Expression]) -> Result<Expression, Error> {
        if args.len() != motive.domains.len() {
            return Err("motive argument count mismatch".into());
        }
        for (i, (&arg, &ty)) in args.iter().zip(&motive.domains).enumerate() {
            self.check_open(arg, self.env.instantiate(ty, &args[..i])?)?;
        }
        self.env.instantiate(motive.body, args).map_err(Error::from)
    }
    fn lift_motive(&self, m: &Motive) -> Result<Motive, Error> {
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

    fn lifted(&self, e: Expression, n: usize) -> Result<Expression, Error> {
        Ok(shift(self.arena(), e, n, 0)?)
    }
    fn application(&self, function: Expression, argument: Expression) -> Result<Expression, Error> {
        Ok(self.alloc(Node::App {
            mode: Mode::Pure,
            function,
            argument,
        }))
    }
    fn equality(&self, left: Expression, right: Expression) -> Result<Expression, Error> {
        Ok(self.alloc(Node::Equal { left, right }))
    }
    fn exists(&self, set: Expression) -> Result<Expression, Error> {
        Ok(self.alloc(Node::Exists { set }))
    }
    fn predicate(
        &self,
        superset: Expression,
        subset: Expression,
        element: Expression,
    ) -> Result<Expression, Error> {
        Ok(self.alloc(Node::Pred {
            superset,
            subset,
            element,
        }))
    }
    fn accessibility(
        &self,
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        state: Expression,
    ) -> Result<Expression, Error> {
        crate::termination::termination(self.arena(), state_ty, result_ty, step, state)
            .map_err(Error::from)
    }
    fn quantified(
        &mut self,
        domain: Expression,
        body: impl FnOnce(&mut Self, Expression) -> Result<Expression, Error>,
    ) -> Result<Expression, Error> {
        self.formation(domain)?;
        let x = self.arena().bound(0);
        let body = self.under(SymbolId::ANONYMOUS, domain, |ch| body(ch, x))?;
        Ok(self.alloc(Node::Product {
            var: SymbolId::ANONYMOUS,
            domain,
            body,
        }))
    }
    fn closed_program_type(&mut self, ty: Expression) -> Result<usize, Error> {
        if max_loose_bound(self.arena(), ty).is_some() || self.env.contains_parameter(ty) {
            return Err("Box requires a closed computation type".into());
        }
        Checker::new(self.env, self.metas, vec![]).program_type(ty, true)
    }
    fn check_run(
        &mut self,
        state_ty: Expression,
        result_ty: Expression,
        step: Expression,
        initial: Expression,
        program: bool,
    ) -> Result<Expression, Error> {
        let runstep = self.runstep(state_ty, result_ty, program)?;
        let step_ty = if program {
            let result = self.alloc(Node::ReturnType { value_ty: runstep });
            let arrow = self.arrow(state_ty, result)?;
            self.alloc(Node::Thunk {
                computation_ty: arrow,
            })
        } else {
            self.arrow(state_ty, runstep)?
        };
        self.check_at("check step", step, step_ty)?;
        self.check_at("check initial state", initial, state_ty)?;
        Ok(runstep)
    }
    fn reflect(&self, term: Expression) -> Expression {
        self.alloc(Node::Reflect { term })
    }
    pub(crate) fn child_context(
        &mut self,
        parent: Expression,
        slot: usize,
    ) -> Result<Context, Error> {
        let mut context = self.context.clone();
        let binding = match self.arena().get(parent) {
            Node::Product { var, domain, .. } | Node::Lambda { var, domain, .. } => {
                Binding { var, ty: domain }
            }
            Node::Subset { var, set, .. } => Binding { var, ty: set },
            Node::IdElim { var, ty, .. } => Binding { var, ty },
            Node::Sequence { var, value_ty, .. } | Node::ValueLet { var, value_ty, .. } => {
                Binding { var, ty: value_ty }
            }
            Node::IndElim {
                motive_bindings, ..
            } => {
                // Child order: scrutinee, telescope domains, motive body, cases.
                let depth = slot
                    .checked_sub(1)
                    .filter(|&depth| depth <= motive_bindings.len())
                    .ok_or("invalid motive binder slot")?;
                context.extend(
                    motive_bindings
                        .into_iter()
                        .take(depth)
                        .map(|(var, ty)| Binding { var, ty }),
                );
                return Ok(context);
            }
            Node::ProgramCase {
                inductive,
                binders,
                scrutinee,
                ..
            }
            | Node::SetCase {
                inductive,
                binders,
                scrutinee,
                ..
            } => {
                let reflected = matches!(self.arena().get(parent), Node::SetCase { .. });
                let spec = self.env.datatype(inductive).ok_or("unknown datatype")?;
                let ty = self.infer_open(scrutinee)?;
                let parameters = match self.arena().get(self.head(ty)?) {
                    Node::Inductive { parameters, .. } | Node::IndType { parameters, .. } => {
                        parameters
                    }
                    _ => return Err("case scrutinee datatype mismatch".into()),
                };
                let index = slot.checked_sub(1).ok_or("invalid case branch slot")?;
                let fields = spec.constructors.get(index).ok_or("unknown case branch")?;
                let vars = binders.get(index).ok_or("missing case binders")?;
                if fields.len() != vars.len() {
                    return Err("case branch binder count mismatch".into());
                }
                for (j, (field, &var)) in fields.iter().zip(vars).enumerate() {
                    let ty = if reflected {
                        self.env.reflect_bound(field.ty)?
                    } else {
                        field.ty
                    };
                    let ty = self.env.instantiate(ty, &parameters)?;
                    context.push(Binding {
                        var,
                        ty: shift(self.arena(), ty, j, 0)?,
                    });
                }
                return Ok(context);
            }
            _ => return Err("unknown binder structure".into()),
        };
        context.push(binding);
        Ok(context)
    }
    fn check_case(
        &mut self,
        inductive: ProgramInductiveId,
        binders: Vec<Vec<SymbolId>>,
        scrutinee: Expression,
        branches: Vec<Expression>,
        reflected: bool,
    ) -> Result<Expression, Error> {
        let spec = self.env.datatype(inductive).ok_or("unknown datatype")?;
        let mut result_ty = None;
        let ty = self.infer_open(scrutinee)?;
        let parameters = match self.arena().get(self.head(ty)?) {
            Node::IndType {
                inductive: id,
                parameters,
            } if reflected && id == spec.reflected => parameters,
            Node::Inductive {
                inductive: id,
                parameters,
            } if !reflected && id == inductive => parameters,
            _ => return Err("case scrutinee datatype mismatch".into()),
        };
        if binders.len() != spec.constructors.len() || branches.len() != binders.len() {
            return Err("case branch count mismatch".into());
        }
        for (i, fields) in spec.constructors.iter().enumerate() {
            if fields.len() != binders[i].len() {
                return Err("case branch binder count mismatch".into());
            }
            let mut branch = Checker::new(self.env, self.metas, self.context.clone());
            branch.solving = self.solving;
            for (j, field) in fields.iter().enumerate() {
                let field = if reflected {
                    self.env.reflect_bound(field.ty)?
                } else {
                    field.ty
                };
                let ty = branch.env.instantiate(field, &parameters)?;
                branch.push_binding(Binding {
                    var: binders[i][j],
                    ty: branch.lifted(ty, j)?,
                });
            }
            match result_ty {
                Some(ty) => branch.check_open(branches[i], branch.lifted(ty, fields.len())?)?,
                None => {
                    let ty = branch.infer_open(branches[i])?;
                    let arguments = (0..self.context.len())
                        .rev()
                        .map(|j| branch.arena().bound(j + fields.len()))
                        .collect::<Vec<_>>();
                    result_ty = Some(
                        abstract_pattern(branch.arena(), ty, &arguments)?
                            .ok_or("case result type depends on fields")?,
                    );
                }
            }
        }
        let result_ty = result_ty.ok_or("empty case needs an expected type")?;
        if reflected {
            self.set_type(result_ty)?;
        } else {
            self.program_type(result_ty, true)?;
        }
        Ok(result_ty)
    }
    fn decompose_app(&self, mut e: Expression) -> (Expression, Vec<Expression>) {
        let mut args = vec![];
        while let Node::App {
            mode: Mode::Pure,
            function,
            argument,
        } = self.arena().get(e)
        {
            args.push(argument);
            e = function;
        }
        args.reverse();
        (e, args)
    }
    #[allow(clippy::too_many_arguments)]
    fn inductive_elimination(
        &mut self,
        inductive: InductiveId,
        scrutinee: Expression,
        motive_bindings: Option<Vec<(SymbolId, Expression)>>,
        motive_term: Expression,
        cases: Vec<Expression>,
        recursive: bool,
    ) -> Result<Expression, Error> {
        let mut motive_vars = vec![];
        let mut motive_domains = vec![];
        let mut motive_body = motive_term;
        if let Some(bindings) = motive_bindings {
            (motive_vars, motive_domains) = bindings.into_iter().unzip();
        } else {
            while let Node::Lambda {
                mode: Mode::Pure,
                var,
                domain,
                body,
            } = self.arena().get(motive_body)
            {
                motive_vars.push(var);
                motive_domains.push(domain);
                motive_body = body;
            }
            if motive_domains.is_empty() {
                let mut ty = self.infer_open(motive_term)?;
                while let Node::Product { var, domain, body } = self.arena().get(self.head(ty)?) {
                    motive_vars.push(var);
                    motive_domains.push(domain);
                    ty = body;
                }
                motive_body = shift(self.arena(), motive_term, motive_domains.len(), 0)?;
                for index in (0..motive_domains.len()).rev() {
                    motive_body = self.application(motive_body, self.arena().bound(index))?;
                }
            }
        }
        let spec = self.env.inductive(inductive).ok_or("unknown inductive")?;
        let ty = self.infer_open(scrutinee)?;
        let mut head = self.head(ty)?;
        while let Node::TypeLift { superset, .. } = self.arena().get(head) {
            head = self.head(superset)?;
        }
        let (head, mut args) = self.decompose_app(head);
        let Node::IndType {
            inductive: id,
            parameters,
        } = self.arena().get(head)
        else {
            return Err("eliminator scrutinee datatype mismatch".into());
        };
        if id != inductive {
            return Err("eliminator scrutinee datatype mismatch".into());
        }
        if cases.len() != spec.constructors.len() {
            return Err("eliminator case count mismatch".into());
        }
        let motive = Motive {
            domains: motive_domains,
            body: motive_body,
        };
        if motive.domains.len() != motive_vars.len() || motive.domains.len() != args.len() + 1 {
            return Err("motive telescope length mismatch".into());
        }
        let mut expected_domains = vec![];
        let mut arity = self.env.instantiate(spec.arity, &parameters)?;
        while let Node::Product { domain, body, .. } = self.arena().get(self.head(arity)?) {
            expected_domains.push(domain);
            arity = body;
        }
        let n = expected_domains.len();
        let mut instance = self.alloc(Node::IndType {
            inductive,
            parameters: parameters
                .iter()
                .map(|&e| shift(self.arena(), e, n, 0))
                .collect::<Result<_, _>>()?,
        });
        for i in (0..n).rev() {
            instance = self.application(instance, self.arena().bound(i))?;
        }
        expected_domains.push(instance);
        let mut local = Checker::new(self.env, self.metas, self.context.clone());
        local.solving = self.solving;
        for ((&var, &ty), &expected) in motive_vars
            .iter()
            .zip(&motive.domains)
            .zip(&expected_domains)
        {
            if local.solving {
                local.metas.unify(local.env, &local.context, ty, expected)?;
            } else if !local.equal(ty, expected)? {
                return Err("motive domain mismatch".into());
            }
            local.formation(expected)?;
            local.push_binding(Binding { var, ty: expected });
        }
        let result_sort = local.formation(motive.body)?;
        let permitted = match (spec.sort, result_sort) {
            (Sort::Base(BaseSort::Set(i)), Sort::Base(BaseSort::Set(j))) => i <= j,
            (_, Sort::Base(BaseSort::Prop))
            | (
                Sort::Base(BaseSort::Set(_)) | Sort::Upper(BaseSort::Prop),
                Sort::Upper(BaseSort::Prop),
            ) => true,
            _ => self.env.singleton_elimination(inductive)?,
        };
        if !permitted {
            return Err("forbidden large elimination".into());
        }
        args.push(scrutinee);
        let applied = self.apply_motive(&motive, &args)?;
        for (i, case) in cases.into_iter().enumerate() {
            let ctor_ty = self.env.instantiate(spec.constructors[i], &parameters)?;
            self.formation(ctor_ty)?;
            let ctor = self.alloc(Node::IndCtor {
                inductive,
                constructor: i,
                parameters: parameters.clone(),
            });
            let expected = self.case_type(
                inductive,
                spec.constructors[i],
                ctor_ty,
                ctor,
                &motive,
                recursive,
            )?;
            self.check_open(case, expected)?;
        }
        Ok(applied)
    }
    fn recursive_hypothesis(
        &mut self,
        ind: InductiveId,
        ty: Expression,
        x: Expression,
        motive: &Motive,
    ) -> Result<Option<Expression>, Error> {
        let ty = self.head(ty)?;
        if let Node::Product { domain, body, .. } = self.arena().get(ty) {
            let mut found = false;
            let result = self.quantified(domain, |ch, arg| {
                let x = ch.application(ch.lifted(x, 1)?, arg)?;
                let motive = ch.lift_motive(motive)?;
                match ch.recursive_hypothesis(ind, body, x, &motive)? {
                    Some(ih) => {
                        found = true;
                        Ok(ih)
                    }
                    None => Ok(ch.base(BaseSort::Prop)),
                }
            })?;
            return Ok(found.then_some(result));
        }
        let (head, mut args) = self.decompose_app(ty);
        if !matches!(self.arena().get(head),Node::IndType { inductive,.. } if inductive==ind) {
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
        recursive: bool,
    ) -> Result<Expression, Error> {
        let ty = self.head(ty)?;
        if let Node::Product { domain, body, .. } = self.arena().get(ty) {
            let Node::Product {
                domain: declared_domain,
                body: declared_body,
                ..
            } = self.arena().get(self.head(declared_ty)?)
            else {
                return Err("expected declared constructor product".into());
            };
            let recursive_field = recursive && self.env.recursive_field(ind, declared_domain)?;
            return self.quantified(domain, |ch, x| {
                let ctor = ch.application(ch.lifted(ctor, 1)?, x)?;
                let motive = ch.lift_motive(motive)?;
                let tail = ch.case_type(ind, declared_body, body, ctor, &motive, recursive)?;
                let domain = ch.lifted(domain, 1)?;
                if recursive_field
                    && let Some(ih) = ch.recursive_hypothesis(ind, domain, x, &motive)?
                {
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

#[cfg(test)]
mod context_tests {
    use super::*;

    #[test]
    fn inference_distinguishes_sibling_scopes_and_restores_context_after_errors() {
        let env = Environment::new();
        let mut metas = MetaContext::new();
        let set = env.arena.sort(Sort::Base(BaseSort::Set(0)));
        let prop = env.arena.sort(Sort::Base(BaseSort::Prop));
        let bound = env.arena.bound(0);
        let mut checker = Checker::new(
            &env,
            &mut metas,
            vec![Binding {
                var: SymbolId::ANONYMOUS,
                ty: set,
            }],
        );
        checker.check_context().unwrap();
        assert_eq!(checker.infer_open(bound).unwrap(), set);
        checker
            .under(SymbolId::ANONYMOUS, bound, |checker| {
                assert_eq!(checker.infer_open(bound)?, env.arena.bound(1));
                Ok(())
            })
            .unwrap();
        let result: Result<(), Error> = checker.under(SymbolId::ANONYMOUS, prop, |checker| {
            assert_eq!(checker.infer_open(bound)?, prop);
            Err("leave this scope".into())
        });
        assert!(result.is_err());
        assert_eq!(checker.context().len(), 1);
        assert_eq!(checker.infer_open(bound).unwrap(), set);
    }
}
