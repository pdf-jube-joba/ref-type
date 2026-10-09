//! Source-facing diagnostics for kernel judgements.
#[cfg(test)]
use crate::raw::ids::SymbolId;
use crate::raw::{environment::CrateEnv, exp::*, sort::Sort};
use kernel::sharing::ContextId;
pub type JudgementError = crate::error::Error;

pub struct CheckSession<'env, 'context> {
    env: &'env CrateEnv,
    context: &'context mut ExpContext,
    context_id: ContextId,
}
impl<'env, 'context> CheckSession<'env, 'context> {
    pub fn new(env: &'env CrateEnv, context: &'context mut ExpContext) -> Self {
        Self {
            env,
            context_id: env.context_id(context),
            context,
        }
    }
    pub fn env(&self) -> &'env CrateEnv {
        self.env
    }
    pub fn arena(&self) -> &'env Arena {
        self.env.arena()
    }
    pub fn context(&self) -> &ExpContext {
        self.context
    }
    #[cfg(test)]
    pub fn push_pts(&mut self, var: SymbolId, ty: Exp) {
        self.context.push(ExpContextEntry { var, ty });
        self.context_id = self.env.contexts.borrow_mut().push(self.context_id, ty);
    }
    #[cfg(test)]
    pub fn pop(&mut self) {
        self.context.pop().expect("context underflow");
        self.context_id = self.env.contexts.borrow().parent(self.context_id);
    }
    pub fn check_pts(&mut self, term: Exp, ty: Exp) -> Result<(), Box<JudgementError>> {
        self.check_pts_resolved(term, ty).map(|_| ())
    }
    pub(crate) fn check_pts_resolved(
        &mut self,
        term: Exp,
        ty: Exp,
    ) -> Result<(Exp, Exp), Box<JudgementError>> {
        crate::kernel_bridge::logical(
            self.env,
            self.context,
            &[term, ty],
            |env, context, terms| {
                kernel::check::Checker::new(
                    env,
                    &mut kernel::metavariables::MetaContext::new(),
                    context,
                )
                .check(terms[0], terms[1])?;
                Ok((Exp(terms[0]), Exp(terms[1])))
            },
        )
        .map_err(Box::new)
    }
    pub fn infer_pts(&mut self, term: Exp) -> Result<Exp, Box<JudgementError>> {
        let key = (term, self.context_id);
        if let Some(&ty) = self.env.inference_cache.borrow().get(&key) {
            return Ok(ty);
        }
        let ty = crate::kernel_bridge::logical(
            self.env,
            self.context,
            &[term],
            |env, context, terms| {
                kernel::check::Checker::new(
                    env,
                    &mut kernel::metavariables::MetaContext::new(),
                    context,
                )
                .infer(terms[0])
            },
        )
        .map(Exp)
        .map_err(Box::new)?;
        self.env.inference_cache.borrow_mut().insert(key, ty);
        Ok(ty)
    }
    pub fn infer_exp_judgement(&mut self, term: Exp) -> Result<ExpJudgement, Box<JudgementError>> {
        Ok(ExpJudgement {
            term,
            ty: self.infer_pts(term)?,
        })
    }
    pub fn infer_sort(&mut self, term: Exp) -> Result<Sort, Box<JudgementError>> {
        crate::kernel_bridge::logical(self.env, self.context, &[term], |env, context, terms| {
            let ty = kernel::check::Checker::new(
                env,
                &mut kernel::metavariables::MetaContext::new(),
                context,
            )
            .infer(terms[0])?;
            match env.arena().get(env.whnf(ty)?) {
                kernel::syntax::Node::Sort(sort) => Ok(sort),
                _ => Err(kernel::error::Error::ExpectedASort),
            }
        })
        .and_then(|sort| match sort {
            kernel::sort::Sort::Base(kernel::sort::BaseSort::Set(i)) => Ok(Sort::Set(i)),
            kernel::sort::Sort::Upper(kernel::sort::BaseSort::Set(i)) => Ok(Sort::SetKind(i)),
            kernel::sort::Sort::Base(kernel::sort::BaseSort::Prop) => Ok(Sort::Prop),
            kernel::sort::Sort::Upper(kernel::sort::BaseSort::Prop) => Ok(Sort::PropKind),
            _ => Err(crate::error::Error::Invalid(
                crate::error::Invalid::ExpectedASetPropSort,
            )),
        })
        .map_err(Box::new)
    }
    pub fn check_wellformed_context(&mut self) -> Result<(), Box<JudgementError>> {
        crate::kernel_bridge::logical(self.env, self.context, &[], |env, context, _| {
            kernel::check::Checker::new(
                env,
                &mut kernel::metavariables::MetaContext::new(),
                context,
            )
            .check_context()
        })
        .map_err(Box::new)
    }
}
