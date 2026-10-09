//! Termination certificates expressed with products, step matching, and equality.
use crate::{
    calculus::shift,
    ids::SymbolId,
    sort::{BaseSort, Sort},
    syntax::{Arena, Expression, Mode, Node},
};

type Result<T> = std::result::Result<T, crate::error::Error>;

// A term remembers its binding depth so nested builders can lift captured terms.
#[derive(Clone, Copy)]
struct Term(Expression, usize);
struct Builder<'a> {
    arena: &'a Arena,
    depth: usize,
}
impl Builder<'_> {
    fn term(&self, node: Node) -> Term {
        Term(self.arena.alloc(node), self.depth)
    }
    fn at(&self, term: Term) -> Result<Expression> {
        shift(self.arena, term.0, self.depth - term.1, 0)
    }
    fn prop(&self) -> Term {
        self.term(Node::Sort(Sort::Base(BaseSort::Prop)))
    }
    fn bind(
        &self,
        domain: Term,
        lambda: bool,
        body: impl FnOnce(&Self, Term) -> Result<Term>,
    ) -> Result<Term> {
        let inner = Self {
            arena: self.arena,
            depth: self.depth + 1,
        };
        let body = inner.at(body(&inner, Term(self.arena.bound(0), inner.depth))?)?;
        let domain = self.at(domain)?;
        Ok(self.term(if lambda {
            Node::Lambda {
                mode: Mode::Pure,
                var: SymbolId::ANONYMOUS,
                domain,
                body,
            }
        } else {
            Node::Product {
                var: SymbolId::ANONYMOUS,
                domain,
                body,
            }
        }))
    }
    fn pi(&self, domain: Term, body: impl FnOnce(&Self, Term) -> Result<Term>) -> Result<Term> {
        self.bind(domain, false, body)
    }
    fn lam(&self, domain: Term, body: impl FnOnce(&Self, Term) -> Result<Term>) -> Result<Term> {
        self.bind(domain, true, body)
    }
    fn arrow(&self, domain: Term, body: Term) -> Result<Term> {
        self.pi(domain, |_, _| Ok(body))
    }
    fn app(&self, function: Term, argument: Term) -> Result<Term> {
        Ok(self.term(Node::App {
            mode: Mode::Pure,
            function: self.at(function)?,
            argument: self.at(argument)?,
        }))
    }
    fn truth(&self) -> Result<Term> {
        self.pi(self.prop(), |b, p| b.arrow(p, p))
    }
    fn step_ty(&self, a: Term, r: Term) -> Result<Term> {
        Ok(self.term(Node::RunStep {
            state_ty: self.at(a)?,
            result_ty: self.at(r)?,
        }))
    }
    fn ready(&self, a: Term, r: Term, p: Term, value: Term) -> Result<Term> {
        let motive = self.lam(self.step_ty(a, r)?, |b, _| Ok(b.prop()))?;
        let on_continue = self.lam(a, |b, x| b.app(p, x))?;
        let on_finish = self.lam(r, |b, _| b.truth())?;
        let matcher = self.term(Node::SetStepMatch {
            state_ty: self.at(a)?,
            result_ty: self.at(r)?,
            motive: self.at(motive)?,
            on_continue: self.at(on_continue)?,
            on_finish: self.at(on_finish)?,
        });
        self.app(matcher, value)
    }
    fn next(&self, a: Term, r: Term, f: Term, p: Term, x: Term) -> Result<Term> {
        self.ready(a, r, p, self.app(f, x)?)
    }
    fn closed(&self, a: Term, r: Term, f: Term, p: Term) -> Result<Term> {
        self.pi(a, |b, x| b.arrow(b.next(a, r, f, p, x)?, b.app(p, x)?))
    }
    fn termination(&self, a: Term, r: Term, f: Term, x: Term) -> Result<Term> {
        self.pi(self.arrow(a, self.prop())?, |b, p| {
            b.arrow(b.closed(a, r, f, p)?, b.app(p, x)?)
        })
    }
    // Lift a pointwise implication through a single RunStep.
    fn map_ready(
        &self,
        a: Term,
        r: Term,
        p: Term,
        q: Term,
        map: Term,
        value: Term,
    ) -> Result<Term> {
        let motive = self.lam(self.step_ty(a, r)?, |b, t| {
            b.arrow(b.ready(a, r, p, t)?, b.ready(a, r, q, t)?)
        })?;
        let on_finish = self.lam(r, |b, _| b.lam(b.truth()?, |_, proof| Ok(proof)))?;
        let matcher = self.term(Node::SetStepMatch {
            state_ty: self.at(a)?,
            result_ty: self.at(r)?,
            motive: self.at(motive)?,
            on_continue: self.at(map)?,
            on_finish: self.at(on_finish)?,
        });
        self.app(matcher, value)
    }
}

pub fn termination(
    arena: &Arena,
    state_ty: Expression,
    result_ty: Expression,
    step: Expression,
    state: Expression,
) -> Result<Expression> {
    let b = Builder { arena, depth: 0 };
    Ok(b.termination(
        Term(state_ty, 0),
        Term(result_ty, 0),
        Term(step, 0),
        Term(state, 0),
    )?
    .0)
}

/// Given termination at `from` and `step from = continue to`, derive termination at `to`.
/// The result contains only ordinary logical terms, including in open contexts.
pub fn descent(
    arena: &Arena,
    state_ty: Expression,
    result_ty: Expression,
    step: Expression,
    from: Expression,
    to: Expression,
    proof: Expression,
    edge: Expression,
) -> Result<Expression> {
    let b = Builder { arena, depth: 0 };
    let (a, r, f, from, to, proof, edge) = (
        Term(state_ty, 0),
        Term(result_ty, 0),
        Term(step, 0),
        Term(from, 0),
        Term(to, 0),
        Term(proof, 0),
        Term(edge, 0),
    );
    Ok(b.lam(b.arrow(a, b.prop())?, |b, p| {
        b.lam(b.closed(a, r, f, p)?, |b, h| {
            let q = b.lam(a, |b, x| b.next(a, r, f, p, x))?;
            let closed_q = b.lam(a, |b, x| b.map_ready(a, r, q, p, h, b.app(f, x)?))?;
            let base = b.app(b.app(proof, q)?, closed_q)?;
            let predicate = b.lam(b.step_ty(a, r)?, |b, t| b.ready(a, r, p, t))?;
            // IdElim stores the predicate body under its own binder.
            let Node::Lambda {
                body: predicate, ..
            } = arena.get(b.at(predicate)?)
            else {
                unreachable!()
            };
            let right = b.term(Node::Continue {
                state_ty: b.at(a)?,
                result_ty: b.at(r)?,
                next: b.at(to)?,
            });
            Ok(b.term(Node::IdElim {
                var: SymbolId::ANONYMOUS,
                left: b.at(b.app(f, from)?)?,
                right: b.at(right)?,
                ty: b.at(b.step_ty(a, r)?)?,
                predicate,
                base: b.at(base)?,
                equality: b.at(edge)?,
            }))
        })
    })?
    .0)
}
