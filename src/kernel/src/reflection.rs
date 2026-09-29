//! Structural reflection shared by checked terms and frontend name resolution.
use crate::{
    calculus::shift,
    ids::{DefinitionId, InductiveId, ProgramInductiveId, SymbolId},
    syntax::*,
};
use rustc_hash::FxHashSet;
use std::cell::RefCell;
pub trait Resolver {
    fn arena(&self) -> &Arena;
    fn replacement(&self, _term: Expression) -> Result<Option<Expression>, String> {
        Ok(None)
    }
    fn definition(&self, id: DefinitionId) -> Result<(DefinitionId, Vec<bool>), String>;
    fn datatype(&self, id: ProgramInductiveId) -> Result<InductiveId, String>;
}
pub struct Reflection<'a, R: Resolver> {
    resolver: &'a R,
    active: RefCell<FxHashSet<Expression>>,
}
impl<'a, R: Resolver> Reflection<'a, R> {
    pub fn new(resolver: &'a R) -> Self {
        Self {
            resolver,
            active: Default::default(),
        }
    }
    fn reflect_shallow(&self, term: Expression) -> Result<Option<Expression>, String> {
        let arena = self.resolver.arena();
        let reflect = |term| arena.alloc(Node::Reflect { term });
        let node = match arena.get(term) {
            Node::Meta { .. } | Node::Bound(_) | Node::Parameter(_) => return Ok(None),
            Node::Definition { id, arguments } => {
                let (id, flags) = self.resolver.definition(id)?;
                if arguments.len() != flags.len() {
                    return Err("definition parameter count mismatch".into());
                }
                Node::Definition {
                    id,
                    arguments: arguments
                        .into_iter()
                        .zip(flags)
                        .map(|(e, program)| if program { reflect(e) } else { e })
                        .collect(),
                }
            }
            Node::Sort(sort) => Node::Sort(sort.reflected()),
            Node::Product { var, domain, body } => Node::Product {
                var,
                domain: reflect(domain),
                body: reflect(body),
            },
            Node::Lambda {
                var, domain, body, ..
            } => Node::Lambda {
                mode: Mode::Pure,
                var,
                domain: reflect(domain),
                body: reflect(body),
            },
            Node::App {
                function, argument, ..
            } => Node::App {
                mode: Mode::Pure,
                function: reflect(function),
                argument: reflect(argument),
            },
            Node::Thunk { computation_ty } => return Ok(Some(reflect(computation_ty))),
            Node::ReturnType { value_ty } => return Ok(Some(reflect(value_ty))),
            Node::ThunkValue { computation } => return Ok(Some(reflect(computation))),
            Node::Return { value } | Node::Force { value } => return Ok(Some(reflect(value))),
            Node::ProgramRunStep {
                state_ty,
                result_ty,
            } => Node::RunStep {
                state_ty: reflect(state_ty),
                result_ty: reflect(result_ty),
            },
            Node::ProgramContinue {
                state_ty,
                result_ty,
                next,
            } => Node::Continue {
                state_ty: reflect(state_ty),
                result_ty: reflect(result_ty),
                next: reflect(next),
            },
            Node::ProgramFinish {
                state_ty,
                result_ty,
                output,
            } => Node::Finish {
                state_ty: reflect(state_ty),
                result_ty: reflect(result_ty),
                output: reflect(output),
            },
            Node::Sequence {
                var,
                value_ty,
                computation,
                body,
            } => {
                let function = arena.alloc(Node::Lambda {
                    mode: Mode::Pure,
                    var,
                    domain: reflect(value_ty),
                    body: reflect(body),
                });
                Node::App {
                    mode: Mode::Pure,
                    function,
                    argument: reflect(computation),
                }
            }
            Node::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => {
                let function = arena.alloc(Node::Lambda {
                    mode: Mode::Pure,
                    var,
                    domain: reflect(value_ty),
                    body: reflect(body),
                });
                Node::App {
                    mode: Mode::Pure,
                    function,
                    argument: reflect(value),
                }
            }
            Node::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => Node::SetRun {
                state_ty: reflect(state_ty),
                result_ty: reflect(result_ty),
                step: reflect(step),
                initial: reflect(initial),
                accessibility,
            },
            Node::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => Node::SetRunCase {
                state_ty: reflect(state_ty),
                result_ty: reflect(result_ty),
                step: reflect(step),
                initial: reflect(initial),
                transition: reflect(transition),
                accessibility,
                transition_equality,
            },
            Node::Inductive {
                inductive,
                parameters,
            } => {
                let reflected = self.resolver.datatype(inductive)?;
                Node::IndType {
                    inductive: reflected,
                    parameters: parameters.into_iter().map(reflect).collect(),
                }
            }
            Node::InductiveConstructor {
                inductive,
                constructor,
                parameters,
                fields,
            } => {
                let reflected = self.resolver.datatype(inductive)?;
                let mut e = arena.alloc(Node::IndCtor {
                    inductive: reflected,
                    constructor,
                    parameters: parameters.into_iter().map(reflect).collect(),
                });
                for field in fields {
                    e = arena.alloc(Node::App {
                        mode: Mode::Pure,
                        function: e,
                        argument: reflect(field),
                    });
                }
                return Ok(Some(e));
            }
            Node::ProgramCase {
                inductive,
                binders,
                scrutinee,
                branches,
            } => Node::SetCase {
                inductive,
                binders,
                scrutinee: reflect(scrutinee),
                branches: branches.into_iter().map(reflect).collect(),
            },
            Node::ProgramStepRec {
                state_ty,
                result_ty,
                computation_ty,
                on_continue,
                on_finish,
                scrutinee,
            } => {
                let domain = arena.alloc(Node::ProgramRunStep {
                    state_ty,
                    result_ty,
                });
                let motive = arena.alloc(Node::Lambda {
                    mode: Mode::Pure,
                    var: SymbolId::ANONYMOUS,
                    domain: reflect(domain),
                    body: shift(arena, reflect(computation_ty), 1, 0)?,
                });
                Node::Recursor {
                    state_ty: reflect(state_ty),
                    result_ty: reflect(result_ty),
                    motive,
                    on_continue: reflect(on_continue),
                    on_finish: reflect(on_finish),
                    scrutinee: reflect(scrutinee),
                }
            }
            node => {
                return Err(format!(
                    "reflection requires a Program expression: {node:?}"
                ));
            }
        };
        Ok(Some(arena.alloc(node)))
    }
    /// Reflect an expression together with its complete Program context.
    pub fn reflect_bound(&self, term: Expression) -> Result<Expression, String> {
        self.reflect_under(term, usize::MAX)
    }
    pub(crate) fn reflect_step(&self, term: Expression) -> Result<Option<Expression>, String> {
        let mut pending = vec![term];
        let mut seen = rustc_hash::FxHashSet::default();
        while let Some(e) = pending.pop() {
            if !seen.insert(e) {
                continue;
            }
            if matches!(self.resolver.arena().get(e), Node::Meta { .. }) {
                return Ok(None);
            }
            pending.extend(
                self.resolver
                    .arena()
                    .children(e)
                    .into_iter()
                    .map(|(child, _)| child),
            );
        }
        if matches!(self.resolver.arena().get(term), Node::Bound(_)) {
            return Ok(None);
        }
        self.reflect_under(term, 0).map(Some)
    }
    fn reflect_under(&self, term: Expression, depth: usize) -> Result<Expression, String> {
        if let Some(replacement) = self.resolver.replacement(term)? {
            if !self.active.borrow_mut().insert(term) {
                return Err("cyclic definition during reflection".into());
            }
            let result = self.reflect_under(replacement, depth);
            self.active.borrow_mut().remove(&term);
            return result;
        }
        if let Node::Bound(index) = self.resolver.arena().get(term) {
            return Ok(if index < depth {
                term
            } else {
                self.resolver.arena().alloc(Node::Reflect { term })
            });
        }
        let Some(e) = self.reflect_shallow(term)? else {
            return Ok(self.resolver.arena().alloc(Node::Reflect { term }));
        };
        self.resolve_reflections(e, depth)
    }
    pub fn resolve_reflections(&self, e: Expression, depth: usize) -> Result<Expression, String> {
        if let Node::Reflect { term } = self.resolver.arena().get(e) {
            return self.reflect_under(term, depth);
        }
        self.resolver.arena().map_children(e, |child, bound| {
            self.resolve_reflections(child, depth.saturating_add(bound))
        })
    }
}
