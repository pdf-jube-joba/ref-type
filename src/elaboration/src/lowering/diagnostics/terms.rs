//! Surface rendering for the common expression syntax.
use super::*;
impl Renderer<'_> {
    pub(super) fn term(&mut self, e: Expression) -> Term {
        use Node::*;
        let node = self.arena.get(e);
        match &node {
            Sort(sort) => {
                use kernel::sort::{BaseSort, Sort};
                let (kind, base) = match sort {
                    Sort::Base(b) => (false, b),
                    Sort::Upper(b) => (true, b),
                };
                Term::atom(match (kind, base) {
                    (false, BaseSort::Set(i)) => universe("Set", *i),
                    (true, BaseSort::Set(i)) => universe("SetKind", *i),
                    (false, BaseSort::Prop) => "\\Prop".into(),
                    (true, BaseSort::Prop) => "\\PropKind".into(),
                    (false, BaseSort::Value(i)) => universe("VType", *i),
                    (true, BaseSort::Value(i)) => universe("VKind", *i),
                    (false, BaseSort::Computation(i)) => universe("CType", *i),
                    (true, BaseSort::Computation(i)) => universe("CKind", *i),
                })
            }
            Parameter(id) => Term::atom(
                self.raw
                    .module_parameter_opt((*id).into())
                    .map(|parameter| self.raw.symbol(parameter.name).to_owned())
                    .unwrap_or_else(|| format!("parameter#{id:?}")),
            ),
            Bound(index) => self.bound(*index),
            Definition { id, arguments } => self.definition(*id, arguments),
            Meta { id, arguments } => self.call(&format!("?{id:?}"), arguments),
            Product { var, domain, body } => {
                let mut tail = *body;
                while let Node::Product { body, .. } = self.arena.get(tail) {
                    tail = body;
                }
                let program = matches!(self.arena.get(tail), Node::ReturnType { .. });
                self.binder(*var, *domain, *body, false, program)
            }
            Lambda {
                mode,
                var,
                domain,
                body,
            } => self.binder(*var, *domain, *body, true, *mode == Mode::Computation),
            App {
                function, argument, ..
            } => self.application(*function, *argument),
            Reflect { term } => {
                let term = self.expression(*term, 3);
                Term::new(format!("{term}^"), 3)
            }
            Subset {
                var,
                set,
                predicate,
            } => self.subset(*var, (*set).into(), (*predicate).into()),
            SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => self.call(
                "into",
                &[
                    (*superset).into(),
                    (*subset).into(),
                    (*element).into(),
                    (*proof).into(),
                ],
            ),
            Continue {
                state_ty,
                result_ty,
                next,
            } => self.call(
                "continue",
                &[(*state_ty).into(), (*result_ty).into(), (*next).into()],
            ),
            Finish {
                state_ty,
                result_ty,
                output,
            } => self.call(
                "finish",
                &[(*state_ty).into(), (*result_ty).into(), (*output).into()],
            ),
            SetRun {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => self.call(
                "run",
                &[
                    (*state_ty).into(),
                    (*result_ty).into(),
                    (*step).into(),
                    (*initial).into(),
                    (*accessibility).into(),
                ],
            ),
            SetRunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => self.call(
                "runCase",
                &[
                    (*state_ty).into(),
                    (*result_ty).into(),
                    (*step).into(),
                    (*initial).into(),
                    (*transition).into(),
                    (*accessibility).into(),
                    (*transition_equality).into(),
                ],
            ),
            Recursor {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => self.call(
                "runStepRec",
                &[
                    *state_ty,
                    *result_ty,
                    *motive,
                    *on_continue,
                    *on_finish,
                    *scrutinee,
                ],
            ),
            BoxProgram {
                program_ty,
                program,
            } => self.call("box", &[(*program_ty).into(), (*program).into()]),
            ForceBox { program_ty, boxed } => {
                self.call("squash", &[(*program_ty).into(), (*boxed).into()])
            }
            BoxApp {
                function, argument, ..
            } => self.call("boxapp", &[(*function).into(), (*argument).into()]),
            BoxTypeApp {
                function, argument, ..
            } => self.call("boxapp", &[(*function).into(), (*argument).into()]),
            TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
            } => self.call(
                "Take",
                &[
                    (*domain).into(),
                    (*codomain).into(),
                    (*map).into(),
                    (*existence).into(),
                    (*uniqueness).into(),
                ],
            ),
            IndCtor {
                inductive,
                constructor,
                parameters,
            } => self.inductive(
                *inductive,
                Some(*constructor),
                parameters.iter().copied().map(Into::into).collect(),
            ),
            IndElim {
                inductive,
                scrutinee,
                motive,
                cases,
            } => self.elimination(true, *inductive, *scrutinee, *motive, cases.clone()),
            Case {
                inductive,
                scrutinee,
                motive,
                branches,
            } => self.elimination(false, *inductive, *scrutinee, *motive, branches.clone()),
            SetCase {
                inductive,
                binders,
                scrutinee,
                branches,
            } => self.case(
                *inductive,
                (*scrutinee).into(),
                binders,
                branches.iter().copied().map(Into::into).collect(),
            ),
            PowerSet { set } => self.call("Pow", &[(*set).into()]),
            TypeLift { superset, subset } => {
                self.call("Cast", &[(*superset).into(), (*subset).into()])
            }
            RunStep {
                state_ty,
                result_ty,
            } => self.call("RunStep", &[(*state_ty).into(), (*result_ty).into()]),
            BoxType { program_ty } => self.call("Box", &[(*program_ty).into()]),
            IndType {
                inductive,
                parameters,
            } => self.inductive(
                *inductive,
                None,
                parameters.iter().copied().map(Into::into).collect(),
            ),
            IdRefl { element } => self.call("refl", &[(*element).into()]),
            ExistsIntro { element, set } => self.call("exact", &[(*element).into(), (*set).into()]),
            SubsetElim {
                element,
                subset,
                superset,
            } => self.call(
                "subset_elim",
                &[(*element).into(), (*subset).into(), (*superset).into()],
            ),
            IdElim {
                var,
                left,
                right,
                ty,
                predicate,
                base,
                equality,
            } => self.id_elim(
                *var,
                (*left).into(),
                (*right).into(),
                (*ty).into(),
                (*predicate).into(),
                (*base).into(),
                (*equality).into(),
            ),
            TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => self.call(
                "TakeProp",
                &[
                    (*domain).into(),
                    (*proposition).into(),
                    (*map).into(),
                    (*existence).into(),
                ],
            ),
            TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
            } => self.call(
                "takeelim",
                &[
                    (*func).into(),
                    (*domain).into(),
                    (*codomain).into(),
                    (*element).into(),
                    (*existence).into(),
                    (*uniqueness).into(),
                ],
            ),
            SetExt {
                left,
                right,
                left_to_right,
                right_to_left,
            } => self.call(
                "axiom:setext",
                &[
                    (*left).into(),
                    (*right).into(),
                    (*left_to_right).into(),
                    (*right_to_left).into(),
                ],
            ),
            FunExt {
                left,
                right,
                pointwise,
            } => self.call(
                "axiom:funext",
                &[(*left).into(), (*right).into(), (*pointwise).into()],
            ),
            ClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            } => self.call(
                "axiom:classicalIndefiniteChoice",
                &[(*domain).into(), (*family).into(), (*inhabited).into()],
            ),
            AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
            } => self.call(
                "accintro",
                &[
                    (*state_ty).into(),
                    (*result_ty).into(),
                    (*step).into(),
                    (*state).into(),
                    (*predecessors).into(),
                ],
            ),
            AccDescent {
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
            } => self.call(
                "accdescent",
                &[
                    (*state_ty).into(),
                    (*result_ty).into(),
                    (*step).into(),
                    (*from).into(),
                    (*to).into(),
                    (*accessibility).into(),
                    (*transition).into(),
                ],
            ),
            Pred {
                superset,
                subset,
                element,
            } => self.call(
                "In",
                &[(*superset).into(), (*subset).into(), (*element).into()],
            ),
            Equal { left, right } => Term::new(
                format!(
                    "{} = {}",
                    self.expression(*left, 2),
                    self.expression(*right, 2)
                ),
                1,
            ),
            Exists { set } => self.call("exists", &[(*set).into()]),
            Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => self.call(
                "Acc",
                &[
                    (*state_ty).into(),
                    (*result_ty).into(),
                    (*step).into(),
                    (*state).into(),
                ],
            ),
            ThunkValue { computation } => self.call("thunk", &[(*computation).into()]),
            ProgramContinue {
                state_ty,
                result_ty,
                next,
            } => self.call(
                "continue",
                &[(*state_ty).into(), (*result_ty).into(), (*next).into()],
            ),
            ProgramFinish {
                state_ty,
                result_ty,
                output,
            } => self.call(
                "finish",
                &[(*state_ty).into(), (*result_ty).into(), (*output).into()],
            ),
            InductiveConstructor {
                inductive,
                constructor,
                parameters,
                fields,
            } => self.datatype_constructor(
                *inductive,
                *constructor,
                parameters.iter().copied().map(Into::into).collect(),
                fields.iter().copied().map(Into::into).collect(),
            ),
            Thunk { computation_ty } => self.call("U", &[(*computation_ty).into()]),
            ProgramRunStep {
                state_ty,
                result_ty,
            } => self.call("RunStep", &[(*state_ty).into(), (*result_ty).into()]),
            Inductive {
                inductive,
                parameters,
            } => self.datatype(
                *inductive,
                None,
                parameters.iter().copied().map(Into::into).collect(),
            ),
            Return { value } => self.call("return", &[(*value).into()]),
            Force { value } => self.call("force", &[(*value).into()]),
            Sequence {
                var,
                value_ty,
                computation,
                body,
            } => self.let_term(
                *var,
                (*value_ty).into(),
                (*computation).into(),
                (*body).into(),
                true,
            ),
            ValueLet {
                var,
                value_ty,
                value,
                body,
            } => self.let_term(
                *var,
                (*value_ty).into(),
                (*value).into(),
                (*body).into(),
                false,
            ),
            ProgramCase {
                inductive,
                binders,
                scrutinee,
                branches,
            } => self.case(
                *inductive,
                (*scrutinee).into(),
                binders,
                branches.iter().copied().map(Into::into).collect(),
            ),
            Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => self.call(
                "run",
                &[
                    (*state_ty).into(),
                    (*result_ty).into(),
                    (*step).into(),
                    (*initial).into(),
                    (*accessibility).into(),
                ],
            ),
            RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => self.call(
                "runCase",
                &[
                    (*state_ty).into(),
                    (*result_ty).into(),
                    (*step).into(),
                    (*initial).into(),
                    (*transition).into(),
                    (*accessibility).into(),
                    (*transition_equality).into(),
                ],
            ),
            ReturnType { value_ty } => self.call("F", &[(*value_ty).into()]),
        }
    }
}
