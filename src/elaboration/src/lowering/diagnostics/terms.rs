//! Surface rendering for the common expression syntax.
use super::*;
impl Renderer<'_> {
    pub(super) fn term(&mut self, e: Expression) -> Term {
        use Node::*;
        let node = self.arena.get(e);
        match &node {
            Ascribe { term, ty } => {
                let term = self.expression(*term, 1);
                let ty = self.expression(*ty, 1);
                Term::new(format!("{term} \\of {ty}"), 0)
            }
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
            } => self.subset(*var, *set, *predicate),
            SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => self.call(
                "into",
                &[
                    (*superset),
                    (*subset),
                    (*element),
                    (*proof),
                ],
            ),
            Continue {
                state_ty,
                result_ty,
                next,
            } => self.call(
                "continue",
                &[(*state_ty), (*result_ty), (*next)],
            ),
            Finish {
                state_ty,
                result_ty,
                output,
            } => self.call(
                "finish",
                &[(*state_ty), (*result_ty), (*output)],
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
                    (*state_ty),
                    (*result_ty),
                    (*step),
                    (*initial),
                    (*accessibility),
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
                    (*state_ty),
                    (*result_ty),
                    (*step),
                    (*initial),
                    (*transition),
                    (*accessibility),
                    (*transition_equality),
                ],
            ),
            SetStepMatch {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
            } => self.call(
                "stepMatchSet",
                &[
                    *state_ty,
                    *result_ty,
                    *motive,
                    *on_continue,
                    *on_finish,
                ],
            ),
            ProgramStepMatch {
                state_ty,
                result_ty,
                computation_ty,
                on_continue,
                on_finish,
                scrutinee,
            } => self.call(
                "programStepMatch",
                &[
                    *state_ty,
                    *result_ty,
                    *computation_ty,
                    *on_continue,
                    *on_finish,
                    *scrutinee,
                ],
            ),
            BoxProgram {
                program_ty,
                program,
            } => self.call("box", &[(*program_ty), (*program)]),
            ForceBox { program_ty, boxed } => {
                self.call("squash", &[(*program_ty), (*boxed)])
            }
            BoxApp {
                function, argument, ..
            } => self.call("boxapp", &[(*function), (*argument)]),
            BoxTypeApp {
                function, argument, ..
            } => self.call("boxapp", &[(*function), (*argument)]),
            TakeSet {
                domain,
                codomain,
                map,
                existence,
                uniqueness,
            } => self.call(
                "Take",
                &[
                    (*domain),
                    (*codomain),
                    (*map),
                    (*existence),
                    (*uniqueness),
                ],
            ),
            IndCtor {
                inductive,
                constructor,
                parameters,
            } => self.inductive(
                *inductive,
                Some(*constructor),
                parameters.to_vec(),
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
                *scrutinee,
                binders,
                branches.to_vec(),
            ),
            PowerSet { set } => self.call("Pow", &[(*set)]),
            TypeLift { superset, subset } => {
                self.call("Cast", &[(*superset), (*subset)])
            }
            RunStep {
                state_ty,
                result_ty,
            } => self.call("RunStep", &[(*state_ty), (*result_ty)]),
            BoxType { program_ty } => self.call("Box", &[(*program_ty)]),
            IndType {
                inductive,
                parameters,
            } => self.inductive(
                *inductive,
                None,
                parameters.to_vec(),
            ),
            IdRefl { element } => self.call("refl", &[(*element)]),
            ExistsIntro { element, set } => self.call("exact", &[(*element), (*set)]),
            SubsetElim {
                element,
                subset,
                superset,
            } => self.call(
                "subset_elim",
                &[(*element), (*subset), (*superset)],
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
                *left,
                *right,
                *ty,
                *predicate,
                *base,
                *equality,
            ),
            TakeProp {
                domain,
                proposition,
                map,
                existence,
            } => self.call(
                "TakeProp",
                &[
                    (*domain),
                    (*proposition),
                    (*map),
                    (*existence),
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
                    (*func),
                    (*domain),
                    (*codomain),
                    (*element),
                    (*existence),
                    (*uniqueness),
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
                    (*left),
                    (*right),
                    (*left_to_right),
                    (*right_to_left),
                ],
            ),
            FunExt {
                left,
                right,
                pointwise,
            } => self.call(
                "axiom:funext",
                &[(*left), (*right), (*pointwise)],
            ),
            ClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            } => self.call(
                "axiom:classicalIndefiniteChoice",
                &[(*domain), (*family), (*inhabited)],
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
                    (*state_ty),
                    (*result_ty),
                    (*step),
                    (*state),
                    (*predecessors),
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
                    (*state_ty),
                    (*result_ty),
                    (*step),
                    (*from),
                    (*to),
                    (*accessibility),
                    (*transition),
                ],
            ),
            Pred {
                superset,
                subset,
                element,
            } => self.call(
                "In",
                &[(*superset), (*subset), (*element)],
            ),
            Equal { left, right } => Term::new(
                format!(
                    "{} = {}",
                    self.expression(*left, 2),
                    self.expression(*right, 2)
                ),
                1,
            ),
            Exists { set } => self.call("exists", &[(*set)]),
            Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => self.call(
                "Acc",
                &[
                    (*state_ty),
                    (*result_ty),
                    (*step),
                    (*state),
                ],
            ),
            ThunkValue { computation } => self.call("thunk", &[(*computation)]),
            ProgramContinue {
                state_ty,
                result_ty,
                next,
            } => self.call(
                "continue",
                &[(*state_ty), (*result_ty), (*next)],
            ),
            ProgramFinish {
                state_ty,
                result_ty,
                output,
            } => self.call(
                "finish",
                &[(*state_ty), (*result_ty), (*output)],
            ),
            InductiveConstructor {
                inductive,
                constructor,
                parameters,
                fields,
            } => self.datatype_constructor(
                *inductive,
                *constructor,
                parameters.to_vec(),
                fields.to_vec(),
            ),
            Thunk { computation_ty } => self.call("U", &[(*computation_ty)]),
            ProgramRunStep {
                state_ty,
                result_ty,
            } => self.call("RunStep", &[(*state_ty), (*result_ty)]),
            Inductive {
                inductive,
                parameters,
            } => self.datatype(
                *inductive,
                None,
                parameters.to_vec(),
            ),
            Return { value } => self.call("return", &[(*value)]),
            Force { value } => self.call("force", &[(*value)]),
            Sequence {
                var,
                value_ty,
                computation,
                body,
            } => self.let_term(
                *var,
                *value_ty,
                *computation,
                *body,
                true,
            ),
            ValueLet {
                var,
                value_ty,
                value,
                body,
            } => self.let_term(
                *var,
                *value_ty,
                *value,
                *body,
                false,
            ),
            ProgramCase {
                inductive,
                binders,
                scrutinee,
                branches,
            } => self.case(
                *inductive,
                *scrutinee,
                binders,
                branches.to_vec(),
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
                    (*state_ty),
                    (*result_ty),
                    (*step),
                    (*initial),
                    (*accessibility),
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
                    (*state_ty),
                    (*result_ty),
                    (*step),
                    (*initial),
                    (*transition),
                    (*accessibility),
                    (*transition_equality),
                ],
            ),
            ReturnType { value_ty } => self.call("F", &[(*value_ty)]),
        }
    }
}
