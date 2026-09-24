//! Visit HIR occurrences independently of shared semantic terms.
use crate::*;

pub trait VisitOrigins {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    );
}

impl<K: VisitOrigins> VisitOrigins for Expr<K> {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        visit(&mut self.origin, parent);
        self.kind.visit_origins(self.origin, visit);
    }
}

impl<T: VisitOrigins> VisitOrigins for Box<T> {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        self.as_mut().visit_origins(parent, visit);
    }
}
impl<T: VisitOrigins> VisitOrigins for Vec<T> {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        for value in self {
            value.visit_origins(parent, visit);
        }
    }
}
impl<T: VisitOrigins> VisitOrigins for Option<T> {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        if let Some(value) = self {
            value.visit_origins(parent, visit);
        }
    }
}
impl<A: VisitOrigins, B: VisitOrigins> VisitOrigins for (A, B) {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        self.0.visit_origins(parent, visit);
        self.1.visit_origins(parent, visit);
    }
}
impl<A: VisitOrigins, B: VisitOrigins, C: VisitOrigins> VisitOrigins for (A, B, C) {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        self.0.visit_origins(parent, visit);
        self.1.visit_origins(parent, visit);
        self.2.visit_origins(parent, visit);
    }
}
impl VisitOrigins for Identifier {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        visit(&mut self.1, parent);
    }
}

impl VisitOrigins for MacroExp {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::RawExp(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::TemplateName(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::TokenParameter(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Splice(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Tok(_) => {}
            Self::Quoted(_) => {}
            Self::Seq(field_0) => {
                field_0.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for RightBind {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        self.vars.visit_origins(parent, visit);
        self.ty.visit_origins(parent, visit);
    }
}
impl VisitOrigins for ValueTypeExpKind {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Meta { token, .. } => {
                visit(token, parent);
            }
            Self::Access {
                access, parameters, ..
            } => {
                access.visit_origins(parent, visit);
                parameters.visit_origins(parent, visit);
            }
            Self::Thunk(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::RunStep {
                state_ty,
                result_ty,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for ComputationTypeExpKind {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Meta { token, .. } => {
                visit(token, parent);
            }
            Self::Return(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Function {
                domain, codomain, ..
            } => {
                domain.visit_origins(parent, visit);
                codomain.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for ValueTermExpKind {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Meta { token, .. } => {
                visit(token, parent);
            }
            Self::Access(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Record {
                datatype,
                parameters,
                fields,
                ..
            } => {
                datatype.visit_origins(parent, visit);
                parameters.visit_origins(parent, visit);
                fields.visit_origins(parent, visit);
            }
            Self::Constructor {
                datatype,
                constructor,
                parameters,
                fields,
                ..
            } => {
                datatype.visit_origins(parent, visit);
                constructor.visit_origins(parent, visit);
                parameters.visit_origins(parent, visit);
                fields.visit_origins(parent, visit);
            }
            Self::Thunk(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Continue {
                state_ty,
                result_ty,
                next,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                next.visit_origins(parent, visit);
            }
            Self::Finish {
                state_ty,
                result_ty,
                output,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                output.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for ComputationTermExpKind {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Meta { token, .. } => {
                visit(token, parent);
            }
            Self::Access(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Associated {
                datatype,
                item,
                parameters,
                ..
            } => {
                datatype.visit_origins(parent, visit);
                item.visit_origins(parent, visit);
                parameters.visit_origins(parent, visit);
            }
            Self::InferredProjection { value, field, .. } => {
                value.visit_origins(parent, visit);
                field.visit_origins(parent, visit);
            }
            Self::Return(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Force(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Lambda {
                var,
                value_ty,
                body,
                ..
            } => {
                var.visit_origins(parent, visit);
                value_ty.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
            }
            Self::Application {
                function,
                arguments,
                ..
            } => {
                function.visit_origins(parent, visit);
                arguments.visit_origins(parent, visit);
            }
            Self::Sequence {
                computation,
                var,
                value_ty,
                body,
                ..
            } => {
                computation.visit_origins(parent, visit);
                var.visit_origins(parent, visit);
                value_ty.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
            }
            Self::ValueLet {
                var,
                value_ty,
                value,
                body,
                ..
            } => {
                var.visit_origins(parent, visit);
                value_ty.visit_origins(parent, visit);
                value.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
            }
            Self::Case {
                datatype,
                scrutinee,
                branches,
                ..
            } => {
                datatype.visit_origins(parent, visit);
                scrutinee.visit_origins(parent, visit);
                branches.visit_origins(parent, visit);
            }
            Self::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                step.visit_origins(parent, visit);
                initial.visit_origins(parent, visit);
                accessibility.visit_origins(parent, visit);
            }
            Self::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                step.visit_origins(parent, visit);
                initial.visit_origins(parent, visit);
                transition.visit_origins(parent, visit);
                accessibility.visit_origins(parent, visit);
                transition_equality.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for ProgramFunctionExpKind {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Access(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Associated {
                datatype,
                item,
                parameters,
                ..
            } => {
                datatype.visit_origins(parent, visit);
                item.visit_origins(parent, visit);
                parameters.visit_origins(parent, visit);
            }
            Self::Value(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Computation(field_0) => {
                field_0.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for Bind {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Named(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Subset {
                var, ty, predicate, ..
            } => {
                var.visit_origins(parent, visit);
                ty.visit_origins(parent, visit);
                predicate.visit_origins(parent, visit);
            }
            Self::SubsetWithProof {
                var,
                ty,
                predicate,
                proof_var,
                ..
            } => {
                var.visit_origins(parent, visit);
                ty.visit_origins(parent, visit);
                predicate.visit_origins(parent, visit);
                proof_var.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for LocalAccess {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Current { access, .. } => {
                access.visit_origins(parent, visit);
            }
            Self::Named { access, child, .. } => {
                access.visit_origins(parent, visit);
                child.visit_origins(parent, visit);
            }
            Self::Resolved { access, .. } => {
                access.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for SExpKind {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Meta { token, .. } => {
                visit(token, parent);
            }
            Self::AccessPath {
                access, parameters, ..
            } => {
                access.visit_origins(parent, visit);
                parameters.visit_origins(parent, visit);
            }
            Self::AssociatedAccess { base, field, .. } => {
                base.visit_origins(parent, visit);
                field.visit_origins(parent, visit);
            }
            Self::InferredProjection { value, field, .. } => {
                value.visit_origins(parent, visit);
                field.visit_origins(parent, visit);
            }
            Self::MathMacro { tokens, .. } => {
                tokens.visit_origins(parent, visit);
            }
            Self::NamedMacro { name, tokens, .. } => {
                name.visit_origins(parent, visit);
                tokens.visit_origins(parent, visit);
            }
            Self::MacroParameter(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::TokenMatch {
                target, branches, ..
            } => {
                target.visit_origins(parent, visit);
                branches.visit_origins(parent, visit);
            }
            Self::Captured(_) => {}
            Self::Where { exp, clauses, .. } => {
                exp.visit_origins(parent, visit);
                clauses.visit_origins(parent, visit);
            }
            Self::Sort(_) => {}
            Self::ValueType => {}
            Self::Prod { bind, body, .. } => {
                bind.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
            }
            Self::Lam { bind, body, .. } => {
                bind.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
            }
            Self::App { func, arg, .. } => {
                func.visit_origins(parent, visit);
                arg.visit_origins(parent, visit);
            }
            Self::SubsetIntro {
                superset,
                subset,
                element,
                proof,
                ..
            } => {
                superset.visit_origins(parent, visit);
                subset.visit_origins(parent, visit);
                element.visit_origins(parent, visit);
                proof.visit_origins(parent, visit);
            }
            Self::IndCase {
                path,
                scrutinee,
                return_type,
                branches,
                ..
            } => {
                path.visit_origins(parent, visit);
                scrutinee.visit_origins(parent, visit);
                return_type.visit_origins(parent, visit);
                branches.visit_origins(parent, visit);
            }
            Self::Induction {
                binder,
                return_type,
                cases,
                ..
            } => {
                binder.visit_origins(parent, visit);
                return_type.visit_origins(parent, visit);
                cases.visit_origins(parent, visit);
            }
            Self::IndElimPrim {
                path,
                parameters,
                motive,
                ..
            } => {
                path.visit_origins(parent, visit);
                parameters.visit_origins(parent, visit);
                motive.visit_origins(parent, visit);
            }
            Self::ThunkType { computation_ty, .. } => {
                computation_ty.visit_origins(parent, visit);
            }
            Self::ReturnType { value_ty, .. } => {
                value_ty.visit_origins(parent, visit);
            }
            Self::ComputationFunction {
                domain, codomain, ..
            } => {
                domain.visit_origins(parent, visit);
                codomain.visit_origins(parent, visit);
            }
            Self::Thunk { computation, .. } => {
                computation.visit_origins(parent, visit);
            }
            Self::Return { value, .. } => {
                value.visit_origins(parent, visit);
            }
            Self::Force { value, .. } => {
                value.visit_origins(parent, visit);
            }
            Self::ComputationLam {
                var,
                value_ty,
                body,
                ..
            } => {
                var.visit_origins(parent, visit);
                value_ty.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
            }
            Self::Sequence {
                computation,
                var,
                value_ty,
                body,
                ..
            } => {
                computation.visit_origins(parent, visit);
                var.visit_origins(parent, visit);
                value_ty.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
            }
            Self::ValueLet {
                var,
                value_ty,
                value,
                body,
                ..
            } => {
                var.visit_origins(parent, visit);
                value_ty.visit_origins(parent, visit);
                value.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
            }
            Self::ProgramCase {
                path,
                scrutinee,
                branches,
                ..
            } => {
                path.visit_origins(parent, visit);
                scrutinee.visit_origins(parent, visit);
                branches.visit_origins(parent, visit);
            }
            Self::RunStep {
                state_ty,
                result_ty,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
            }
            Self::Continue {
                state_ty,
                result_ty,
                next,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                next.visit_origins(parent, visit);
            }
            Self::Finish {
                state_ty,
                result_ty,
                output,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                output.visit_origins(parent, visit);
            }
            Self::Acc {
                state_ty,
                result_ty,
                step,
                state,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                step.visit_origins(parent, visit);
                state.visit_origins(parent, visit);
            }
            Self::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                step.visit_origins(parent, visit);
                initial.visit_origins(parent, visit);
                accessibility.visit_origins(parent, visit);
            }
            Self::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                step.visit_origins(parent, visit);
                initial.visit_origins(parent, visit);
                transition.visit_origins(parent, visit);
                accessibility.visit_origins(parent, visit);
                transition_equality.visit_origins(parent, visit);
            }
            Self::RunStepRec {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                motive.visit_origins(parent, visit);
                on_continue.visit_origins(parent, visit);
                on_finish.visit_origins(parent, visit);
                scrutinee.visit_origins(parent, visit);
            }
            Self::BoxType { program_ty, .. } => {
                program_ty.visit_origins(parent, visit);
            }
            Self::BoxProgram {
                program_ty,
                program,
                ..
            } => {
                program_ty.visit_origins(parent, visit);
                program.visit_origins(parent, visit);
            }
            Self::ForceBox {
                program_ty, boxed, ..
            } => {
                program_ty.visit_origins(parent, visit);
                boxed.visit_origins(parent, visit);
            }
            Self::BoxApp {
                function, argument, ..
            } => {
                function.visit_origins(parent, visit);
                argument.visit_origins(parent, visit);
            }
            Self::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                step.visit_origins(parent, visit);
                state.visit_origins(parent, visit);
                predecessors.visit_origins(parent, visit);
            }
            Self::AccDescent {
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
                ..
            } => {
                state_ty.visit_origins(parent, visit);
                result_ty.visit_origins(parent, visit);
                step.visit_origins(parent, visit);
                from.visit_origins(parent, visit);
                to.visit_origins(parent, visit);
                accessibility.visit_origins(parent, visit);
                transition.visit_origins(parent, visit);
            }
            Self::RecordTypeCtor {
                access,
                parameters,
                fields,
                ..
            } => {
                access.visit_origins(parent, visit);
                parameters.visit_origins(parent, visit);
                fields.visit_origins(parent, visit);
            }
            Self::PowerSet { set, .. } => {
                set.visit_origins(parent, visit);
            }
            Self::SubSet {
                var,
                set,
                predicate,
                ..
            } => {
                var.visit_origins(parent, visit);
                set.visit_origins(parent, visit);
                predicate.visit_origins(parent, visit);
            }
            Self::Pred {
                superset,
                subset,
                element,
                ..
            } => {
                superset.visit_origins(parent, visit);
                subset.visit_origins(parent, visit);
                element.visit_origins(parent, visit);
            }
            Self::TypeLift {
                superset, subset, ..
            } => {
                superset.visit_origins(parent, visit);
                subset.visit_origins(parent, visit);
            }
            Self::Equal { left, right, .. } => {
                left.visit_origins(parent, visit);
                right.visit_origins(parent, visit);
            }
            Self::Exists { bind, .. } => {
                bind.visit_origins(parent, visit);
            }
            Self::TakeSet {
                bind,
                body,
                existence,
                uniqueness,
                ..
            } => {
                bind.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
                existence.visit_origins(parent, visit);
                uniqueness.visit_origins(parent, visit);
            }
            Self::TakeProp {
                bind,
                body,
                existence,
                ..
            } => {
                bind.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
                existence.visit_origins(parent, visit);
            }
            Self::ExistsIntro { element, set, .. } => {
                element.visit_origins(parent, visit);
                set.visit_origins(parent, visit);
            }
            Self::SubsetElim {
                element,
                subset,
                superset,
                ..
            } => {
                element.visit_origins(parent, visit);
                subset.visit_origins(parent, visit);
                superset.visit_origins(parent, visit);
            }
            Self::IdRefl { element, .. } => {
                element.visit_origins(parent, visit);
            }
            Self::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
                base,
                equality,
                ..
            } => {
                left.visit_origins(parent, visit);
                right.visit_origins(parent, visit);
                var.visit_origins(parent, visit);
                ty.visit_origins(parent, visit);
                predicate.visit_origins(parent, visit);
                base.visit_origins(parent, visit);
                equality.visit_origins(parent, visit);
            }
            Self::AxiomSetExt {
                left,
                right,
                left_to_right,
                right_to_left,
                ..
            } => {
                left.visit_origins(parent, visit);
                right.visit_origins(parent, visit);
                left_to_right.visit_origins(parent, visit);
                right_to_left.visit_origins(parent, visit);
            }
            Self::AxiomFunExt {
                left,
                right,
                pointwise,
                ..
            } => {
                left.visit_origins(parent, visit);
                right.visit_origins(parent, visit);
                pointwise.visit_origins(parent, visit);
            }
            Self::AxiomClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
                ..
            } => {
                domain.visit_origins(parent, visit);
                family.visit_origins(parent, visit);
                inhabited.visit_origins(parent, visit);
            }
            Self::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
                ..
            } => {
                func.visit_origins(parent, visit);
                domain.visit_origins(parent, visit);
                codomain.visit_origins(parent, visit);
                element.visit_origins(parent, visit);
                existence.visit_origins(parent, visit);
                uniqueness.visit_origins(parent, visit);
            }
            Self::Block(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Program(field_0) => {
                field_0.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for Block {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        self.statements.visit_origins(parent, visit);
        self.result.visit_origins(parent, visit);
    }
}
impl VisitOrigins for Statement {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Fix(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Let { var, ty, body, .. } => {
                var.visit_origins(parent, visit);
                ty.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
            }
            Self::Bind {
                var,
                ty,
                computation,
                ..
            } => {
                var.visit_origins(parent, visit);
                ty.visit_origins(parent, visit);
                computation.visit_origins(parent, visit);
            }
            Self::Sufficient { map, map_ty, .. } => {
                map.visit_origins(parent, visit);
                map_ty.visit_origins(parent, visit);
            }
            Self::TakeFrom {
                var, ty, existence, ..
            } => {
                var.visit_origins(parent, visit);
                ty.visit_origins(parent, visit);
                existence.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for ModuleBody {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Inline(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::External => {}
        }
    }
}
impl VisitOrigins for ModuleItem {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Error { name, .. } => {
                name.visit_origins(parent, visit);
            }
            Self::Definition {
                owner,
                name,
                binders,
                ty,
                body,
                ..
            } => {
                owner.visit_origins(parent, visit);
                name.visit_origins(parent, visit);
                binders.visit_origins(parent, visit);
                ty.visit_origins(parent, visit);
                body.visit_origins(parent, visit);
            }
            Self::Inductive {
                type_name,
                parameters,
                indices,
                constructors,
                ..
            } => {
                type_name.visit_origins(parent, visit);
                parameters.visit_origins(parent, visit);
                indices.visit_origins(parent, visit);
                constructors.visit_origins(parent, visit);
            }
            Self::Record {
                type_name,
                parameters,
                fields,
                ..
            } => {
                type_name.visit_origins(parent, visit);
                parameters.visit_origins(parent, visit);
                fields.visit_origins(parent, visit);
            }
            Self::ChildModule { .. } => {}
            Self::Import {
                path, import_name, ..
            } => {
                path.visit_origins(parent, visit);
                import_name.visit_origins(parent, visit);
            }
            Self::MathMacro {
                name,
                before,
                after,
                ..
            } => {
                name.visit_origins(parent, visit);
                before.visit_origins(parent, visit);
                after.visit_origins(parent, visit);
            }
            Self::UserMacro {
                name,
                before,
                after,
                ..
            } => {
                name.visit_origins(parent, visit);
                before.visit_origins(parent, visit);
                after.visit_origins(parent, visit);
            }
            Self::UseMacro {
                import_name,
                macro_name,
                ..
            } => {
                import_name.visit_origins(parent, visit);
                macro_name.visit_origins(parent, visit);
            }
            Self::Eval { exp, .. } => {
                exp.visit_origins(parent, visit);
            }
            Self::Normalize { exp, .. } => {
                exp.visit_origins(parent, visit);
            }
            Self::ComputationEval { exp, .. } => {
                exp.visit_origins(parent, visit);
            }
            Self::ComputationNormalize { exp, .. } => {
                exp.visit_origins(parent, visit);
            }
            Self::ValueCheck { exp, ty, .. } => {
                exp.visit_origins(parent, visit);
                ty.visit_origins(parent, visit);
            }
            Self::ComputationCheck { exp, ty, .. } => {
                exp.visit_origins(parent, visit);
                ty.visit_origins(parent, visit);
            }
            Self::ValueInfer { exp, .. } => {
                exp.visit_origins(parent, visit);
            }
            Self::ComputationInfer { exp, .. } => {
                exp.visit_origins(parent, visit);
            }
            Self::Check { exp, ty, .. } => {
                exp.visit_origins(parent, visit);
                ty.visit_origins(parent, visit);
            }
            Self::Infer { exp, .. } => {
                exp.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for AssociatedOwner {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        self.type_name.visit_origins(parent, visit);
        self.parameters.visit_origins(parent, visit);
    }
}
impl VisitOrigins for ModuleInstantiatePath {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::FromPackage { package, calls, .. } => {
                package.visit_origins(parent, visit);
                calls.visit_origins(parent, visit);
            }
            Self::FromCurrent { calls, .. } => {
                calls.visit_origins(parent, visit);
            }
            Self::FromRoot { calls, .. } => {
                calls.visit_origins(parent, visit);
            }
            Self::FromImport {
                import_name, calls, ..
            } => {
                import_name.visit_origins(parent, visit);
                calls.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for MacroSeqAtom {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Capture(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::TokenCapture(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Rest(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Tok(_) => {}
            Self::Quoted(_) => {}
            Self::Seq(field_0) => {
                field_0.visit_origins(parent, visit);
            }
        }
    }
}
impl VisitOrigins for TokenMatchPattern {
    fn visit_origins(
        &mut self,
        parent: Option<AstId>,
        visit: &mut impl FnMut(&mut Option<AstId>, Option<AstId>),
    ) {
        match self {
            Self::Token(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Sequence(field_0) => {
                field_0.visit_origins(parent, visit);
            }
            Self::Default => {}
        }
    }
}
