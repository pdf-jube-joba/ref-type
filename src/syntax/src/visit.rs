//! Visit source occurrences across logical and Program syntax.
use crate::*;

pub trait VisitSources {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource));
}

impl<K: VisitSources> VisitSources for Expr<K> {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        if let Some(source) = self.source {
            visit(source);
        }
        self.kind.visit_sources(visit);
    }
}

impl<T: VisitSources> VisitSources for Box<T> {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        self.as_ref().visit_sources(visit);
    }
}
impl<T: VisitSources> VisitSources for Vec<T> {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        for value in self {
            value.visit_sources(visit);
        }
    }
}
impl<T: VisitSources> VisitSources for Option<T> {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        if let Some(value) = self {
            value.visit_sources(visit);
        }
    }
}
impl<A: VisitSources, B: VisitSources> VisitSources for (A, B) {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        self.0.visit_sources(visit);
        self.1.visit_sources(visit);
    }
}
impl<A: VisitSources, B: VisitSources, C: VisitSources> VisitSources for (A, B, C) {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        self.0.visit_sources(visit);
        self.1.visit_sources(visit);
        self.2.visit_sources(visit);
    }
}
impl VisitSources for Identifier {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        if let Some(source) = self.1 {
            visit(source);
        }
    }
}
impl VisitSources for AstSource {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        visit(*self);
    }
}
impl VisitSources for ModuleBody {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Inline(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::External => {}
        }
    }
}
impl VisitSources for MacroSeqAtom {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Capture(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::TokenCapture(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Rest(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Tok(_) => {}
            Self::Quoted(_) => {}
            Self::Seq(field_0) => {
                field_0.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for TokenMatchPattern {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Token(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Sequence(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Default => {}
        }
    }
}
impl VisitSources for ModuleItem {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Error { name, .. } => {
                name.visit_sources(visit);
            }
            Self::Definition {
                owner,
                name,
                binders,
                ty,
                body,
                ..
            } => {
                owner.visit_sources(visit);
                name.visit_sources(visit);
                binders.visit_sources(visit);
                ty.visit_sources(visit);
                body.visit_sources(visit);
            }
            Self::Inductive {
                type_name,
                parameters,
                indices,
                constructors,
                ..
            } => {
                type_name.visit_sources(visit);
                parameters.visit_sources(visit);
                indices.visit_sources(visit);
                constructors.visit_sources(visit);
            }
            Self::Record {
                type_name,
                parameters,
                fields,
                ..
            } => {
                type_name.visit_sources(visit);
                parameters.visit_sources(visit);
                fields.visit_sources(visit);
            }
            Self::ChildModule { .. } => {}
            Self::Import {
                path, import_name, ..
            } => {
                path.visit_sources(visit);
                import_name.visit_sources(visit);
            }
            Self::MathMacro {
                name,
                before,
                after,
                ..
            } => {
                name.visit_sources(visit);
                before.visit_sources(visit);
                after.visit_sources(visit);
            }
            Self::UserMacro {
                name,
                before,
                after,
                ..
            } => {
                name.visit_sources(visit);
                before.visit_sources(visit);
                after.visit_sources(visit);
            }
            Self::UseMacro {
                import_name,
                macro_name,
                ..
            } => {
                import_name.visit_sources(visit);
                macro_name.visit_sources(visit);
            }
            Self::Eval { exp, .. } => {
                exp.visit_sources(visit);
            }
            Self::Normalize { exp, .. } => {
                exp.visit_sources(visit);
            }
            Self::ComputationEval { exp, .. } => {
                exp.visit_sources(visit);
            }
            Self::ComputationNormalize { exp, .. } => {
                exp.visit_sources(visit);
            }
            Self::ValueCheck { exp, ty, .. } => {
                exp.visit_sources(visit);
                ty.visit_sources(visit);
            }
            Self::ComputationCheck { exp, ty, .. } => {
                exp.visit_sources(visit);
                ty.visit_sources(visit);
            }
            Self::ValueInfer { exp, .. } => {
                exp.visit_sources(visit);
            }
            Self::ComputationInfer { exp, .. } => {
                exp.visit_sources(visit);
            }
            Self::Check { exp, ty, .. } => {
                exp.visit_sources(visit);
                ty.visit_sources(visit);
            }
            Self::Infer { exp, .. } => {
                exp.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for AssociatedOwner {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        self.type_name.visit_sources(visit);
        self.parameters.visit_sources(visit);
    }
}
impl VisitSources for ModuleInstantiatePath {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::FromPackage { package, calls, .. } => {
                package.visit_sources(visit);
                calls.visit_sources(visit);
            }
            Self::FromCurrent { calls, .. } => {
                calls.visit_sources(visit);
            }
            Self::FromRoot { calls, .. } => {
                calls.visit_sources(visit);
            }
            Self::FromImport {
                import_name, calls, ..
            } => {
                import_name.visit_sources(visit);
                calls.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for MacroExp {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::RawExp(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::TemplateName(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::TokenParameter(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Splice(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Tok(_) => {}
            Self::Quoted(_) => {}
            Self::Seq(field_0) => {
                field_0.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for RightBind {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        self.vars.visit_sources(visit);
        self.ty.visit_sources(visit);
    }
}
impl VisitSources for ValueTypeExpKind {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Meta { token, .. } => {
                token.visit_sources(visit);
            }
            Self::Access {
                access, parameters, ..
            } => {
                access.visit_sources(visit);
                parameters.visit_sources(visit);
            }
            Self::Thunk(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::RunStep {
                state_ty,
                result_ty,
                ..
            } => {
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for ComputationTypeExpKind {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Meta { token, .. } => {
                token.visit_sources(visit);
            }
            Self::Return(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Function {
                domain, codomain, ..
            } => {
                domain.visit_sources(visit);
                codomain.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for ValueTermExpKind {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Meta { token, .. } => {
                token.visit_sources(visit);
            }
            Self::Access(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Record {
                datatype,
                parameters,
                fields,
                ..
            } => {
                datatype.visit_sources(visit);
                parameters.visit_sources(visit);
                fields.visit_sources(visit);
            }
            Self::Constructor {
                datatype,
                constructor,
                parameters,
                fields,
                ..
            } => {
                datatype.visit_sources(visit);
                constructor.visit_sources(visit);
                parameters.visit_sources(visit);
                fields.visit_sources(visit);
            }
            Self::Thunk(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Continue {
                state_ty,
                result_ty,
                next,
                ..
            } => {
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                next.visit_sources(visit);
            }
            Self::Finish {
                state_ty,
                result_ty,
                output,
                ..
            } => {
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                output.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for ComputationTermExpKind {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Meta { token, .. } => {
                token.visit_sources(visit);
            }
            Self::Access(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Associated {
                datatype,
                item,
                parameters,
                ..
            } => {
                datatype.visit_sources(visit);
                item.visit_sources(visit);
                parameters.visit_sources(visit);
            }
            Self::InferredProjection { value, field, .. } => {
                value.visit_sources(visit);
                field.visit_sources(visit);
            }
            Self::Return(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Force(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Lambda {
                var,
                value_ty,
                body,
                ..
            } => {
                var.visit_sources(visit);
                value_ty.visit_sources(visit);
                body.visit_sources(visit);
            }
            Self::Application {
                function,
                arguments,
                ..
            } => {
                function.visit_sources(visit);
                arguments.visit_sources(visit);
            }
            Self::Sequence {
                computation,
                var,
                value_ty,
                body,
                ..
            } => {
                computation.visit_sources(visit);
                var.visit_sources(visit);
                value_ty.visit_sources(visit);
                body.visit_sources(visit);
            }
            Self::ValueLet {
                var,
                value_ty,
                value,
                body,
                ..
            } => {
                var.visit_sources(visit);
                value_ty.visit_sources(visit);
                value.visit_sources(visit);
                body.visit_sources(visit);
            }
            Self::Case {
                datatype,
                scrutinee,
                branches,
                ..
            } => {
                datatype.visit_sources(visit);
                scrutinee.visit_sources(visit);
                branches.visit_sources(visit);
            }
            Self::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
                ..
            } => {
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                step.visit_sources(visit);
                initial.visit_sources(visit);
                accessibility.visit_sources(visit);
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
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                step.visit_sources(visit);
                initial.visit_sources(visit);
                transition.visit_sources(visit);
                accessibility.visit_sources(visit);
                transition_equality.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for ProgramFunctionExpKind {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Access(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Associated {
                datatype,
                item,
                parameters,
                ..
            } => {
                datatype.visit_sources(visit);
                item.visit_sources(visit);
                parameters.visit_sources(visit);
            }
            Self::Value(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Computation(field_0) => {
                field_0.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for Bind {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Named(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Subset {
                var, ty, predicate, ..
            } => {
                var.visit_sources(visit);
                ty.visit_sources(visit);
                predicate.visit_sources(visit);
            }
            Self::SubsetWithProof {
                var,
                ty,
                predicate,
                proof_var,
                ..
            } => {
                var.visit_sources(visit);
                ty.visit_sources(visit);
                predicate.visit_sources(visit);
                proof_var.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for LocalAccess {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Current { access, .. } => {
                access.visit_sources(visit);
            }
            Self::Named { access, child, .. } => {
                access.visit_sources(visit);
                child.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for SExpKind {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Meta { token, .. } => {
                token.visit_sources(visit);
            }
            Self::AccessPath {
                access, parameters, ..
            } => {
                access.visit_sources(visit);
                parameters.visit_sources(visit);
            }
            Self::AssociatedAccess { base, field, .. } => {
                base.visit_sources(visit);
                field.visit_sources(visit);
            }
            Self::InferredProjection { value, field, .. } => {
                value.visit_sources(visit);
                field.visit_sources(visit);
            }
            Self::MathMacro { tokens, .. } => {
                tokens.visit_sources(visit);
            }
            Self::NamedMacro { name, tokens, .. } => {
                name.visit_sources(visit);
                tokens.visit_sources(visit);
            }
            Self::MacroParameter(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::TokenMatch {
                target, branches, ..
            } => {
                target.visit_sources(visit);
                branches.visit_sources(visit);
            }
            Self::Where { exp, clauses, .. } => {
                exp.visit_sources(visit);
                clauses.visit_sources(visit);
            }
            Self::Sort(_) => {}
            Self::ValueType => {}
            Self::Prod { bind, body, .. } => {
                bind.visit_sources(visit);
                body.visit_sources(visit);
            }
            Self::Lam { bind, body, .. } => {
                bind.visit_sources(visit);
                body.visit_sources(visit);
            }
            Self::App { func, arg, .. } => {
                func.visit_sources(visit);
                arg.visit_sources(visit);
            }
            Self::SubsetIntro {
                superset,
                subset,
                element,
                proof,
                ..
            } => {
                superset.visit_sources(visit);
                subset.visit_sources(visit);
                element.visit_sources(visit);
                proof.visit_sources(visit);
            }
            Self::IndCase {
                path,
                scrutinee,
                return_type,
                branches,
                ..
            } => {
                path.visit_sources(visit);
                scrutinee.visit_sources(visit);
                return_type.visit_sources(visit);
                branches.visit_sources(visit);
            }
            Self::Induction {
                binder,
                return_type,
                cases,
                ..
            } => {
                binder.visit_sources(visit);
                return_type.visit_sources(visit);
                cases.visit_sources(visit);
            }
            Self::IndElimPrim {
                path,
                parameters,
                motive,
                ..
            } => {
                path.visit_sources(visit);
                parameters.visit_sources(visit);
                motive.visit_sources(visit);
            }
            Self::ThunkType { computation_ty, .. } => {
                computation_ty.visit_sources(visit);
            }
            Self::ReturnType { value_ty, .. } => {
                value_ty.visit_sources(visit);
            }
            Self::ComputationFunction {
                domain, codomain, ..
            } => {
                domain.visit_sources(visit);
                codomain.visit_sources(visit);
            }
            Self::Thunk { computation, .. } => {
                computation.visit_sources(visit);
            }
            Self::Return { value, .. } => {
                value.visit_sources(visit);
            }
            Self::Force { value, .. } => {
                value.visit_sources(visit);
            }
            Self::ComputationLam {
                var,
                value_ty,
                body,
                ..
            } => {
                var.visit_sources(visit);
                value_ty.visit_sources(visit);
                body.visit_sources(visit);
            }
            Self::Sequence {
                computation,
                var,
                value_ty,
                body,
                ..
            } => {
                computation.visit_sources(visit);
                var.visit_sources(visit);
                value_ty.visit_sources(visit);
                body.visit_sources(visit);
            }
            Self::ValueLet {
                var,
                value_ty,
                value,
                body,
                ..
            } => {
                var.visit_sources(visit);
                value_ty.visit_sources(visit);
                value.visit_sources(visit);
                body.visit_sources(visit);
            }
            Self::ProgramCase {
                path,
                scrutinee,
                branches,
                ..
            } => {
                path.visit_sources(visit);
                scrutinee.visit_sources(visit);
                branches.visit_sources(visit);
            }
            Self::RunStep {
                state_ty,
                result_ty,
                ..
            } => {
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
            }
            Self::Continue {
                state_ty,
                result_ty,
                next,
                ..
            } => {
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                next.visit_sources(visit);
            }
            Self::Finish {
                state_ty,
                result_ty,
                output,
                ..
            } => {
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                output.visit_sources(visit);
            }
            Self::Acc {
                state_ty,
                result_ty,
                step,
                state,
                ..
            } => {
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                step.visit_sources(visit);
                state.visit_sources(visit);
            }
            Self::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
                ..
            } => {
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                step.visit_sources(visit);
                initial.visit_sources(visit);
                accessibility.visit_sources(visit);
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
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                step.visit_sources(visit);
                initial.visit_sources(visit);
                transition.visit_sources(visit);
                accessibility.visit_sources(visit);
                transition_equality.visit_sources(visit);
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
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                motive.visit_sources(visit);
                on_continue.visit_sources(visit);
                on_finish.visit_sources(visit);
                scrutinee.visit_sources(visit);
            }
            Self::BoxType { program_ty, .. } => {
                program_ty.visit_sources(visit);
            }
            Self::BoxProgram {
                program_ty,
                program,
                ..
            } => {
                program_ty.visit_sources(visit);
                program.visit_sources(visit);
            }
            Self::ForceBox {
                program_ty, boxed, ..
            } => {
                program_ty.visit_sources(visit);
                boxed.visit_sources(visit);
            }
            Self::BoxApp {
                function, argument, ..
            } => {
                function.visit_sources(visit);
                argument.visit_sources(visit);
            }
            Self::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
                ..
            } => {
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                step.visit_sources(visit);
                state.visit_sources(visit);
                predecessors.visit_sources(visit);
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
                state_ty.visit_sources(visit);
                result_ty.visit_sources(visit);
                step.visit_sources(visit);
                from.visit_sources(visit);
                to.visit_sources(visit);
                accessibility.visit_sources(visit);
                transition.visit_sources(visit);
            }
            Self::RecordTypeCtor {
                access,
                parameters,
                fields,
                ..
            } => {
                access.visit_sources(visit);
                parameters.visit_sources(visit);
                fields.visit_sources(visit);
            }
            Self::PowerSet { set, .. } => {
                set.visit_sources(visit);
            }
            Self::SubSet {
                var,
                set,
                predicate,
                ..
            } => {
                var.visit_sources(visit);
                set.visit_sources(visit);
                predicate.visit_sources(visit);
            }
            Self::Pred {
                superset,
                subset,
                element,
                ..
            } => {
                superset.visit_sources(visit);
                subset.visit_sources(visit);
                element.visit_sources(visit);
            }
            Self::TypeLift {
                superset, subset, ..
            } => {
                superset.visit_sources(visit);
                subset.visit_sources(visit);
            }
            Self::Equal { left, right, .. } => {
                left.visit_sources(visit);
                right.visit_sources(visit);
            }
            Self::Exists { bind, .. } => {
                bind.visit_sources(visit);
            }
            Self::TakeSet {
                bind,
                body,
                existence,
                uniqueness,
                ..
            } => {
                bind.visit_sources(visit);
                body.visit_sources(visit);
                existence.visit_sources(visit);
                uniqueness.visit_sources(visit);
            }
            Self::TakeProp {
                bind,
                body,
                existence,
                ..
            } => {
                bind.visit_sources(visit);
                body.visit_sources(visit);
                existence.visit_sources(visit);
            }
            Self::ExistsIntro { element, set, .. } => {
                element.visit_sources(visit);
                set.visit_sources(visit);
            }
            Self::SubsetElim {
                element,
                subset,
                superset,
                ..
            } => {
                element.visit_sources(visit);
                subset.visit_sources(visit);
                superset.visit_sources(visit);
            }
            Self::IdRefl { element, .. } => {
                element.visit_sources(visit);
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
                left.visit_sources(visit);
                right.visit_sources(visit);
                var.visit_sources(visit);
                ty.visit_sources(visit);
                predicate.visit_sources(visit);
                base.visit_sources(visit);
                equality.visit_sources(visit);
            }
            Self::AxiomSetExt {
                left,
                right,
                left_to_right,
                right_to_left,
                ..
            } => {
                left.visit_sources(visit);
                right.visit_sources(visit);
                left_to_right.visit_sources(visit);
                right_to_left.visit_sources(visit);
            }
            Self::AxiomFunExt {
                left,
                right,
                pointwise,
                ..
            } => {
                left.visit_sources(visit);
                right.visit_sources(visit);
                pointwise.visit_sources(visit);
            }
            Self::AxiomClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
                ..
            } => {
                domain.visit_sources(visit);
                family.visit_sources(visit);
                inhabited.visit_sources(visit);
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
                func.visit_sources(visit);
                domain.visit_sources(visit);
                codomain.visit_sources(visit);
                element.visit_sources(visit);
                existence.visit_sources(visit);
                uniqueness.visit_sources(visit);
            }
            Self::Block(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Program(field_0) => {
                field_0.visit_sources(visit);
            }
        }
    }
}
impl VisitSources for Block {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        self.statements.visit_sources(visit);
        self.result.visit_sources(visit);
    }
}
impl VisitSources for Statement {
    fn visit_sources(&self, visit: &mut impl FnMut(AstSource)) {
        match self {
            Self::Fix(field_0) => {
                field_0.visit_sources(visit);
            }
            Self::Let { var, ty, body, .. } => {
                var.visit_sources(visit);
                ty.visit_sources(visit);
                body.visit_sources(visit);
            }
            Self::Bind {
                var,
                ty,
                computation,
                ..
            } => {
                var.visit_sources(visit);
                ty.visit_sources(visit);
                computation.visit_sources(visit);
            }
            Self::Sufficient { map, map_ty, .. } => {
                map.visit_sources(visit);
                map_ty.visit_sources(visit);
            }
            Self::TakeFrom {
                var, ty, existence, ..
            } => {
                var.visit_sources(visit);
                ty.visit_sources(visit);
                existence.visit_sources(visit);
            }
        }
    }
}
