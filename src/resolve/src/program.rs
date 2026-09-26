//! Recover the common expression shape for resolution of Program queries.
use crate::hir::*;
fn boxed<T: Into<SExp>>(value: T) -> Box<SExp> {
    Box::new(value.into())
}
impl From<ValueTypeExp> for SExp {
    fn from(value: ValueTypeExp) -> Self {
        match value {
            ValueTypeExp::Meta { kind, span } => Self::Meta { kind, span },
            ValueTypeExp::Access { access, parameters } => Self::AccessPath {
                access,
                parameters: parameters.into_iter().map(Into::into).collect(),
            },
            ValueTypeExp::Thunk(value) => Self::ThunkType {
                computation_ty: boxed(*value),
            },
            ValueTypeExp::RunStep {
                state_ty,
                result_ty,
            } => Self::RunStep {
                state_ty: boxed(*state_ty),
                result_ty: boxed(*result_ty),
            },
        }
    }
}
impl From<ComputationTypeExp> for SExp {
    fn from(value: ComputationTypeExp) -> Self {
        match value {
            ComputationTypeExp::Meta { kind, span } => Self::Meta { kind, span },
            ComputationTypeExp::Return(value) => Self::ReturnType {
                value_ty: boxed(*value),
            },
            ComputationTypeExp::Function { domain, codomain } => Self::ComputationFunction {
                domain: boxed(*domain),
                codomain: boxed(*codomain),
            },
        }
    }
}
impl From<ValueTermExp> for SExp {
    fn from(value: ValueTermExp) -> Self {
        match value {
            ValueTermExp::Meta { kind, span } => Self::Meta { kind, span },
            ValueTermExp::Access(access) => Self::AccessPath {
                access,
                parameters: Vec::new(),
            },
            ValueTermExp::Record {
                datatype,
                parameters,
                fields,
            } => Self::RecordTypeCtor {
                access: datatype,
                parameters: parameters.into_iter().map(Into::into).collect(),
                fields: fields
                    .into_iter()
                    .map(|(name, value)| (name, value.into()))
                    .collect(),
            },
            ValueTermExp::Constructor {
                span,
                datatype,
                constructor,
                parameters,
                fields,
            } => {
                let mut result = Self::AssociatedAccess {
                    span,
                    base: Box::new(Self::AccessPath {
                        access: datatype,
                        parameters: parameters.into_iter().map(Into::into).collect(),
                    }),
                    field: constructor,
                };
                for field in fields {
                    result = Self::App {
                        func: Box::new(result),
                        arg: Box::new(field.into()),
                    };
                }
                result
            }
            ValueTermExp::Thunk(value) => Self::Thunk {
                computation: boxed(*value),
            },
            ValueTermExp::Continue {
                state_ty,
                result_ty,
                next,
            } => Self::Continue {
                state_ty: boxed(*state_ty),
                result_ty: boxed(*result_ty),
                next: boxed(*next),
            },
            ValueTermExp::Finish {
                state_ty,
                result_ty,
                output,
            } => Self::Finish {
                state_ty: boxed(*state_ty),
                result_ty: boxed(*result_ty),
                output: boxed(*output),
            },
        }
    }
}
impl From<ProgramFunctionExp> for SExp {
    fn from(value: ProgramFunctionExp) -> Self {
        match value {
            ProgramFunctionExp::Access(access) => Self::AccessPath {
                access,
                parameters: Vec::new(),
            },
            ProgramFunctionExp::Associated {
                span,
                datatype,
                item,
                parameters,
            } => Self::AssociatedAccess {
                span,
                base: Box::new(Self::AccessPath {
                    access: datatype,
                    parameters: parameters.into_iter().map(Into::into).collect(),
                }),
                field: item,
            },
            ProgramFunctionExp::Value(value) => (*value).into(),
            ProgramFunctionExp::Computation(value) => (*value).into(),
        }
    }
}
impl From<ComputationTermExp> for SExp {
    fn from(value: ComputationTermExp) -> Self {
        match value {
            ComputationTermExp::Meta { kind, span } => Self::Meta { kind, span },
            ComputationTermExp::Access(access) => Self::AccessPath {
                access,
                parameters: Vec::new(),
            },
            ComputationTermExp::Associated {
                span,
                datatype,
                item,
                parameters,
            } => Self::AssociatedAccess {
                span,
                base: Box::new(Self::AccessPath {
                    access: datatype,
                    parameters: parameters.into_iter().map(Into::into).collect(),
                }),
                field: item,
            },
            ComputationTermExp::InferredProjection { value, field } => Self::InferredProjection {
                value: boxed(*value),
                field,
            },
            ComputationTermExp::Return(value) => Self::Return {
                value: boxed(*value),
            },
            ComputationTermExp::Force(value) => Self::Force {
                value: boxed(*value),
            },
            ComputationTermExp::Lambda {
                var,
                value_ty,
                body,
            } => Self::ComputationLam {
                var,
                value_ty: boxed(*value_ty),
                body: boxed(*body),
            },
            ComputationTermExp::Application {
                function,
                arguments,
            } => {
                let mut result = function.into();
                for arg in arguments {
                    result = Self::App {
                        func: Box::new(result),
                        arg: Box::new(arg.into()),
                    };
                }
                result
            }
            ComputationTermExp::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => Self::Sequence {
                computation: boxed(*computation),
                var,
                value_ty: boxed(*value_ty),
                body: boxed(*body),
            },
            ComputationTermExp::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => Self::ValueLet {
                var,
                value_ty: boxed(*value_ty),
                value: boxed(*value),
                body: boxed(*body),
            },
            ComputationTermExp::Case {
                datatype,
                scrutinee,
                branches,
            } => Self::ProgramCase {
                path: datatype,
                scrutinee: boxed(*scrutinee),
                branches: branches
                    .into_iter()
                    .map(|(name, vars, body)| (name, vars, body.into()))
                    .collect(),
            },
            ComputationTermExp::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => Self::Run {
                state_ty: boxed(*state_ty),
                result_ty: boxed(*result_ty),
                step: boxed(*step),
                initial: boxed(*initial),
                accessibility,
            },
            ComputationTermExp::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => Self::RunCase {
                state_ty: boxed(*state_ty),
                result_ty: boxed(*result_ty),
                step: boxed(*step),
                initial: boxed(*initial),
                transition: boxed(*transition),
                accessibility,
                transition_equality,
            },
        }
    }
}
