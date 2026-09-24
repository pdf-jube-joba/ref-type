//! Lower parsed syntax to HIR occurrence identities.
use crate::*;

impl From<syntax::SurfaceMeta> for SurfaceMeta {
    fn from(value: syntax::SurfaceMeta) -> Self {
        Self {
            kind: value.kind,
            origin: MetaOrigin::Source,
        }
    }
}
impl From<syntax::Module> for Module {
    fn from(value: syntax::Module) -> Self {
        Self {
            name: value.name.into(),
            parameters: value
                .parameters
                .into_iter()
                .map(|item0| item0.into())
                .collect(),
            body: value.body.into(),
            span: value.span,
            declaration_spans: value.declaration_spans.into_iter().collect(),
            source: value.source,
            header_source: value.header_source,
        }
    }
}
impl From<syntax::ModuleBody> for ModuleBody {
    fn from(value: syntax::ModuleBody) -> Self {
        match value {
            syntax::ModuleBody::Inline(field0) => {
                ModuleBody::Inline(field0.into_iter().map(|item0| item0.into()).collect())
            }
            syntax::ModuleBody::External => ModuleBody::External,
        }
    }
}
impl From<syntax::ModuleItem> for ModuleItem {
    fn from(value: syntax::ModuleItem) -> Self {
        match value {
            syntax::ModuleItem::Error { name, message } => ModuleItem::Error {
                name: name.map(|item0| item0.into()),
                message,
            },
            syntax::ModuleItem::Definition {
                owner,
                name,
                binders,
                ty,
                body,
            } => ModuleItem::Definition {
                owner: owner.map(|item0| item0.into()),
                name: name.into(),
                binders: binders.into_iter().map(|item0| item0.into()).collect(),
                ty: ty.into(),
                body: body.into(),
            },
            syntax::ModuleItem::Inductive {
                type_name,
                parameters,
                indices,
                kind,
                constructors,
            } => ModuleItem::Inductive {
                type_name: type_name.into(),
                parameters: parameters.into_iter().map(|item0| item0.into()).collect(),
                indices: indices.into_iter().map(|item0| item0.into()).collect(),
                kind,
                constructors: constructors
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1, item1_2) = item0;
                        (
                            item1_0.into(),
                            item1_1.into_iter().map(|item2| item2.into()).collect(),
                            item1_2.into(),
                        )
                    })
                    .collect(),
            },
            syntax::ModuleItem::Record {
                type_name,
                parameters,
                kind,
                fields,
            } => ModuleItem::Record {
                type_name: type_name.into(),
                parameters: parameters.into_iter().map(|item0| item0.into()).collect(),
                kind,
                fields: fields
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1) = item0;
                        (item1_0.into(), item1_1.into())
                    })
                    .collect(),
            },
            syntax::ModuleItem::ChildModule { module } => ModuleItem::ChildModule {
                module: Box::new((*module).into()),
            },
            syntax::ModuleItem::Import { path, import_name } => ModuleItem::Import {
                path: path.into(),
                import_name: import_name.into(),
            },
            syntax::ModuleItem::MathMacro {
                name,
                before,
                after,
            } => ModuleItem::MathMacro {
                name: name.into(),
                before: before.into_iter().map(|item0| item0.into()).collect(),
                after: after.into(),
            },
            syntax::ModuleItem::UserMacro {
                name,
                before,
                after,
            } => ModuleItem::UserMacro {
                name: name.into(),
                before: before.into_iter().map(|item0| item0.into()).collect(),
                after: after.into(),
            },
            syntax::ModuleItem::UseMacro {
                import_name,
                macro_name,
            } => ModuleItem::UseMacro {
                import_name: import_name.into(),
                macro_name: macro_name.into(),
            },
            syntax::ModuleItem::Eval { exp } => ModuleItem::Eval { exp: exp.into() },
            syntax::ModuleItem::Normalize { exp } => ModuleItem::Normalize { exp: exp.into() },
            syntax::ModuleItem::ComputationEval { exp } => {
                ModuleItem::ComputationEval { exp: exp.into() }
            }
            syntax::ModuleItem::ComputationNormalize { exp } => {
                ModuleItem::ComputationNormalize { exp: exp.into() }
            }
            syntax::ModuleItem::ValueCheck { exp, ty } => ModuleItem::ValueCheck {
                exp: exp.into(),
                ty: ty.into(),
            },
            syntax::ModuleItem::ComputationCheck { exp, ty } => ModuleItem::ComputationCheck {
                exp: exp.into(),
                ty: ty.into(),
            },
            syntax::ModuleItem::ValueInfer { exp } => ModuleItem::ValueInfer { exp: exp.into() },
            syntax::ModuleItem::ComputationInfer { exp } => {
                ModuleItem::ComputationInfer { exp: exp.into() }
            }
            syntax::ModuleItem::Check { exp, ty } => ModuleItem::Check {
                exp: exp.into(),
                ty: ty.into(),
            },
            syntax::ModuleItem::Infer { exp } => ModuleItem::Infer { exp: exp.into() },
        }
    }
}
impl From<syntax::AssociatedOwner> for AssociatedOwner {
    fn from(value: syntax::AssociatedOwner) -> Self {
        Self {
            type_name: value.type_name.into(),
            parameters: value
                .parameters
                .into_iter()
                .map(|item0| item0.into())
                .collect(),
        }
    }
}
impl From<syntax::ModuleInstantiatePath> for ModuleInstantiatePath {
    fn from(value: syntax::ModuleInstantiatePath) -> Self {
        match value {
            syntax::ModuleInstantiatePath::FromPackage { package, calls } => {
                ModuleInstantiatePath::FromPackage {
                    package: package.into(),
                    calls: calls
                        .into_iter()
                        .map(|item0| {
                            let (item1_0, item1_1) = item0;
                            (
                                item1_0.into(),
                                item1_1
                                    .into_iter()
                                    .map(|item2| {
                                        let (item3_0, item3_1) = item2;
                                        (item3_0.into(), item3_1.into())
                                    })
                                    .collect(),
                            )
                        })
                        .collect(),
                }
            }
            syntax::ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                ModuleInstantiatePath::FromCurrent {
                    back_parent,
                    calls: calls
                        .into_iter()
                        .map(|item0| {
                            let (item1_0, item1_1) = item0;
                            (
                                item1_0.into(),
                                item1_1
                                    .into_iter()
                                    .map(|item2| {
                                        let (item3_0, item3_1) = item2;
                                        (item3_0.into(), item3_1.into())
                                    })
                                    .collect(),
                            )
                        })
                        .collect(),
                }
            }
            syntax::ModuleInstantiatePath::FromRoot { calls } => ModuleInstantiatePath::FromRoot {
                calls: calls
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1) = item0;
                        (
                            item1_0.into(),
                            item1_1
                                .into_iter()
                                .map(|item2| {
                                    let (item3_0, item3_1) = item2;
                                    (item3_0.into(), item3_1.into())
                                })
                                .collect(),
                        )
                    })
                    .collect(),
            },
            syntax::ModuleInstantiatePath::FromImport { import_name, calls } => {
                ModuleInstantiatePath::FromImport {
                    import_name: import_name.into(),
                    calls: calls
                        .into_iter()
                        .map(|item0| {
                            let (item1_0, item1_1) = item0;
                            (
                                item1_0.into(),
                                item1_1
                                    .into_iter()
                                    .map(|item2| {
                                        let (item3_0, item3_1) = item2;
                                        (item3_0.into(), item3_1.into())
                                    })
                                    .collect(),
                            )
                        })
                        .collect(),
                }
            }
        }
    }
}
impl From<syntax::MacroExp> for MacroExp {
    fn from(value: syntax::MacroExp) -> Self {
        match value {
            syntax::MacroExp::RawExp(field0) => MacroExp::RawExp(field0.into()),
            syntax::MacroExp::TemplateName(field0) => MacroExp::TemplateName(field0.into()),
            syntax::MacroExp::TokenParameter(field0) => MacroExp::TokenParameter(field0.into()),
            syntax::MacroExp::Splice(field0) => MacroExp::Splice(field0.into()),
            syntax::MacroExp::Tok(field0) => MacroExp::Tok(field0),
            syntax::MacroExp::Quoted(field0) => MacroExp::Quoted(field0),
            syntax::MacroExp::Seq(field0) => {
                MacroExp::Seq(field0.into_iter().map(|item0| item0.into()).collect())
            }
        }
    }
}
impl From<syntax::RightBind> for RightBind {
    fn from(value: syntax::RightBind) -> Self {
        Self {
            vars: value.vars.into_iter().map(|item0| item0.into()).collect(),
            ty: Box::new((*value.ty).into()),
        }
    }
}
impl From<syntax::ValueTypeExp> for ValueTypeExp {
    fn from(value: syntax::ValueTypeExp) -> Self {
        let origin = value.source.map(|source| source.id);
        let kind = match value.kind {
            syntax::ValueTypeExpKind::Meta { kind, token } => ValueTypeExpKind::Meta {
                kind: kind.into(),
                token: Some(token.id),
            },
            syntax::ValueTypeExpKind::Access { access, parameters } => ValueTypeExpKind::Access {
                access: access.into(),
                parameters: parameters.into_iter().map(|item0| item0.into()).collect(),
            },
            syntax::ValueTypeExpKind::Thunk(field0) => {
                ValueTypeExpKind::Thunk(Box::new((*field0).into()))
            }
            syntax::ValueTypeExpKind::RunStep {
                state_ty,
                result_ty,
            } => ValueTypeExpKind::RunStep {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
            },
        };
        Self { kind, origin }
    }
}
impl From<syntax::ComputationTypeExp> for ComputationTypeExp {
    fn from(value: syntax::ComputationTypeExp) -> Self {
        let origin = value.source.map(|source| source.id);
        let kind = match value.kind {
            syntax::ComputationTypeExpKind::Meta { kind, token } => ComputationTypeExpKind::Meta {
                kind: kind.into(),
                token: Some(token.id),
            },
            syntax::ComputationTypeExpKind::Return(field0) => {
                ComputationTypeExpKind::Return(Box::new((*field0).into()))
            }
            syntax::ComputationTypeExpKind::Function { domain, codomain } => {
                ComputationTypeExpKind::Function {
                    domain: Box::new((*domain).into()),
                    codomain: Box::new((*codomain).into()),
                }
            }
        };
        Self { kind, origin }
    }
}
impl From<syntax::ValueTermExp> for ValueTermExp {
    fn from(value: syntax::ValueTermExp) -> Self {
        let origin = value.source.map(|source| source.id);
        let kind = match value.kind {
            syntax::ValueTermExpKind::Meta { kind, token } => ValueTermExpKind::Meta {
                kind: kind.into(),
                token: Some(token.id),
            },
            syntax::ValueTermExpKind::Access(field0) => ValueTermExpKind::Access(field0.into()),
            syntax::ValueTermExpKind::Record {
                datatype,
                parameters,
                fields,
            } => ValueTermExpKind::Record {
                datatype: datatype.into(),
                parameters: parameters.into_iter().map(|item0| item0.into()).collect(),
                fields: fields
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1) = item0;
                        (item1_0.into(), item1_1.into())
                    })
                    .collect(),
            },
            syntax::ValueTermExpKind::Constructor {
                datatype,
                constructor,
                parameters,
                fields,
            } => ValueTermExpKind::Constructor {
                datatype: datatype.into(),
                constructor: constructor.into(),
                parameters: parameters.into_iter().map(|item0| item0.into()).collect(),
                fields: fields.into_iter().map(|item0| item0.into()).collect(),
            },
            syntax::ValueTermExpKind::Thunk(field0) => {
                ValueTermExpKind::Thunk(Box::new((*field0).into()))
            }
            syntax::ValueTermExpKind::Continue {
                state_ty,
                result_ty,
                next,
            } => ValueTermExpKind::Continue {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                next: Box::new((*next).into()),
            },
            syntax::ValueTermExpKind::Finish {
                state_ty,
                result_ty,
                output,
            } => ValueTermExpKind::Finish {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                output: Box::new((*output).into()),
            },
        };
        Self { kind, origin }
    }
}
impl From<syntax::ComputationTermExp> for ComputationTermExp {
    fn from(value: syntax::ComputationTermExp) -> Self {
        let origin = value.source.map(|source| source.id);
        let kind = match value.kind {
            syntax::ComputationTermExpKind::Meta { kind, token } => ComputationTermExpKind::Meta {
                kind: kind.into(),
                token: Some(token.id),
            },
            syntax::ComputationTermExpKind::Access(field0) => {
                ComputationTermExpKind::Access(field0.into())
            }
            syntax::ComputationTermExpKind::Associated {
                datatype,
                item,
                parameters,
            } => ComputationTermExpKind::Associated {
                datatype: datatype.into(),
                item: item.into(),
                parameters: parameters.into_iter().map(|item0| item0.into()).collect(),
            },
            syntax::ComputationTermExpKind::InferredProjection { value, field } => {
                ComputationTermExpKind::InferredProjection {
                    value: Box::new((*value).into()),
                    field: field.into(),
                }
            }
            syntax::ComputationTermExpKind::Return(field0) => {
                ComputationTermExpKind::Return(Box::new((*field0).into()))
            }
            syntax::ComputationTermExpKind::Force(field0) => {
                ComputationTermExpKind::Force(Box::new((*field0).into()))
            }
            syntax::ComputationTermExpKind::Lambda {
                var,
                value_ty,
                body,
            } => ComputationTermExpKind::Lambda {
                var: var.into(),
                value_ty: Box::new((*value_ty).into()),
                body: Box::new((*body).into()),
            },
            syntax::ComputationTermExpKind::Application {
                function,
                arguments,
            } => ComputationTermExpKind::Application {
                function: function.into(),
                arguments: arguments.into_iter().map(|item0| item0.into()).collect(),
            },
            syntax::ComputationTermExpKind::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => ComputationTermExpKind::Sequence {
                computation: Box::new((*computation).into()),
                var: var.into(),
                value_ty: Box::new((*value_ty).into()),
                body: Box::new((*body).into()),
            },
            syntax::ComputationTermExpKind::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => ComputationTermExpKind::ValueLet {
                var: var.into(),
                value_ty: Box::new((*value_ty).into()),
                value: Box::new((*value).into()),
                body: Box::new((*body).into()),
            },
            syntax::ComputationTermExpKind::Case {
                datatype,
                scrutinee,
                branches,
            } => ComputationTermExpKind::Case {
                datatype: datatype.into(),
                scrutinee: Box::new((*scrutinee).into()),
                branches: branches
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1, item1_2) = item0;
                        (
                            item1_0.into(),
                            item1_1.into_iter().map(|item2| item2.into()).collect(),
                            item1_2.into(),
                        )
                    })
                    .collect(),
            },
            syntax::ComputationTermExpKind::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => ComputationTermExpKind::Run {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                initial: Box::new((*initial).into()),
                accessibility: Box::new((*accessibility).into()),
            },
            syntax::ComputationTermExpKind::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => ComputationTermExpKind::RunCase {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                initial: Box::new((*initial).into()),
                transition: Box::new((*transition).into()),
                accessibility: Box::new((*accessibility).into()),
                transition_equality: Box::new((*transition_equality).into()),
            },
        };
        Self { kind, origin }
    }
}
impl From<syntax::ProgramFunctionExp> for ProgramFunctionExp {
    fn from(value: syntax::ProgramFunctionExp) -> Self {
        let origin = value.source.map(|source| source.id);
        let kind = match value.kind {
            syntax::ProgramFunctionExpKind::Access(field0) => {
                ProgramFunctionExpKind::Access(field0.into())
            }
            syntax::ProgramFunctionExpKind::Associated {
                datatype,
                item,
                parameters,
            } => ProgramFunctionExpKind::Associated {
                datatype: datatype.into(),
                item: item.into(),
                parameters: parameters.into_iter().map(|item0| item0.into()).collect(),
            },
            syntax::ProgramFunctionExpKind::Value(field0) => {
                ProgramFunctionExpKind::Value(Box::new((*field0).into()))
            }
            syntax::ProgramFunctionExpKind::Computation(field0) => {
                ProgramFunctionExpKind::Computation(Box::new((*field0).into()))
            }
        };
        Self { kind, origin }
    }
}
impl From<syntax::Bind> for Bind {
    fn from(value: syntax::Bind) -> Self {
        match value {
            syntax::Bind::Named(field0) => Bind::Named(field0.into()),
            syntax::Bind::Subset { var, ty, predicate } => Bind::Subset {
                var: var.into(),
                ty: Box::new((*ty).into()),
                predicate: Box::new((*predicate).into()),
            },
            syntax::Bind::SubsetWithProof {
                var,
                ty,
                predicate,
                proof_var,
            } => Bind::SubsetWithProof {
                var: var.into(),
                ty: Box::new((*ty).into()),
                predicate: Box::new((*predicate).into()),
                proof_var: proof_var.into(),
            },
        }
    }
}
impl From<syntax::LocalAccess> for LocalAccess {
    fn from(value: syntax::LocalAccess) -> Self {
        match value {
            syntax::LocalAccess::Current { access } => LocalAccess::Current {
                access: access.into(),
            },
            syntax::LocalAccess::Named { access, child } => LocalAccess::Named {
                access: access.into(),
                child: child.into(),
            },
        }
    }
}
impl From<syntax::SExp> for SExp {
    fn from(value: syntax::SExp) -> Self {
        let origin = value.source.map(|source| source.id);
        let kind = match value.kind {
            syntax::SExpKind::Meta { kind, token } => SExpKind::Meta {
                kind: kind.into(),
                token: Some(token.id),
            },
            syntax::SExpKind::AccessPath { access, parameters } => SExpKind::AccessPath {
                access: access.into(),
                parameters: parameters.into_iter().map(|item0| item0.into()).collect(),
            },
            syntax::SExpKind::AssociatedAccess { base, field } => SExpKind::AssociatedAccess {
                base: Box::new((*base).into()),
                field: field.into(),
            },
            syntax::SExpKind::InferredProjection { value, field } => SExpKind::InferredProjection {
                value: Box::new((*value).into()),
                field: field.into(),
            },
            syntax::SExpKind::MathMacro { tokens } => SExpKind::MathMacro {
                tokens: tokens.into_iter().map(|item0| item0.into()).collect(),
                scope: None,
                depth: 0,
                max_order: None,
            },
            syntax::SExpKind::NamedMacro { name, tokens } => SExpKind::NamedMacro {
                name: name.into(),
                tokens: tokens.into_iter().map(|item0| item0.into()).collect(),
                scope: None,
                depth: 0,
                max_order: None,
            },
            syntax::SExpKind::MacroParameter(field0) => SExpKind::MacroParameter(field0.into()),
            syntax::SExpKind::TokenMatch { target, branches } => SExpKind::TokenMatch {
                target: target.into(),
                branches: branches
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1) = item0;
                        (item1_0.into(), item1_1.into())
                    })
                    .collect(),
            },
            syntax::SExpKind::Where { exp, clauses } => SExpKind::Where {
                exp: Box::new((*exp).into()),
                clauses: clauses
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1, item1_2) = item0;
                        (item1_0.into(), item1_1.into(), item1_2.into())
                    })
                    .collect(),
            },
            syntax::SExpKind::Sort(field0) => SExpKind::Sort(field0),
            syntax::SExpKind::ValueType => SExpKind::ValueType,
            syntax::SExpKind::Prod { bind, body } => SExpKind::Prod {
                bind: bind.into(),
                body: Box::new((*body).into()),
            },
            syntax::SExpKind::Lam { bind, body } => SExpKind::Lam {
                bind: bind.into(),
                body: Box::new((*body).into()),
            },
            syntax::SExpKind::App { func, arg } => SExpKind::App {
                func: Box::new((*func).into()),
                arg: Box::new((*arg).into()),
            },
            syntax::SExpKind::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => SExpKind::SubsetIntro {
                superset: Box::new((*superset).into()),
                subset: Box::new((*subset).into()),
                element: Box::new((*element).into()),
                proof: Box::new((*proof).into()),
            },
            syntax::SExpKind::IndCase {
                path,
                scrutinee,
                return_type,
                branches,
            } => SExpKind::IndCase {
                path: path.into(),
                scrutinee: Box::new((*scrutinee).into()),
                return_type: Box::new((*return_type).into()),
                branches: branches
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1) = item0;
                        (item1_0.into(), item1_1.into())
                    })
                    .collect(),
            },
            syntax::SExpKind::Induction {
                binder,
                return_type,
                cases,
            } => SExpKind::Induction {
                binder: binder.into(),
                return_type: Box::new((*return_type).into()),
                cases: cases
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1) = item0;
                        (item1_0.into(), item1_1.into())
                    })
                    .collect(),
            },
            syntax::SExpKind::IndElimPrim {
                path,
                parameters,
                motive,
            } => SExpKind::IndElimPrim {
                path: path.into(),
                parameters: parameters.into_iter().map(|item0| item0.into()).collect(),
                motive: Box::new((*motive).into()),
            },
            syntax::SExpKind::ThunkType { computation_ty } => SExpKind::ThunkType {
                computation_ty: Box::new((*computation_ty).into()),
            },
            syntax::SExpKind::ReturnType { value_ty } => SExpKind::ReturnType {
                value_ty: Box::new((*value_ty).into()),
            },
            syntax::SExpKind::ComputationFunction { domain, codomain } => {
                SExpKind::ComputationFunction {
                    domain: Box::new((*domain).into()),
                    codomain: Box::new((*codomain).into()),
                }
            }
            syntax::SExpKind::Thunk { computation } => SExpKind::Thunk {
                computation: Box::new((*computation).into()),
            },
            syntax::SExpKind::Return { value } => SExpKind::Return {
                value: Box::new((*value).into()),
            },
            syntax::SExpKind::Force { value } => SExpKind::Force {
                value: Box::new((*value).into()),
            },
            syntax::SExpKind::ComputationLam {
                var,
                value_ty,
                body,
            } => SExpKind::ComputationLam {
                var: var.into(),
                value_ty: Box::new((*value_ty).into()),
                body: Box::new((*body).into()),
            },
            syntax::SExpKind::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => SExpKind::Sequence {
                computation: Box::new((*computation).into()),
                var: var.into(),
                value_ty: Box::new((*value_ty).into()),
                body: Box::new((*body).into()),
            },
            syntax::SExpKind::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => SExpKind::ValueLet {
                var: var.into(),
                value_ty: Box::new((*value_ty).into()),
                value: Box::new((*value).into()),
                body: Box::new((*body).into()),
            },
            syntax::SExpKind::ProgramCase {
                path,
                scrutinee,
                branches,
            } => SExpKind::ProgramCase {
                path: path.into(),
                scrutinee: Box::new((*scrutinee).into()),
                branches: branches
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1, item1_2) = item0;
                        (
                            item1_0.into(),
                            item1_1.into_iter().map(|item2| item2.into()).collect(),
                            item1_2.into(),
                        )
                    })
                    .collect(),
            },
            syntax::SExpKind::RunStep {
                state_ty,
                result_ty,
            } => SExpKind::RunStep {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
            },
            syntax::SExpKind::Continue {
                state_ty,
                result_ty,
                next,
            } => SExpKind::Continue {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                next: Box::new((*next).into()),
            },
            syntax::SExpKind::Finish {
                state_ty,
                result_ty,
                output,
            } => SExpKind::Finish {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                output: Box::new((*output).into()),
            },
            syntax::SExpKind::Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => SExpKind::Acc {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                state: Box::new((*state).into()),
            },
            syntax::SExpKind::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => SExpKind::Run {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                initial: Box::new((*initial).into()),
                accessibility: Box::new((*accessibility).into()),
            },
            syntax::SExpKind::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => SExpKind::RunCase {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                initial: Box::new((*initial).into()),
                transition: Box::new((*transition).into()),
                accessibility: Box::new((*accessibility).into()),
                transition_equality: Box::new((*transition_equality).into()),
            },
            syntax::SExpKind::RunStepRec {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => SExpKind::RunStepRec {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                motive: Box::new((*motive).into()),
                on_continue: Box::new((*on_continue).into()),
                on_finish: Box::new((*on_finish).into()),
                scrutinee: Box::new((*scrutinee).into()),
            },
            syntax::SExpKind::BoxType { program_ty } => SExpKind::BoxType {
                program_ty: Box::new((*program_ty).into()),
            },
            syntax::SExpKind::BoxProgram {
                program_ty,
                program,
            } => SExpKind::BoxProgram {
                program_ty: Box::new((*program_ty).into()),
                program: Box::new((*program).into()),
            },
            syntax::SExpKind::ForceBox { program_ty, boxed } => SExpKind::ForceBox {
                program_ty: Box::new((*program_ty).into()),
                boxed: Box::new((*boxed).into()),
            },
            syntax::SExpKind::BoxApp { function, argument } => SExpKind::BoxApp {
                function: Box::new((*function).into()),
                argument: Box::new((*argument).into()),
            },
            syntax::SExpKind::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
            } => SExpKind::AccIntro {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                state: Box::new((*state).into()),
                predecessors: Box::new((*predecessors).into()),
            },
            syntax::SExpKind::AccDescent {
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
            } => SExpKind::AccDescent {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                from: Box::new((*from).into()),
                to: Box::new((*to).into()),
                accessibility: Box::new((*accessibility).into()),
                transition: Box::new((*transition).into()),
            },
            syntax::SExpKind::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => SExpKind::RecordTypeCtor {
                access: access.into(),
                parameters: parameters.into_iter().map(|item0| item0.into()).collect(),
                fields: fields
                    .into_iter()
                    .map(|item0| {
                        let (item1_0, item1_1) = item0;
                        (item1_0.into(), item1_1.into())
                    })
                    .collect(),
            },
            syntax::SExpKind::PowerSet { set } => SExpKind::PowerSet {
                set: Box::new((*set).into()),
            },
            syntax::SExpKind::SubSet {
                var,
                set,
                predicate,
            } => SExpKind::SubSet {
                var: var.into(),
                set: Box::new((*set).into()),
                predicate: Box::new((*predicate).into()),
            },
            syntax::SExpKind::Pred {
                superset,
                subset,
                element,
            } => SExpKind::Pred {
                superset: Box::new((*superset).into()),
                subset: Box::new((*subset).into()),
                element: Box::new((*element).into()),
            },
            syntax::SExpKind::TypeLift { superset, subset } => SExpKind::TypeLift {
                superset: Box::new((*superset).into()),
                subset: Box::new((*subset).into()),
            },
            syntax::SExpKind::Equal { left, right } => SExpKind::Equal {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
            },
            syntax::SExpKind::Exists { bind } => SExpKind::Exists { bind: bind.into() },
            syntax::SExpKind::TakeSet {
                bind,
                body,
                existence,
                uniqueness,
            } => SExpKind::TakeSet {
                bind: bind.into(),
                body: Box::new((*body).into()),
                existence: Box::new((*existence).into()),
                uniqueness: Box::new((*uniqueness).into()),
            },
            syntax::SExpKind::TakeProp {
                bind,
                body,
                existence,
            } => SExpKind::TakeProp {
                bind: bind.into(),
                body: Box::new((*body).into()),
                existence: Box::new((*existence).into()),
            },
            syntax::SExpKind::ExistsIntro { element, set } => SExpKind::ExistsIntro {
                element: Box::new((*element).into()),
                set: Box::new((*set).into()),
            },
            syntax::SExpKind::SubsetElim {
                element,
                subset,
                superset,
            } => SExpKind::SubsetElim {
                element: Box::new((*element).into()),
                subset: Box::new((*subset).into()),
                superset: Box::new((*superset).into()),
            },
            syntax::SExpKind::IdRefl { element } => SExpKind::IdRefl {
                element: Box::new((*element).into()),
            },
            syntax::SExpKind::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
                base,
                equality,
            } => SExpKind::IdElim {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
                var: var.into(),
                ty: Box::new((*ty).into()),
                predicate: Box::new((*predicate).into()),
                base: Box::new((*base).into()),
                equality: Box::new((*equality).into()),
            },
            syntax::SExpKind::AxiomSetExt {
                left,
                right,
                left_to_right,
                right_to_left,
            } => SExpKind::AxiomSetExt {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
                left_to_right: Box::new((*left_to_right).into()),
                right_to_left: Box::new((*right_to_left).into()),
            },
            syntax::SExpKind::AxiomFunExt {
                left,
                right,
                pointwise,
            } => SExpKind::AxiomFunExt {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
                pointwise: Box::new((*pointwise).into()),
            },
            syntax::SExpKind::AxiomClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            } => SExpKind::AxiomClassicalIndefiniteChoice {
                domain: Box::new((*domain).into()),
                family: Box::new((*family).into()),
                inhabited: Box::new((*inhabited).into()),
            },
            syntax::SExpKind::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
            } => SExpKind::TakeEq {
                func: Box::new((*func).into()),
                domain: Box::new((*domain).into()),
                codomain: Box::new((*codomain).into()),
                element: Box::new((*element).into()),
                existence: Box::new((*existence).into()),
                uniqueness: Box::new((*uniqueness).into()),
            },
            syntax::SExpKind::Block(field0) => SExpKind::Block(field0.into()),
            syntax::SExpKind::Program(field0) => SExpKind::Program(field0.into()),
        };
        Self { kind, origin }
    }
}
impl From<syntax::Block> for Block {
    fn from(value: syntax::Block) -> Self {
        Self {
            statements: value
                .statements
                .into_iter()
                .map(|item0| item0.into())
                .collect(),
            result: Box::new((*value.result).into()),
        }
    }
}
impl From<syntax::Statement> for Statement {
    fn from(value: syntax::Statement) -> Self {
        match value {
            syntax::Statement::Fix(field0) => {
                Statement::Fix(field0.into_iter().map(|item0| item0.into()).collect())
            }
            syntax::Statement::Let { var, ty, body } => Statement::Let {
                var: var.into(),
                ty: ty.into(),
                body: body.into(),
            },
            syntax::Statement::Bind {
                var,
                ty,
                computation,
            } => Statement::Bind {
                var: var.into(),
                ty: ty.into(),
                computation: computation.into(),
            },
            syntax::Statement::Sufficient { map, map_ty } => Statement::Sufficient {
                map: map.into(),
                map_ty: map_ty.into(),
            },
            syntax::Statement::TakeFrom { var, ty, existence } => Statement::TakeFrom {
                var: var.into(),
                ty: ty.into(),
                existence: existence.into(),
            },
        }
    }
}
