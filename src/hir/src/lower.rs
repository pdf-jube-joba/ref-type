//! Lower parsed syntax to independent HIR, preserving source locations and proof structure.
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
            name: value.name,
            parameters: value.parameters.into_iter().map(Into::into).collect(),
            body: value.body.into(),
            span: value.span,
            declaration_spans: value.declaration_spans,
            source: value.source,
            header_source: value.header_source,
        }
    }
}

impl From<syntax::ModuleBody> for ModuleBody {
    fn from(value: syntax::ModuleBody) -> Self {
        match value {
            syntax::ModuleBody::Inline(v0) => {
                Self::Inline(v0.into_iter().map(Into::into).collect())
            }
            syntax::ModuleBody::External => Self::External,
        }
    }
}

impl From<syntax::ModuleItem> for ModuleItem {
    fn from(value: syntax::ModuleItem) -> Self {
        match value {
            syntax::ModuleItem::Error { name, message } => Self::Error { name, message },
            syntax::ModuleItem::Definition {
                owner,
                name,
                binders,
                ty,
                body,
            } => Self::Definition {
                owner: owner.map(Into::into),
                name,
                binders: binders.into_iter().map(Into::into).collect(),
                ty: ty.into(),
                body: body.into(),
            },
            syntax::ModuleItem::Inductive {
                type_name,
                parameters,
                indices,
                kind,
                constructors,
            } => Self::Inductive {
                type_name,
                parameters: parameters.into_iter().map(Into::into).collect(),
                indices: indices.into_iter().map(Into::into).collect(),
                kind,
                constructors: constructors
                    .into_iter()
                    .map(|value| {
                        let (name, binders, result) = value;
                        (
                            name,
                            binders.into_iter().map(Into::into).collect(),
                            result.into(),
                        )
                    })
                    .collect(),
            },
            syntax::ModuleItem::Record {
                type_name,
                parameters,
                kind,
                fields,
            } => Self::Record {
                type_name,
                parameters: parameters.into_iter().map(Into::into).collect(),
                kind,
                fields: fields
                    .into_iter()
                    .map(|(name, value)| (name, value.into()))
                    .collect(),
            },
            syntax::ModuleItem::ChildModule { module } => Self::ChildModule {
                module: Box::new((*module).into()),
            },
            syntax::ModuleItem::Import { path, import_name } => Self::Import {
                path: path.into(),
                import_name,
            },
            syntax::ModuleItem::MathMacro {
                name,
                before,
                after,
            } => Self::MathMacro {
                name,
                before,
                after: after.into(),
            },
            syntax::ModuleItem::UserMacro {
                name,
                before,
                after,
            } => Self::UserMacro {
                name,
                before,
                after: after.into(),
            },
            syntax::ModuleItem::UseMacro {
                import_name,
                macro_name,
            } => Self::UseMacro {
                import_name,
                macro_name,
            },
            syntax::ModuleItem::Eval { exp } => Self::Eval { exp: exp.into() },
            syntax::ModuleItem::Normalize { exp } => Self::Normalize { exp: exp.into() },
            syntax::ModuleItem::ComputationEval { exp } => {
                Self::ComputationEval { exp: exp.into() }
            }
            syntax::ModuleItem::ComputationNormalize { exp } => {
                Self::ComputationNormalize { exp: exp.into() }
            }
            syntax::ModuleItem::ValueCheck { exp, ty } => Self::ValueCheck {
                exp: exp.into(),
                ty: ty.into(),
            },
            syntax::ModuleItem::ComputationCheck { exp, ty } => Self::ComputationCheck {
                exp: exp.into(),
                ty: ty.into(),
            },
            syntax::ModuleItem::ValueInfer { exp } => Self::ValueInfer { exp: exp.into() },
            syntax::ModuleItem::ComputationInfer { exp } => {
                Self::ComputationInfer { exp: exp.into() }
            }
            syntax::ModuleItem::Check { exp, ty } => Self::Check {
                exp: exp.into(),
                ty: ty.into(),
            },
            syntax::ModuleItem::Infer { exp } => Self::Infer { exp: exp.into() },
        }
    }
}

impl From<syntax::AssociatedOwner> for AssociatedOwner {
    fn from(value: syntax::AssociatedOwner) -> Self {
        Self {
            type_name: value.type_name,
            parameters: value.parameters.into_iter().map(Into::into).collect(),
        }
    }
}

type ModuleCalls<E> = Vec<(Identifier, Vec<(Identifier, E)>)>;

fn lower_module_calls(calls: ModuleCalls<syntax::SExp>) -> ModuleCalls<SExp> {
    calls
        .into_iter()
        .map(|(module, arguments)| {
            let arguments = arguments
                .into_iter()
                .map(|(name, value)| (name, value.into()))
                .collect();
            (module, arguments)
        })
        .collect()
}

impl From<syntax::ModuleInstantiatePath> for ModuleInstantiatePath {
    fn from(value: syntax::ModuleInstantiatePath) -> Self {
        match value {
            syntax::ModuleInstantiatePath::FromPackage { package, calls } => Self::FromPackage {
                package,
                calls: lower_module_calls(calls),
            },
            syntax::ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                Self::FromCurrent {
                    back_parent,
                    calls: lower_module_calls(calls),
                }
            }
            syntax::ModuleInstantiatePath::FromRoot { calls } => Self::FromRoot {
                calls: lower_module_calls(calls),
            },
            syntax::ModuleInstantiatePath::FromImport { import_name, calls } => Self::FromImport {
                import_name,
                calls: lower_module_calls(calls),
            },
        }
    }
}

impl From<syntax::MacroExp> for MacroExp {
    fn from(value: syntax::MacroExp) -> Self {
        match value {
            syntax::MacroExp::RawExp(v0) => Self::RawExp(v0.into()),
            syntax::MacroExp::TemplateName(v0) => Self::TemplateName(v0),
            syntax::MacroExp::TokenParameter(v0) => Self::TokenParameter(v0),
            syntax::MacroExp::Splice(v0) => Self::Splice(v0),
            syntax::MacroExp::Tok(v0) => Self::Tok(v0),
            syntax::MacroExp::Quoted(v0) => Self::Quoted(v0),
            syntax::MacroExp::Seq(v0) => Self::Seq(v0.into_iter().map(Into::into).collect()),
        }
    }
}

impl From<syntax::RightBind> for RightBind {
    fn from(value: syntax::RightBind) -> Self {
        Self {
            vars: value.vars,
            ty: Box::new((*value.ty).into()),
        }
    }
}

impl From<syntax::ValueTypeExp> for ValueTypeExp {
    fn from(value: syntax::ValueTypeExp) -> Self {
        match value {
            syntax::ValueTypeExp::Meta { kind, span } => Self::Meta {
                kind: kind.into(),
                span,
            },
            syntax::ValueTypeExp::Access { access, parameters } => Self::Access {
                access: access.into(),
                parameters: parameters.into_iter().map(Into::into).collect(),
            },
            syntax::ValueTypeExp::Thunk(v0) => Self::Thunk(Box::new((*v0).into())),
            syntax::ValueTypeExp::RunStep {
                state_ty,
                result_ty,
            } => Self::RunStep {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
            },
        }
    }
}

impl From<syntax::ComputationTypeExp> for ComputationTypeExp {
    fn from(value: syntax::ComputationTypeExp) -> Self {
        match value {
            syntax::ComputationTypeExp::Meta { kind, span } => Self::Meta {
                kind: kind.into(),
                span,
            },
            syntax::ComputationTypeExp::Return(v0) => Self::Return(Box::new((*v0).into())),
            syntax::ComputationTypeExp::Function { domain, codomain } => Self::Function {
                domain: Box::new((*domain).into()),
                codomain: Box::new((*codomain).into()),
            },
        }
    }
}

impl From<syntax::ValueTermExp> for ValueTermExp {
    fn from(value: syntax::ValueTermExp) -> Self {
        match value {
            syntax::ValueTermExp::Meta { kind, span } => Self::Meta {
                kind: kind.into(),
                span,
            },
            syntax::ValueTermExp::Access(v0) => Self::Access(v0.into()),
            syntax::ValueTermExp::Record {
                datatype,
                parameters,
                fields,
            } => Self::Record {
                datatype: datatype.into(),
                parameters: parameters.into_iter().map(Into::into).collect(),
                fields: fields
                    .into_iter()
                    .map(|(name, value)| (name, value.into()))
                    .collect(),
            },
            syntax::ValueTermExp::Constructor {
                datatype,
                constructor,
                parameters,
                fields,
            } => Self::Constructor {
                datatype: datatype.into(),
                constructor,
                parameters: parameters.into_iter().map(Into::into).collect(),
                fields: fields.into_iter().map(Into::into).collect(),
            },
            syntax::ValueTermExp::Thunk(v0) => Self::Thunk(Box::new((*v0).into())),
            syntax::ValueTermExp::Continue {
                state_ty,
                result_ty,
                next,
            } => Self::Continue {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                next: Box::new((*next).into()),
            },
            syntax::ValueTermExp::Finish {
                state_ty,
                result_ty,
                output,
            } => Self::Finish {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                output: Box::new((*output).into()),
            },
        }
    }
}

impl From<syntax::ComputationTermExp> for ComputationTermExp {
    fn from(value: syntax::ComputationTermExp) -> Self {
        match value {
            syntax::ComputationTermExp::Meta { kind, span } => Self::Meta {
                kind: kind.into(),
                span,
            },
            syntax::ComputationTermExp::Access(v0) => Self::Access(v0.into()),
            syntax::ComputationTermExp::Associated {
                datatype,
                item,
                parameters,
            } => Self::Associated {
                datatype: datatype.into(),
                item,
                parameters: parameters.into_iter().map(Into::into).collect(),
            },
            syntax::ComputationTermExp::InferredProjection { value, field } => {
                Self::InferredProjection {
                    value: Box::new((*value).into()),
                    field,
                }
            }
            syntax::ComputationTermExp::Return(v0) => Self::Return(Box::new((*v0).into())),
            syntax::ComputationTermExp::Force(v0) => Self::Force(Box::new((*v0).into())),
            syntax::ComputationTermExp::Lambda {
                var,
                value_ty,
                body,
            } => Self::Lambda {
                var,
                value_ty: Box::new((*value_ty).into()),
                body: Box::new((*body).into()),
            },
            syntax::ComputationTermExp::Application {
                function,
                arguments,
            } => Self::Application {
                function: function.into(),
                arguments: arguments.into_iter().map(Into::into).collect(),
            },
            syntax::ComputationTermExp::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => Self::Sequence {
                computation: Box::new((*computation).into()),
                var,
                value_ty: Box::new((*value_ty).into()),
                body: Box::new((*body).into()),
            },
            syntax::ComputationTermExp::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => Self::ValueLet {
                var,
                value_ty: Box::new((*value_ty).into()),
                value: Box::new((*value).into()),
                body: Box::new((*body).into()),
            },
            syntax::ComputationTermExp::Case {
                datatype,
                scrutinee,
                branches,
            } => Self::Case {
                datatype: datatype.into(),
                scrutinee: Box::new((*scrutinee).into()),
                branches: branches
                    .into_iter()
                    .map(|value| {
                        let (v0, v1, v2) = value;
                        (v0, v1, v2.into())
                    })
                    .collect(),
            },
            syntax::ComputationTermExp::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => Self::Run {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                initial: Box::new((*initial).into()),
                accessibility: Box::new((*accessibility).into()),
            },
            syntax::ComputationTermExp::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => Self::RunCase {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                initial: Box::new((*initial).into()),
                transition: Box::new((*transition).into()),
                accessibility: Box::new((*accessibility).into()),
                transition_equality: Box::new((*transition_equality).into()),
            },
        }
    }
}

impl From<syntax::ProgramFunctionExp> for ProgramFunctionExp {
    fn from(value: syntax::ProgramFunctionExp) -> Self {
        match value {
            syntax::ProgramFunctionExp::Access(v0) => Self::Access(v0.into()),
            syntax::ProgramFunctionExp::Associated {
                datatype,
                item,
                parameters,
            } => Self::Associated {
                datatype: datatype.into(),
                item,
                parameters: parameters.into_iter().map(Into::into).collect(),
            },
            syntax::ProgramFunctionExp::Value(v0) => Self::Value(Box::new((*v0).into())),
            syntax::ProgramFunctionExp::Computation(v0) => {
                Self::Computation(Box::new((*v0).into()))
            }
        }
    }
}

impl From<syntax::Bind> for Bind {
    fn from(value: syntax::Bind) -> Self {
        match value {
            syntax::Bind::Named(v0) => Self::Named(v0.into()),
            syntax::Bind::Subset { var, ty, predicate } => Self::Subset {
                var,
                ty: Box::new((*ty).into()),
                predicate: Box::new((*predicate).into()),
            },
            syntax::Bind::SubsetWithProof {
                var,
                ty,
                predicate,
                proof_var,
            } => Self::SubsetWithProof {
                var,
                ty: Box::new((*ty).into()),
                predicate: Box::new((*predicate).into()),
                proof_var,
            },
        }
    }
}

impl From<syntax::LocalAccess> for LocalAccess {
    fn from(value: syntax::LocalAccess) -> Self {
        match value {
            syntax::LocalAccess::Current { access } => Self::Current { access },
            syntax::LocalAccess::Named { access, child } => Self::Named { access, child },
        }
    }
}

impl From<syntax::SExp> for SExp {
    fn from(value: syntax::SExp) -> Self {
        match value {
            syntax::SExp::Meta { kind, span } => Self::Meta {
                kind: kind.into(),
                span,
            },
            syntax::SExp::AccessPath { access, parameters } => Self::AccessPath {
                access: access.into(),
                parameters: parameters.into_iter().map(Into::into).collect(),
            },
            syntax::SExp::AssociatedAccess { base, field } => Self::AssociatedAccess {
                base: Box::new((*base).into()),
                field,
            },
            syntax::SExp::InferredProjection { value, field } => Self::InferredProjection {
                value: Box::new((*value).into()),
                field,
            },
            syntax::SExp::MathMacro { tokens } => Self::MathMacro {
                tokens: tokens.into_iter().map(Into::into).collect(),
                scope: None,
                max_order: None,
                depth: 0,
            },
            syntax::SExp::NamedMacro { name, tokens } => Self::NamedMacro {
                name,
                tokens: tokens.into_iter().map(Into::into).collect(),
                scope: None,
                max_order: None,
                depth: 0,
            },
            syntax::SExp::MacroParameter(v0) => Self::MacroParameter(v0),
            syntax::SExp::TokenMatch { target, branches } => Self::TokenMatch {
                target,
                branches: branches
                    .into_iter()
                    .map(|(name, value)| (name, value.into()))
                    .collect(),
            },
            syntax::SExp::Where { exp, clauses } => Self::Where {
                exp: Box::new((*exp).into()),
                clauses: clauses
                    .into_iter()
                    .map(|value| {
                        let (v0, v1, v2) = value;
                        (v0, v1.into(), v2.into())
                    })
                    .collect(),
            },
            syntax::SExp::Sort(v0) => Self::Sort(v0),
            syntax::SExp::ValueType => Self::ValueType,
            syntax::SExp::Prod { bind, body } => Self::Prod {
                bind: bind.into(),
                body: Box::new((*body).into()),
            },
            syntax::SExp::Lam { bind, body } => Self::Lam {
                bind: bind.into(),
                body: Box::new((*body).into()),
            },
            syntax::SExp::App { func, arg } => Self::App {
                func: Box::new((*func).into()),
                arg: Box::new((*arg).into()),
            },
            syntax::SExp::SubsetIntro {
                superset,
                subset,
                element,
                proof,
            } => Self::SubsetIntro {
                superset: Box::new((*superset).into()),
                subset: Box::new((*subset).into()),
                element: Box::new((*element).into()),
                proof: Box::new((*proof).into()),
            },
            syntax::SExp::IndCase {
                path,
                scrutinee,
                return_type,
                branches,
            } => Self::IndCase {
                path: path.into(),
                scrutinee: Box::new((*scrutinee).into()),
                return_type: Box::new((*return_type).into()),
                branches: branches
                    .into_iter()
                    .map(|(name, value)| (name, value.into()))
                    .collect(),
            },
            syntax::SExp::Induction {
                binder,
                return_type,
                cases,
            } => Self::Induction {
                binder: binder.into(),
                return_type: Box::new((*return_type).into()),
                cases: cases
                    .into_iter()
                    .map(|(name, value)| (name, value.into()))
                    .collect(),
            },
            syntax::SExp::IndElimPrim {
                path,
                parameters,
                motive,
            } => Self::IndElimPrim {
                path: path.into(),
                parameters: parameters.into_iter().map(Into::into).collect(),
                motive: Box::new((*motive).into()),
            },
            syntax::SExp::ThunkType { computation_ty } => Self::ThunkType {
                computation_ty: Box::new((*computation_ty).into()),
            },
            syntax::SExp::ReturnType { value_ty } => Self::ReturnType {
                value_ty: Box::new((*value_ty).into()),
            },
            syntax::SExp::ComputationFunction { domain, codomain } => Self::ComputationFunction {
                domain: Box::new((*domain).into()),
                codomain: Box::new((*codomain).into()),
            },
            syntax::SExp::Thunk { computation } => Self::Thunk {
                computation: Box::new((*computation).into()),
            },
            syntax::SExp::Return { value } => Self::Return {
                value: Box::new((*value).into()),
            },
            syntax::SExp::Force { value } => Self::Force {
                value: Box::new((*value).into()),
            },
            syntax::SExp::ComputationLam {
                var,
                value_ty,
                body,
            } => Self::ComputationLam {
                var,
                value_ty: Box::new((*value_ty).into()),
                body: Box::new((*body).into()),
            },
            syntax::SExp::Sequence {
                computation,
                var,
                value_ty,
                body,
            } => Self::Sequence {
                computation: Box::new((*computation).into()),
                var,
                value_ty: Box::new((*value_ty).into()),
                body: Box::new((*body).into()),
            },
            syntax::SExp::ValueLet {
                var,
                value_ty,
                value,
                body,
            } => Self::ValueLet {
                var,
                value_ty: Box::new((*value_ty).into()),
                value: Box::new((*value).into()),
                body: Box::new((*body).into()),
            },
            syntax::SExp::ProgramCase {
                path,
                scrutinee,
                branches,
            } => Self::ProgramCase {
                path: path.into(),
                scrutinee: Box::new((*scrutinee).into()),
                branches: branches
                    .into_iter()
                    .map(|value| {
                        let (v0, v1, v2) = value;
                        (v0, v1, v2.into())
                    })
                    .collect(),
            },
            syntax::SExp::RunStep {
                state_ty,
                result_ty,
            } => Self::RunStep {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
            },
            syntax::SExp::Continue {
                state_ty,
                result_ty,
                next,
            } => Self::Continue {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                next: Box::new((*next).into()),
            },
            syntax::SExp::Finish {
                state_ty,
                result_ty,
                output,
            } => Self::Finish {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                output: Box::new((*output).into()),
            },
            syntax::SExp::Acc {
                state_ty,
                result_ty,
                step,
                state,
            } => Self::Acc {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                state: Box::new((*state).into()),
            },
            syntax::SExp::Run {
                state_ty,
                result_ty,
                step,
                initial,
                accessibility,
            } => Self::Run {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                initial: Box::new((*initial).into()),
                accessibility: Box::new((*accessibility).into()),
            },
            syntax::SExp::RunCase {
                state_ty,
                result_ty,
                step,
                initial,
                transition,
                accessibility,
                transition_equality,
            } => Self::RunCase {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                initial: Box::new((*initial).into()),
                transition: Box::new((*transition).into()),
                accessibility: Box::new((*accessibility).into()),
                transition_equality: Box::new((*transition_equality).into()),
            },
            syntax::SExp::RunStepRec {
                state_ty,
                result_ty,
                motive,
                on_continue,
                on_finish,
                scrutinee,
            } => Self::RunStepRec {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                motive: Box::new((*motive).into()),
                on_continue: Box::new((*on_continue).into()),
                on_finish: Box::new((*on_finish).into()),
                scrutinee: Box::new((*scrutinee).into()),
            },
            syntax::SExp::BoxType { program_ty } => Self::BoxType {
                program_ty: Box::new((*program_ty).into()),
            },
            syntax::SExp::BoxProgram {
                program_ty,
                program,
            } => Self::BoxProgram {
                program_ty: Box::new((*program_ty).into()),
                program: Box::new((*program).into()),
            },
            syntax::SExp::ForceBox { program_ty, boxed } => Self::ForceBox {
                program_ty: Box::new((*program_ty).into()),
                boxed: Box::new((*boxed).into()),
            },
            syntax::SExp::BoxApp { function, argument } => Self::BoxApp {
                function: Box::new((*function).into()),
                argument: Box::new((*argument).into()),
            },
            syntax::SExp::AccIntro {
                state_ty,
                result_ty,
                step,
                state,
                predecessors,
            } => Self::AccIntro {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                state: Box::new((*state).into()),
                predecessors: Box::new((*predecessors).into()),
            },
            syntax::SExp::AccDescent {
                state_ty,
                result_ty,
                step,
                from,
                to,
                accessibility,
                transition,
            } => Self::AccDescent {
                state_ty: Box::new((*state_ty).into()),
                result_ty: Box::new((*result_ty).into()),
                step: Box::new((*step).into()),
                from: Box::new((*from).into()),
                to: Box::new((*to).into()),
                accessibility: Box::new((*accessibility).into()),
                transition: Box::new((*transition).into()),
            },
            syntax::SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => Self::RecordTypeCtor {
                access: access.into(),
                parameters: parameters.into_iter().map(Into::into).collect(),
                fields: fields
                    .into_iter()
                    .map(|(name, value)| (name, value.into()))
                    .collect(),
            },
            syntax::SExp::PowerSet { set } => Self::PowerSet {
                set: Box::new((*set).into()),
            },
            syntax::SExp::SubSet {
                var,
                set,
                predicate,
            } => Self::SubSet {
                var,
                set: Box::new((*set).into()),
                predicate: Box::new((*predicate).into()),
            },
            syntax::SExp::Pred {
                superset,
                subset,
                element,
            } => Self::Pred {
                superset: Box::new((*superset).into()),
                subset: Box::new((*subset).into()),
                element: Box::new((*element).into()),
            },
            syntax::SExp::TypeLift { superset, subset } => Self::TypeLift {
                superset: Box::new((*superset).into()),
                subset: Box::new((*subset).into()),
            },
            syntax::SExp::Equal { left, right } => Self::Equal {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
            },
            syntax::SExp::Exists { bind } => Self::Exists { bind: bind.into() },
            syntax::SExp::TakeSet {
                bind,
                body,
                existence,
                uniqueness,
            } => Self::TakeSet {
                bind: bind.into(),
                body: Box::new((*body).into()),
                existence: Box::new((*existence).into()),
                uniqueness: Box::new((*uniqueness).into()),
            },
            syntax::SExp::TakeProp {
                bind,
                body,
                existence,
            } => Self::TakeProp {
                bind: bind.into(),
                body: Box::new((*body).into()),
                existence: Box::new((*existence).into()),
            },
            syntax::SExp::ExistsIntro { element, set } => Self::ExistsIntro {
                element: Box::new((*element).into()),
                set: Box::new((*set).into()),
            },
            syntax::SExp::SubsetElim {
                element,
                subset,
                superset,
            } => Self::SubsetElim {
                element: Box::new((*element).into()),
                subset: Box::new((*subset).into()),
                superset: Box::new((*superset).into()),
            },
            syntax::SExp::IdRefl { element } => Self::IdRefl {
                element: Box::new((*element).into()),
            },
            syntax::SExp::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
                base,
                equality,
            } => Self::IdElim {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
                var,
                ty: Box::new((*ty).into()),
                predicate: Box::new((*predicate).into()),
                base: Box::new((*base).into()),
                equality: Box::new((*equality).into()),
            },
            syntax::SExp::AxiomSetExt {
                left,
                right,
                left_to_right,
                right_to_left,
            } => Self::AxiomSetExt {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
                left_to_right: Box::new((*left_to_right).into()),
                right_to_left: Box::new((*right_to_left).into()),
            },
            syntax::SExp::AxiomFunExt {
                left,
                right,
                pointwise,
            } => Self::AxiomFunExt {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
                pointwise: Box::new((*pointwise).into()),
            },
            syntax::SExp::AxiomClassicalIndefiniteChoice {
                domain,
                family,
                inhabited,
            } => Self::AxiomClassicalIndefiniteChoice {
                domain: Box::new((*domain).into()),
                family: Box::new((*family).into()),
                inhabited: Box::new((*inhabited).into()),
            },
            syntax::SExp::TakeEq {
                func,
                domain,
                codomain,
                element,
                existence,
                uniqueness,
            } => Self::TakeEq {
                func: Box::new((*func).into()),
                domain: Box::new((*domain).into()),
                codomain: Box::new((*codomain).into()),
                element: Box::new((*element).into()),
                existence: Box::new((*existence).into()),
                uniqueness: Box::new((*uniqueness).into()),
            },
            syntax::SExp::Block(v0) => Self::Block(v0.into()),
            syntax::SExp::Program(v0) => Self::Program(v0.into()),
        }
    }
}

impl From<syntax::Block> for Block {
    fn from(value: syntax::Block) -> Self {
        Self {
            statements: value.statements.into_iter().map(Into::into).collect(),
            result: Box::new((*value.result).into()),
        }
    }
}

impl From<syntax::Statement> for Statement {
    fn from(value: syntax::Statement) -> Self {
        match value {
            syntax::Statement::Fix(v0) => Self::Fix(v0.into_iter().map(Into::into).collect()),
            syntax::Statement::Let { var, ty, body } => Self::Let {
                var,
                ty: ty.into(),
                body: body.into(),
            },
            syntax::Statement::Bind {
                var,
                ty,
                computation,
            } => Self::Bind {
                var,
                ty: ty.into(),
                computation: computation.into(),
            },
            syntax::Statement::Sufficient { map, map_ty } => Self::Sufficient {
                map: map.into(),
                map_ty: map_ty.into(),
            },
            syntax::Statement::TakeFrom { var, ty, existence } => Self::TakeFrom {
                var,
                ty: ty.into(),
                existence: existence.into(),
            },
        }
    }
}
