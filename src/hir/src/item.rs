//! Module and declaration structure after syntax lowering.
use crate::*;

// module definition
#[derive(Debug, Clone)]
pub struct Module {
    pub name: Identifier,
    pub parameters: Vec<RightBind>, // given parameters for module
    pub body: ModuleBody,
    pub span: SourceSpan,
    pub declaration_spans: Vec<SourceSpan>,
    pub source: Option<std::sync::Arc<SourceFile>>,
    pub header_source: Option<std::sync::Arc<SourceFile>>,
}

#[derive(Debug, Clone)]
pub enum ModuleBody {
    Inline(Vec<ModuleItem>), // sensitive to order
    External,
}

#[derive(Debug, Clone)]
pub enum ModuleItem {
    /// A recovered declaration remains in the outline and still shadows its name.
    Error {
        name: Option<Identifier>,
        message: String,
    },
    Definition {
        owner: Option<AssociatedOwner>,
        name: Identifier,
        binders: Vec<RightBind>,
        ty: SExp,
        body: SExp,
    },
    Inductive {
        type_name: Identifier,
        parameters: Vec<RightBind>,
        indices: Vec<RightBind>,
        kind: InductiveKind,
        constructors: Vec<(Identifier, Vec<RightBind>, SExp)>,
    },
    Record {
        type_name: Identifier,
        parameters: Vec<RightBind>,
        kind: InductiveKind,
        fields: Vec<(Identifier, SExp)>,
    },
    ChildModule {
        module: Box<Module>,
    },
    Import {
        path: ModuleInstantiatePath,
        import_name: Identifier,
    },
    MathMacro {
        name: Identifier,
        before: Vec<MacroSeqAtom>,
        after: SExp,
    },
    UserMacro {
        name: Identifier,
        before: Vec<MacroSeqAtom>,
        after: SExp,
    },
    UseMacro {
        import_name: Identifier,
        macro_name: Identifier,
    },
    Eval {
        exp: SExp,
    },
    Normalize {
        exp: SExp,
    },
    ComputationEval {
        exp: ComputationTermExp,
    },
    ComputationNormalize {
        exp: ComputationTermExp,
    },
    ValueCheck {
        exp: ValueTermExp,
        ty: ValueTypeExp,
    },
    ComputationCheck {
        exp: ComputationTermExp,
        ty: ComputationTypeExp,
    },
    ValueInfer {
        exp: ValueTermExp,
    },
    ComputationInfer {
        exp: ComputationTermExp,
    },
    Check {
        exp: SExp,
        ty: SExp,
    },
    Infer {
        exp: SExp,
    },
}

#[derive(Debug, Clone)]
pub struct AssociatedOwner {
    pub type_name: Identifier,
    pub parameters: Vec<RightBind>,
}

#[derive(Debug, Clone)]
pub enum ModuleInstantiatePath {
    FromPackage {
        package: Identifier,
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
    FromCurrent {
        back_parent: usize,
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
    FromRoot {
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
    FromImport {
        import_name: Identifier,
        calls: Vec<(Identifier, Vec<(Identifier, SExp)>)>,
    },
}
