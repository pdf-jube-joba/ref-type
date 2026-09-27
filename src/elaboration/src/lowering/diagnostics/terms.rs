//! Surface rendering for each indexed syntax family.
use super::*;
impl Renderer<'_> {
    pub(super) fn term(&mut self, e: Expression) -> Term {
        match self.error.node(e) {
            ExpressionNode::SetTerm(node) => {
                use SetTermForm::*;
                match &node.form {
                    Bound { index } => self.bound(*index),
                    Annotated { global, body, .. } => self.annotation(*global, (*body).into()),
                    LambdaTerm {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, false),
                    LambdaType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, false),
                    AppTerm {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
                    AppType {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
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
                        var,
                        state_ty,
                        result_ty,
                        motive,
                        on_continue,
                        on_finish,
                        scrutinee,
                        ..
                    } => self.recursor(
                        *var,
                        (*state_ty).into(),
                        (*result_ty).into(),
                        (*motive).into(),
                        (*on_continue).into(),
                        (*on_finish).into(),
                        (*scrutinee).into(),
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
                        motive_vars,
                        scrutinee,
                        motive_domains,
                        motive_body,
                        cases,
                    } => self.elimination(
                        *inductive,
                        (*scrutinee).into(),
                        motive_vars,
                        motive_domains.iter().copied().map(Into::into).collect(),
                        (*motive_body).into(),
                        cases.iter().copied().map(Into::into).collect(),
                        true,
                    ),
                    Case {
                        inductive,
                        motive_vars,
                        scrutinee,
                        motive_domains,
                        motive_body,
                        branches,
                    } => self.elimination(
                        *inductive,
                        (*scrutinee).into(),
                        motive_vars,
                        motive_domains.iter().copied().map(Into::into).collect(),
                        (*motive_body).into(),
                        branches.iter().copied().map(Into::into).collect(),
                        false,
                    ),
                    SetCase {
                        inductive,
                        binders,
                        result_ty,
                        scrutinee,
                        branches,
                    } => self.case(
                        *inductive,
                        (*scrutinee).into(),
                        (*result_ty).into(),
                        binders,
                        branches.iter().copied().map(Into::into).collect(),
                    ),
                }
            }
            ExpressionNode::SetType(node) => {
                use SetTypeForm::*;
                match &node.form {
                    Bound { index } => self.bound(*index),
                    Annotated { global, body, .. } => self.annotation(*global, (*body).into()),
                    ProdTerm {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, false),
                    ProdType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, false),
                    LambdaTerm {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, false),
                    LambdaType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, false),
                    AppTerm {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
                    AppType {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
                    PowerSet { set } => self.call("Pow", &[(*set).into()]),
                    TypeLift { superset, subset } => {
                        self.call("Cast", &[(*superset).into(), (*subset).into()])
                    }
                    RunStep {
                        state_ty,
                        result_ty,
                    } => self.call("RunStep", &[(*state_ty).into(), (*result_ty).into()]),
                    BoxType { program_ty } => self.call("Box", &[(*program_ty).into()]),
                    Recursor {
                        var,
                        state_ty,
                        result_ty,
                        motive,
                        on_continue,
                        on_finish,
                        scrutinee,
                        ..
                    } => self.recursor(
                        *var,
                        (*state_ty).into(),
                        (*result_ty).into(),
                        (*motive).into(),
                        (*on_continue).into(),
                        (*on_finish).into(),
                        (*scrutinee).into(),
                    ),
                    IndType {
                        inductive,
                        parameters,
                    } => self.inductive(
                        *inductive,
                        None,
                        parameters.iter().copied().map(Into::into).collect(),
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
                        motive_vars,
                        scrutinee,
                        motive_domains,
                        motive_body,
                        cases,
                    } => self.elimination(
                        *inductive,
                        (*scrutinee).into(),
                        motive_vars,
                        motive_domains.iter().copied().map(Into::into).collect(),
                        (*motive_body).into(),
                        cases.iter().copied().map(Into::into).collect(),
                        true,
                    ),
                    Case {
                        inductive,
                        motive_vars,
                        scrutinee,
                        motive_domains,
                        motive_body,
                        branches,
                    } => self.elimination(
                        *inductive,
                        (*scrutinee).into(),
                        motive_vars,
                        motive_domains.iter().copied().map(Into::into).collect(),
                        (*motive_body).into(),
                        branches.iter().copied().map(Into::into).collect(),
                        false,
                    ),
                }
            }
            ExpressionNode::SetKind(node) => {
                use SetKindForm::*;
                match &node.form {
                    Base => Term::atom(universe("Set", node.level)),
                    ProdTerm {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, false),
                    ProdType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, false),
                    IndType {
                        inductive,
                        parameters,
                    } => self.inductive(
                        *inductive,
                        None,
                        parameters.iter().copied().map(Into::into).collect(),
                    ),
                    Annotated { global, body, .. } => self.annotation(*global, (*body).into()),
                }
            }
            ExpressionNode::PropTerm(node) => {
                use PropTermForm::*;
                match &node.form {
                    Bound { index } => self.bound(*index),
                    Annotated { global, body, .. } => self.annotation(*global, (*body).into()),
                    LambdaTerm {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, false),
                    LambdaType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, false),
                    AppTerm {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
                    AppType {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
                    Recursor {
                        var,
                        state_ty,
                        result_ty,
                        motive,
                        on_continue,
                        on_finish,
                        scrutinee,
                        ..
                    } => self.recursor(
                        *var,
                        (*state_ty).into(),
                        (*result_ty).into(),
                        (*motive).into(),
                        (*on_continue).into(),
                        (*on_finish).into(),
                        (*scrutinee).into(),
                    ),
                    IdRefl { element } => self.call("refl", &[(*element).into()]),
                    ExistsIntro { element, set } => {
                        self.call("exact", &[(*element).into(), (*set).into()])
                    }
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
                        motive_vars,
                        scrutinee,
                        motive_domains,
                        motive_body,
                        cases,
                    } => self.elimination(
                        *inductive,
                        (*scrutinee).into(),
                        motive_vars,
                        motive_domains.iter().copied().map(Into::into).collect(),
                        (*motive_body).into(),
                        cases.iter().copied().map(Into::into).collect(),
                        true,
                    ),
                    Case {
                        inductive,
                        motive_vars,
                        scrutinee,
                        motive_domains,
                        motive_body,
                        branches,
                    } => self.elimination(
                        *inductive,
                        (*scrutinee).into(),
                        motive_vars,
                        motive_domains.iter().copied().map(Into::into).collect(),
                        (*motive_body).into(),
                        branches.iter().copied().map(Into::into).collect(),
                        false,
                    ),
                }
            }
            ExpressionNode::PropType(node) => {
                use PropTypeForm::*;
                match &node.form {
                    Bound { index } => self.bound(*index),
                    Annotated { global, body, .. } => self.annotation(*global, (*body).into()),
                    ProdTerm {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, false),
                    ProdType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, false),
                    LambdaTerm {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, false),
                    LambdaType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, false),
                    AppTerm {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
                    AppType {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
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
                    Recursor {
                        var,
                        state_ty,
                        result_ty,
                        motive,
                        on_continue,
                        on_finish,
                        scrutinee,
                        ..
                    } => self.recursor(
                        *var,
                        (*state_ty).into(),
                        (*result_ty).into(),
                        (*motive).into(),
                        (*on_continue).into(),
                        (*on_finish).into(),
                        (*scrutinee).into(),
                    ),
                    IndType {
                        inductive,
                        parameters,
                    } => self.inductive(
                        *inductive,
                        None,
                        parameters.iter().copied().map(Into::into).collect(),
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
                        motive_vars,
                        scrutinee,
                        motive_domains,
                        motive_body,
                        cases,
                    } => self.elimination(
                        *inductive,
                        (*scrutinee).into(),
                        motive_vars,
                        motive_domains.iter().copied().map(Into::into).collect(),
                        (*motive_body).into(),
                        cases.iter().copied().map(Into::into).collect(),
                        true,
                    ),
                    Case {
                        inductive,
                        motive_vars,
                        scrutinee,
                        motive_domains,
                        motive_body,
                        branches,
                    } => self.elimination(
                        *inductive,
                        (*scrutinee).into(),
                        motive_vars,
                        motive_domains.iter().copied().map(Into::into).collect(),
                        (*motive_body).into(),
                        branches.iter().copied().map(Into::into).collect(),
                        false,
                    ),
                }
            }
            ExpressionNode::PropKind(node) => {
                use PropKindForm::*;
                match &node.form {
                    Base => Term::atom("\\Prop"),
                    ProdTerm {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, false),
                    ProdType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, false),
                    IndType {
                        inductive,
                        parameters,
                    } => self.inductive(
                        *inductive,
                        None,
                        parameters.iter().copied().map(Into::into).collect(),
                    ),
                    Annotated { global, body, .. } => self.annotation(*global, (*body).into()),
                }
            }
            ExpressionNode::ValueTerm(node) => {
                use ValueTermForm::*;
                match &node.form {
                    Bound { index } => self.bound(*index),
                    Annotated { global, body, .. } => self.annotation(*global, (*body).into()),
                    ThunkValue { computation } => self.call("thunk", &[(*computation).into()]),
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
                }
            }
            ExpressionNode::ValueType(node) => {
                use ValueTypeForm::*;
                match &node.form {
                    Bound { index } => self.bound(*index),
                    Annotated { global, body, .. } => self.annotation(*global, (*body).into()),
                    Thunk { computation_ty } => self.call("U", &[(*computation_ty).into()]),
                    RunStep {
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
                    LambdaType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, false),
                    AppType {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
                }
            }
            ExpressionNode::ValueKind(node) => {
                use ValueKindForm::*;
                match &node.form {
                    Base => Term::atom(universe("VType", node.level)),
                    ProdType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, false),
                }
            }
            ExpressionNode::ComputationTerm(node) => {
                use ComputationTermForm::*;
                match &node.form {
                    Annotated { global, body, .. } => self.annotation(*global, (*body).into()),
                    Return { value } => self.call("return", &[(*value).into()]),
                    Force { value } => self.call("force", &[(*value).into()]),
                    LambdaTerm {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, true),
                    LambdaType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, true),
                    AppTerm {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
                    AppType {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
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
                    Case {
                        inductive,
                        binders,
                        result_ty,
                        scrutinee,
                        branches,
                    } => self.case(
                        *inductive,
                        (*scrutinee).into(),
                        (*result_ty).into(),
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
                }
            }
            ExpressionNode::ComputationType(node) => {
                use ComputationTypeForm::*;
                match &node.form {
                    Bound { index } => self.bound(*index),
                    Annotated { global, body, .. } => self.annotation(*global, (*body).into()),
                    ReturnType { value_ty } => self.call("F", &[(*value_ty).into()]),
                    ProdTerm {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, true),
                    ProdType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, true),
                    LambdaType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), true, false),
                    AppType {
                        function, argument, ..
                    } => self.application((*function).into(), (*argument).into()),
                }
            }
            ExpressionNode::ComputationKind(node) => {
                use ComputationKindForm::*;
                match &node.form {
                    Base => Term::atom(universe("CType", node.level)),
                    ProdType {
                        var, domain, body, ..
                    } => self.binder(*var, (*domain).into(), (*body).into(), false, false),
                }
            }
        }
    }
}
