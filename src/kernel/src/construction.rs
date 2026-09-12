//! Construction of rules whose result family is determined by a sort annotation.
use super::{ids::*, sort::*, syntax::*};
pub(crate) fn base_kind(arena: &Arena, sort: BaseSort) -> Result<Expression, String> {
    let family = Family::at(sort, Stage::Kind);
    Ok(match family {
        Family::SetKind => arena
            .alloc(SetKindNode {
                level: sort.level().expect("indexed family"),
                form: SetKindForm::Base,
            })
            .into(),
        Family::PropKind => arena
            .alloc(PropKindNode {
                form: PropKindForm::Base,
            })
            .into(),
        Family::ValueKind => arena
            .alloc(ValueKindNode {
                level: sort.level().expect("indexed family"),
                form: ValueKindForm::Base,
            })
            .into(),
        Family::ComputationKind => arena
            .alloc(ComputationKindNode {
                level: sort.level().expect("indexed family"),
                form: ComputationKindForm::Base,
            })
            .into(),
        _ => return Err("constructor has no syntax in this family".into()),
    })
}
pub(crate) fn bound(
    arena: &Arena,
    sort: BaseSort,
    stage: Stage,
    index: usize,
) -> Result<Expression, String> {
    let family = Family::at(sort, stage);
    Ok(match family {
        Family::SetTerm => arena
            .alloc(SetTermNode {
                level: sort.level().expect("indexed family"),
                form: SetTermForm::Bound { index },
            })
            .into(),
        Family::SetType => arena
            .alloc(SetTypeNode {
                level: sort.level().expect("indexed family"),
                form: SetTypeForm::Bound { index },
            })
            .into(),
        Family::PropTerm => arena
            .alloc(PropTermNode {
                form: PropTermForm::Bound { index },
            })
            .into(),
        Family::PropType => arena
            .alloc(PropTypeNode {
                form: PropTypeForm::Bound { index },
            })
            .into(),
        Family::ValueTerm => arena
            .alloc(ValueTermNode {
                level: sort.level().expect("indexed family"),
                form: ValueTermForm::Bound { index },
            })
            .into(),
        Family::ValueType => arena
            .alloc(ValueTypeNode {
                level: sort.level().expect("indexed family"),
                form: ValueTypeForm::Bound { index },
            })
            .into(),
        Family::ComputationType => arena
            .alloc(ComputationTypeNode {
                level: sort.level().expect("indexed family"),
                form: ComputationTypeForm::Bound { index },
            })
            .into(),
        _ => return Err("constructor has no syntax in this family".into()),
    })
}
pub(crate) fn product(
    arena: &Arena,
    rule: ProductRule,
    var: SymbolId,
    domain: Expression,
    body: Expression,
) -> Result<Expression, String> {
    let sort = rule.result.base();
    let family = Family::at(
        sort,
        if rule.result.is_upper() {
            Stage::Kind
        } else {
            Stage::Type
        },
    );
    Ok(match (family, rule.domain.is_upper()) {
        (Family::SetType, false) => arena
            .alloc(SetTypeNode {
                level: sort.level().expect("indexed family"),
                form: SetTypeForm::ProdTerm {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::SetType, true) => arena
            .alloc(SetTypeNode {
                level: sort.level().expect("indexed family"),
                form: SetTypeForm::ProdType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::SetKind, false) => arena
            .alloc(SetKindNode {
                level: sort.level().expect("indexed family"),
                form: SetKindForm::ProdTerm {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::SetKind, true) => arena
            .alloc(SetKindNode {
                level: sort.level().expect("indexed family"),
                form: SetKindForm::ProdType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::PropType, false) => arena
            .alloc(PropTypeNode {
                form: PropTypeForm::ProdTerm {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::PropType, true) => arena
            .alloc(PropTypeNode {
                form: PropTypeForm::ProdType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::PropKind, false) => arena
            .alloc(PropKindNode {
                form: PropKindForm::ProdTerm {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::PropKind, true) => arena
            .alloc(PropKindNode {
                form: PropKindForm::ProdType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::ValueKind, true) => arena
            .alloc(ValueKindNode {
                level: sort.level().expect("indexed family"),
                form: ValueKindForm::ProdType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::ComputationType, false) => arena
            .alloc(ComputationTypeNode {
                level: sort.level().expect("indexed family"),
                form: ComputationTypeForm::ProdTerm {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::ComputationType, true) => arena
            .alloc(ComputationTypeNode {
                level: sort.level().expect("indexed family"),
                form: ComputationTypeForm::ProdType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::ComputationKind, true) => arena
            .alloc(ComputationKindNode {
                level: sort.level().expect("indexed family"),
                form: ComputationKindForm::ProdType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        _ => return Err("constructor has no syntax in this family".into()),
    })
}
pub(crate) fn lambda(
    arena: &Arena,
    rule: ProductRule,
    var: SymbolId,
    domain: Expression,
    body: Expression,
) -> Result<Expression, String> {
    let sort = rule.result.base();
    let family = Family::at(
        sort,
        if rule.result.is_upper() {
            Stage::Type
        } else {
            Stage::Term
        },
    );
    Ok(match (family, rule.domain.is_upper()) {
        (Family::SetTerm, false) => arena
            .alloc(SetTermNode {
                level: sort.level().expect("indexed family"),
                form: SetTermForm::LambdaTerm {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::SetTerm, true) => arena
            .alloc(SetTermNode {
                level: sort.level().expect("indexed family"),
                form: SetTermForm::LambdaType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::SetType, false) => arena
            .alloc(SetTypeNode {
                level: sort.level().expect("indexed family"),
                form: SetTypeForm::LambdaTerm {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::SetType, true) => arena
            .alloc(SetTypeNode {
                level: sort.level().expect("indexed family"),
                form: SetTypeForm::LambdaType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::PropTerm, false) => arena
            .alloc(PropTermNode {
                form: PropTermForm::LambdaTerm {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::PropTerm, true) => arena
            .alloc(PropTermNode {
                form: PropTermForm::LambdaType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::PropType, false) => arena
            .alloc(PropTypeNode {
                form: PropTypeForm::LambdaTerm {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::PropType, true) => arena
            .alloc(PropTypeNode {
                form: PropTypeForm::LambdaType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::ValueType, true) => arena
            .alloc(ValueTypeNode {
                level: sort.level().expect("indexed family"),
                form: ValueTypeForm::LambdaType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::ComputationTerm, false) => arena
            .alloc(ComputationTermNode {
                level: sort.level().expect("indexed family"),
                form: ComputationTermForm::LambdaTerm {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::ComputationTerm, true) => arena
            .alloc(ComputationTermNode {
                level: sort.level().expect("indexed family"),
                form: ComputationTermForm::LambdaType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        (Family::ComputationType, true) => arena
            .alloc(ComputationTypeNode {
                level: sort.level().expect("indexed family"),
                form: ComputationTypeForm::LambdaType {
                    rule,
                    var,
                    domain: domain.try_into()?,
                    body: body.try_into()?,
                },
            })
            .into(),
        _ => return Err("constructor has no syntax in this family".into()),
    })
}
pub(crate) fn apply(
    arena: &Arena,
    rule: ProductRule,
    function: Expression,
    argument: Expression,
) -> Result<Expression, String> {
    let sort = rule.body.base();
    let family = Family::at(
        sort,
        if rule.body.is_upper() {
            Stage::Type
        } else {
            Stage::Term
        },
    );
    Ok(match (family, rule.domain.is_upper()) {
        (Family::SetTerm, false) => arena
            .alloc(SetTermNode {
                level: sort.level().expect("indexed family"),
                form: SetTermForm::AppTerm {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::SetTerm, true) => arena
            .alloc(SetTermNode {
                level: sort.level().expect("indexed family"),
                form: SetTermForm::AppType {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::SetType, false) => arena
            .alloc(SetTypeNode {
                level: sort.level().expect("indexed family"),
                form: SetTypeForm::AppTerm {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::SetType, true) => arena
            .alloc(SetTypeNode {
                level: sort.level().expect("indexed family"),
                form: SetTypeForm::AppType {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::PropTerm, false) => arena
            .alloc(PropTermNode {
                form: PropTermForm::AppTerm {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::PropTerm, true) => arena
            .alloc(PropTermNode {
                form: PropTermForm::AppType {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::PropType, false) => arena
            .alloc(PropTypeNode {
                form: PropTypeForm::AppTerm {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::PropType, true) => arena
            .alloc(PropTypeNode {
                form: PropTypeForm::AppType {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::ValueType, true) => arena
            .alloc(ValueTypeNode {
                level: sort.level().expect("indexed family"),
                form: ValueTypeForm::AppType {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::ComputationTerm, false) => arena
            .alloc(ComputationTermNode {
                level: sort.level().expect("indexed family"),
                form: ComputationTermForm::AppTerm {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::ComputationTerm, true) => arena
            .alloc(ComputationTermNode {
                level: sort.level().expect("indexed family"),
                form: ComputationTermForm::AppType {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        (Family::ComputationType, true) => arena
            .alloc(ComputationTypeNode {
                level: sort.level().expect("indexed family"),
                form: ComputationTypeForm::AppType {
                    rule,
                    function: function.try_into()?,
                    argument: argument.try_into()?,
                },
            })
            .into(),
        _ => return Err("constructor has no syntax in this family".into()),
    })
}
pub(crate) fn inductive_type(
    arena: &Arena,
    sort: BaseSort,
    stage: Stage,
    inductive: InductiveId,
    parameters: Vec<LogicalArgument>,
) -> Result<Expression, String> {
    let family = Family::at(sort, stage);
    Ok(match family {
        Family::SetType => arena
            .alloc(SetTypeNode {
                level: sort.level().expect("indexed family"),
                form: SetTypeForm::IndType {
                    inductive,
                    parameters,
                },
            })
            .into(),
        Family::SetKind => arena
            .alloc(SetKindNode {
                level: sort.level().expect("indexed family"),
                form: SetKindForm::IndType {
                    inductive,
                    parameters,
                },
            })
            .into(),
        Family::PropType => arena
            .alloc(PropTypeNode {
                form: PropTypeForm::IndType {
                    inductive,
                    parameters,
                },
            })
            .into(),
        Family::PropKind => arena
            .alloc(PropKindNode {
                form: PropKindForm::IndType {
                    inductive,
                    parameters,
                },
            })
            .into(),
        _ => return Err("constructor has no syntax in this family".into()),
    })
}
pub(crate) fn inductive_constructor(
    arena: &Arena,
    sort: BaseSort,
    stage: Stage,
    inductive: InductiveId,
    constructor: usize,
    parameters: Vec<LogicalArgument>,
) -> Result<Expression, String> {
    let family = Family::at(sort, stage);
    Ok(match family {
        Family::SetTerm => arena
            .alloc(SetTermNode {
                level: sort.level().expect("indexed family"),
                form: SetTermForm::IndCtor {
                    inductive,
                    constructor,
                    parameters,
                },
            })
            .into(),
        Family::SetType => arena
            .alloc(SetTypeNode {
                level: sort.level().expect("indexed family"),
                form: SetTypeForm::IndCtor {
                    inductive,
                    constructor,
                    parameters,
                },
            })
            .into(),
        Family::PropTerm => arena
            .alloc(PropTermNode {
                form: PropTermForm::IndCtor {
                    inductive,
                    constructor,
                    parameters,
                },
            })
            .into(),
        Family::PropType => arena
            .alloc(PropTypeNode {
                form: PropTypeForm::IndCtor {
                    inductive,
                    constructor,
                    parameters,
                },
            })
            .into(),
        _ => return Err("constructor has no syntax in this family".into()),
    })
}
