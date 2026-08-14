use crate::printing::ptr_lower32bit_base62_fixed;
use kernel::exp::{Context, DefinedConstant, Exp, Sort, Var};

fn format_var(var: &Var) -> String {
    format!(
        "{}[{}]",
        var.as_str(),
        ptr_lower32bit_base62_fixed(var.ptr() as *const ())
    )
}

pub(super) fn format_sort(sort: &Sort) -> String {
    match sort {
        Sort::Prop => "\\Prop".to_string(),
        Sort::PropKind => "\\PropKind".to_string(),
        Sort::Set(i) => format!("\\Set({i})"),
        Sort::SetKind(i) => format!("\\SetKind({i})"),
        Sort::Univ => "\\Univ".to_string(),
        Sort::UnivKind => "\\UnivKind".to_string(),
    }
}

pub(super) fn format_exp(exp: &Exp) -> String {
    match exp {
        Exp::Sort(sort) => format_sort(sort),
        Exp::Var(var) => format_var(var),
        Exp::Prod { var, ty, body } => format!(
            "({}: {}) -> {}",
            format_var(var),
            format_exp(ty),
            format_exp(body)
        ),
        Exp::Lam { var, ty, body } => format!(
            "({}: {}) => {}",
            format_var(var),
            format_exp(ty),
            format_exp(body)
        ),
        Exp::App { func, arg } => format!("({}) ({})", format_exp(func), format_exp(arg)),
        Exp::DefinedConstant(rc) => {
            format!("{}{}", super::print_rc_ptr(rc), format_defined_constant(rc))
        }
        Exp::IndType {
            indspec,
            parameters,
        } => format!(
            "{}[{}]",
            super::print_rc_ptr(indspec),
            parameters
                .iter()
                .map(format_exp)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Exp::IndCtor {
            indspec,
            parameters,
            idx,
        } => format!(
            "{}.{}[{}]",
            super::print_rc_ptr(indspec),
            idx,
            parameters
                .iter()
                .map(format_exp)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Exp::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => format!(
            "elim {} \\in {} \\return {} with {{{}}}",
            format_exp(elim),
            super::print_rc_ptr(indspec),
            format_exp(return_type),
            cases.iter().map(format_exp).collect::<Vec<_>>().join(", ")
        ),
        Exp::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => format!(
            "subset_intro({}, {}, {}, {})",
            format_exp(superset),
            format_exp(subset),
            format_exp(element),
            format_exp(proof),
        ),
        Exp::PowerSet { set } => format!("Pow({})", format_exp(set)),
        Exp::SubSet {
            var,
            set,
            predicate,
        } => format!(
            "{{ {}: {} | {} }}",
            format_var(var),
            format_exp(set),
            format_exp(predicate)
        ),
        Exp::Pred {
            superset,
            subset,
            element,
        } => format!(
            "{} ∈ {} ⊆ {}",
            format_exp(element),
            format_exp(subset),
            format_exp(superset)
        ),
        Exp::TypeLift { superset, subset } => {
            format!("TypeLift({}, {})", format_exp(superset), format_exp(subset))
        }
        Exp::Equal { left, right } => format!("{} = {}", format_exp(left), format_exp(right)),
        Exp::Exists { set } => format!("\\exists {}", format_exp(set)),
        Exp::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => format!(
            "\\Take({}, {}, {}) by ({}, {})",
            format_exp(domain),
            format_exp(codomain),
            format_exp(map),
            format_exp(existence),
            format_exp(uniqueness)
        ),
        Exp::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => format!(
            "\\TakeProp({}, {}, {}) by ({})",
            format_exp(domain),
            format_exp(proposition),
            format_exp(map),
            format_exp(existence),
        ),
        Exp::TakeSetUnchecked {
            domain,
            codomain,
            map,
        } => format!(
            "TakeSetUnchecked({}, {}, {})",
            format_exp(domain),
            format_exp(codomain),
            format_exp(map),
        ),
        Exp::TakePropUnchecked { proposition } => {
            format!("TakePropUnchecked({})", format_exp(proposition))
        }
        Exp::ExistsIntro { element, set } => {
            format!("exact({}, {})", format_exp(element), format_exp(set))
        }
        Exp::SubsetElim {
            element,
            subset,
            superset,
        } => format!(
            "subset_elim({}, {}, {})",
            format_exp(superset),
            format_exp(subset),
            format_exp(element)
        ),
        Exp::IdRefl { element } => format!("refl({})", format_exp(element)),
        Exp::IdElim { .. } | Exp::TakeEq { .. } | Exp::TakeEqUnchecked { .. } => {
            format!("{:?}", exp)
        }
    }
}

pub(super) fn format_ctx(ctx: &Context) -> String {
    ctx.iter()
        .map(|(var, ty)| format!("{}: {}", format_var(var), format_exp(ty)))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_defined_constant(rc: &std::rc::Rc<DefinedConstant>) -> String {
    format!("[: {} := {}]", format_exp(&rc.ty), format_exp(&rc.body))
}
