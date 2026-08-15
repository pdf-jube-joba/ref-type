use crate::printing::ptr_lower32bit_base62_fixed;
use kernel::exp::{Arena, Context, DefinedConstant, Exp, Node, Sort, Var};

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
        Sort::Set(level) => format!("\\Set({level})"),
        Sort::SetKind(level) => format!("\\SetKind({level})"),
        Sort::Univ => "\\Univ".to_string(),
        Sort::UnivKind => "\\UnivKind".to_string(),
    }
}

pub(super) fn format_exp(arena: &Arena, exp: Exp) -> String {
    let child = |exp| format_exp(arena, exp);
    match arena.get(exp) {
        Node::Sort(sort) => format_sort(&sort),
        Node::Bound(index) => format!("#{index}"),
        Node::Var(var) => format_var(&var),
        Node::Prod { var, ty, body } => {
            format!("({}: {}) -> {}", format_var(&var), child(ty), child(body))
        }
        Node::Lam { var, ty, body } => {
            format!("({}: {}) => {}", format_var(&var), child(ty), child(body))
        }
        Node::App { func, arg } => format!("({}) ({})", child(func), child(arg)),
        Node::DefinedConstant(definition) => format!(
            "{}{}",
            super::print_rc_ptr(&definition),
            format_defined_constant(arena, &definition)
        ),
        Node::IndType {
            indspec,
            parameters,
        } => format!(
            "{}[{}]",
            super::print_rc_ptr(&indspec),
            parameters
                .into_iter()
                .map(child)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Node::IndCtor {
            indspec,
            parameters,
            idx,
        } => format!(
            "{}.{}[{}]",
            super::print_rc_ptr(&indspec),
            idx,
            parameters
                .into_iter()
                .map(child)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Node::IndElim {
            indspec,
            elim,
            return_type,
            cases,
        } => format!(
            "elim {} \\in {} \\return {} with {{{}}}",
            child(elim),
            super::print_rc_ptr(&indspec),
            child(return_type),
            cases.into_iter().map(child).collect::<Vec<_>>().join(", ")
        ),
        Node::SubsetIntro {
            superset,
            subset,
            element,
            proof,
        } => format!(
            "subset_intro({}, {}, {}, {})",
            child(superset),
            child(subset),
            child(element),
            child(proof)
        ),
        Node::PowerSet { set } => format!("Pow({})", child(set)),
        Node::SubSet {
            var,
            set,
            predicate,
        } => format!(
            "{{ {}: {} | {} }}",
            format_var(&var),
            child(set),
            child(predicate)
        ),
        Node::Pred {
            superset,
            subset,
            element,
        } => format!(
            "{} ∈ {} ⊆ {}",
            child(element),
            child(subset),
            child(superset)
        ),
        Node::TypeLift { superset, subset } => {
            format!("TypeLift({}, {})", child(superset), child(subset))
        }
        Node::Equal { left, right } => format!("{} = {}", child(left), child(right)),
        Node::Exists { set } => format!("\\exists {}", child(set)),
        Node::TakeSet {
            domain,
            codomain,
            map,
            existence,
            uniqueness,
        } => format!(
            "\\Take({}, {}, {}) by ({}, {})",
            child(domain),
            child(codomain),
            child(map),
            child(existence),
            child(uniqueness)
        ),
        Node::TakeProp {
            domain,
            proposition,
            map,
            existence,
        } => format!(
            "\\TakeProp({}, {}, {}) by ({})",
            child(domain),
            child(proposition),
            child(map),
            child(existence)
        ),
        Node::ExistsIntro { element, set } => {
            format!("exact({}, {})", child(element), child(set))
        }
        Node::SubsetElim {
            element,
            subset,
            superset,
        } => format!(
            "subset_elim({}, {}, {})",
            child(superset),
            child(subset),
            child(element)
        ),
        Node::IdRefl { element } => format!("refl({})", child(element)),
        Node::IdElim { .. } | Node::TakeEq { .. } => format!("{:?}", arena.get(exp)),
    }
}

pub(super) fn format_ctx(arena: &Arena, ctx: &Context) -> String {
    ctx.iter()
        .map(|(var, ty)| format!("{}: {}", format_var(var), format_exp(arena, *ty)))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_defined_constant(arena: &Arena, definition: &DefinedConstant) -> String {
    format!(
        "[: {} := {}]",
        format_exp(arena, definition.ty),
        format_exp(arena, definition.body)
    )
}
