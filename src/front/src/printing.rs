use std::fmt::Display;

use crate::elaborator::module_manager::{InstantiatedModule, ModuleElaborated, ModuleManager};

use super::syntax::*;

impl From<Identifier> for kernel::exp::Var {
    fn from(value: Identifier) -> Self {
        kernel::exp::Var::new(&value.0)
    }
}

impl From<&Identifier> for kernel::exp::Var {
    fn from(value: &Identifier) -> Self {
        kernel::exp::Var::new(&value.0)
    }
}

impl From<String> for Identifier {
    fn from(value: String) -> Self {
        Identifier(value)
    }
}

impl From<&str> for Identifier {
    fn from(value: &str) -> Self {
        Identifier(value.to_string())
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for MacroToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for LocalAccess {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocalAccess::Current { access } => {
                write!(f, "{}", access)
            }
            LocalAccess::Named { access, child } => {
                write!(f, "{}.{}", access, child)
            }
        }
    }
}

impl Display for RightBind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let vars_str = self
            .vars
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "({}: {})", vars_str, self.ty)
    }
}

fn impl_display_for_vec_rightbinds(
    binds: &[RightBind],
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    for (i, bind) in binds.iter().enumerate() {
        if i > 0 {
            write!(f, " -> ")?;
        }
        write!(f, "{}", bind)?;
    }
    Ok(())
}

impl Display for SExp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SExp::AccessPath { access, parameters } => {
                write!(f, "{}", access)?;
                if !parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", param)?;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            SExp::AssociatedAccess { base, field } => {
                write!(f, "{}#{}", base, field)
            }
            SExp::MathMacro { tokens } => todo!(),
            SExp::NamedMacro { name, tokens } => todo!(),
            SExp::Where { exp, clauses } => {
                write!(f, "where {} {{ ", exp)?;
                for (var, ty, body) in clauses {
                    write!(f, "{}: {} := {}; ", var, ty, body)?;
                }
                write!(f, "}}")
            }
            SExp::WithProofs { exp, proofs } => {
                write!(f, "with_proofs {} {{ ", exp)?;
                for proof in proofs {
                    write!(f, "{:?} ", proof)?; // Placeholder
                }
                write!(f, "}}")
            }
            SExp::Sort(sort) => {
                write!(f, "{:?}", sort)
            }
            SExp::Prod { bind, body } | SExp::Lam { bind, body } => {
                let is_prod = matches!(self, SExp::Prod { .. });
                match bind {
                    Bind::Named(right_bind) => {
                        let vars_str = right_bind
                            .vars
                            .iter()
                            .map(|v| v.to_string())
                            .collect::<Vec<_>>()
                            .join(", ");
                        if is_prod {
                            write!(f, "({}: {}) -> {}", vars_str, right_bind.ty, body)
                        } else {
                            write!(f, "({}: {}) => {}", vars_str, right_bind.ty, body)
                        }
                    }
                    Bind::Subset { var, ty, predicate } => {
                        if is_prod {
                            write!(f, "({}: {} | {}) -> {}", var, ty, predicate, body)
                        } else {
                            write!(f, "({}: {} | {}) => {}", var, ty, predicate, body)
                        }
                    }
                    Bind::SubsetWithProof {
                        var,
                        ty,
                        predicate,
                        proof_var,
                    } => {
                        if is_prod {
                            write!(
                                f,
                                "({}: {} | {}: {}) -> {}",
                                var, ty, predicate, proof_var, body
                            )
                        } else {
                            write!(
                                f,
                                "({}: {} | {}: {}) => {}",
                                var, ty, predicate, proof_var, body
                            )
                        }
                    }
                }
            }
            SExp::App { func, arg, piped } => {
                if *piped {
                    write!(f, "{} | {}", func, arg)
                } else {
                    write!(f, "{} {}", func, arg)
                }
            }
            SExp::Cast { exp, to } => {
                write!(f, "{} \\as {}", exp, to)
            }
            SExp::IndElim {
                path,
                elim,
                return_type,
                cases,
            } => {
                write!(f, "ind_elim {}", path)?;
                write!(f, "elim: {}, ", elim)?;
                write!(f, "return_type: {}, ", return_type)?;
                write!(f, " {{")?;
                for (ctor_name, case) in cases {
                    write!(f, "| {} => {} ; ", ctor_name, case)?;
                }
                write!(f, "}}")
            }
            SExp::IndElimPrim {
                path,
                parameters,
                sort,
            } => {
                write!(f, "ind_elim_prim {}[", path)?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, "] : {}", sort)
            }
            SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => {
                write!(f, "{}[", access)?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, "] {{ ")?;
                for (field_name, field_type) in fields {
                    write!(f, "{}: {}; ", field_name, field_type)?;
                }
                write!(f, "}}")
            }
            SExp::ProveLater { prop } => {
                write!(f, "prove_later {}", prop)
            }
            SExp::PowerSet { set } => {
                write!(f, "PowerSet({})", set)
            }
            SExp::SubSet {
                var,
                set,
                predicate,
            } => {
                write!(f, "{{ {} : {} | {} }}", var, set, predicate)
            }
            SExp::Pred {
                superset,
                subset,
                element,
            } => {
                write!(f, "Pred({}, {}, {})", superset, subset, element)
            }
            SExp::TypeLift { superset, subset } => {
                write!(f, "TypeLift({}, {})", superset, subset)
            }
            SExp::Equal { left, right } => {
                write!(f, "{} == {}", left, right)
            }
            SExp::Exists { bind } => match bind {
                Bind::Named(right_bind) => {
                    let vars_str = right_bind
                        .vars
                        .iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "exists ({}: {}). ", vars_str, right_bind.ty)
                }
                Bind::Subset { var, ty, predicate } => {
                    write!(f, "exists ({}: {} | {}). ", var, ty, predicate)
                }
                Bind::SubsetWithProof {
                    var,
                    ty,
                    predicate,
                    proof_var,
                } => {
                    write!(
                        f,
                        "exists ({}: {} | {}: {}). ",
                        var, ty, predicate, proof_var
                    )
                }
            },
            SExp::Take { bind, body } => match bind {
                Bind::Named(right_bind) => {
                    let vars_str = right_bind
                        .vars
                        .iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "\\take ({}: {}) => {}", vars_str, right_bind.ty, body)
                }
                Bind::Subset { var, ty, predicate } => {
                    write!(f, "\\take ({}: {} | {}) => {}", var, ty, predicate, body)
                }
                Bind::SubsetWithProof {
                    var,
                    ty,
                    predicate,
                    proof_var,
                } => {
                    write!(
                        f,
                        "\\take ({}: {} | {}: {}) => {}",
                        var, ty, predicate, proof_var, body
                    )
                }
            },
            SExp::ProofTermRaw(sprove_command_by) => {
                write!(f, "{}", sprove_command_by)
            }
            SExp::Block(block) => {
                write!(f, "\\block {{ ")?;
                let Block { statements, result } = block;
                for stmt in statements {
                    write!(f, "{}; ", stmt)?;
                }
                write!(f, "return {};", result)?;
                write!(f, "}}")
            }
        }
    }
}

impl Display for SProveCommandBy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SProveCommandBy::Construct { term } => {
                write!(f, "\\construct {}", term)
            }
            SProveCommandBy::Exact { term, set } => {
                write!(f, "\\exact {} : {}", term, set)
            }
            SProveCommandBy::SubsetElim {
                superset,
                subset,
                elem,
            } => {
                write!(f, "\\subset_elim {}, {}, {}", superset, subset, elem)
            }
            SProveCommandBy::IdRefl { term } => {
                write!(f, "\\id_refl {}", term)
            }
            SProveCommandBy::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
            } => {
                write!(
                    f,
                    "\\id_elim {}, {}, {}, {}, {}",
                    left, right, var, ty, predicate
                )
            }
            SProveCommandBy::TakeEq {
                func,
                elem,
                domain,
                codomain,
            } => {
                write!(f, "\\take_eq {}, {}, {}, {}", func, elem, domain, codomain)
            }
            SProveCommandBy::Axiom(axiom) => {
                write!(f, "\\axiom {:?}", axiom)
            }
        }
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Fix(right_binds) => {
                let binds_str = right_binds
                    .iter()
                    .map(|bind| {
                        let vars_str = bind
                            .vars
                            .iter()
                            .map(|v| v.to_string())
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("({}: {})", vars_str, bind.ty)
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "\\fix {}", binds_str)
            }
            Statement::Let { var, ty, body } => {
                write!(f, "\\let {}: {} := {}", var, ty, body)
            }
            Statement::Take { bind } => match bind {
                Bind::Named(right_bind) => {
                    let vars_str = right_bind
                        .vars
                        .iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "\\take ({}: {}) ", vars_str, right_bind.ty)
                }
                Bind::Subset { var, ty, predicate } => {
                    write!(f, "\\take ({}: {} | {}) ", var, ty, predicate)
                }
                Bind::SubsetWithProof {
                    var,
                    ty,
                    predicate,
                    proof_var,
                } => {
                    write!(
                        f,
                        "\\take ({}: {} | {}: {}) ",
                        var, ty, predicate, proof_var
                    )
                }
            },
            Statement::Sufficient { map, map_ty } => {
                write!(f, "\\sufficient {}: {}", map, map_ty)
            }
        }
    }
}

impl Display for ModuleItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModuleItem::Definition { name, ty, body } => {
                write!(f, "\\def {}: {} := {}", name, ty, body)
            }
            ModuleItem::Inductive {
                type_name,
                parameters,
                indices,
                sort,
                constructors,
            } => {
                write!(f, "\\inductive {}[", type_name)?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, "] (")?;
                for (i, index) in indices.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", index)?;
                }
                write!(f, ") : {} {{ ", sort)?;
                for (ctor_name, rightbinds, end) in constructors {
                    write!(f, "| {}: ", ctor_name)?;
                    impl_display_for_vec_rightbinds(rightbinds, f)?;
                    write!(f, " -> {}; ", end)?;
                }
                write!(f, "}}")
            }
            ModuleItem::Record {
                type_name,
                parameters,
                sort,
                fields,
            } => {
                write!(f, "\\record {}[", type_name)?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, "] : {} {{ ", sort)?;
                for (field_name, field_type) in fields {
                    write!(f, "{}: {}; ", field_name, field_type)?;
                }
                write!(f, "}}")
            }
            ModuleItem::ChildModule { module } => {
                write!(f, "{}", module)
            }
            ModuleItem::Import { path, import_name } => {
                write!(f, "\\import {:?} as {}", path, import_name)
            }
            ModuleItem::MathMacro { before, after } => todo!(),
            ModuleItem::UserMacro {
                name,
                before,
                after,
            } => todo!(),
            ModuleItem::Eval { exp } => {
                write!(f, "\\eval {}", exp)
            }
            ModuleItem::Normalize { exp } => {
                write!(f, "\\normalize {}", exp)
            }
            ModuleItem::Check { exp, ty } => {
                write!(f, "\\check {} : {}", exp, ty)
            }
            ModuleItem::Infer { exp } => {
                write!(f, "\\infer {}", exp)
            }
        }
    }
}

impl Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Module {
            name,
            parameters,
            declarations,
        } = self;
        write!(f, "\\module {}", name)?;
        impl_display_for_vec_rightbinds(parameters, f)?;
        write!(f, " {{ ")?;
        for decl in declarations {
            write!(f, "{}; ", decl)?;
        }
        write!(f, "}}")
    }
}

impl Display for ModItemDefinition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\\def {}{}", self.name, self.body)
    }
}

impl Display for ModItemInductive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ModItemInductive {
            type_name,
            ctor_names,
            ind_defs,
        } = self;
        write!(
            f,
            "\\inductive {} {:?} := {ind_defs:?}",
            type_name, ctor_names
        )
    }
}

impl Display for ModItemRecord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ModItemRecord {
            type_name,
            rc_spec_as_indtype,
        } = self;
        write!(f, "\\record {type_name} := {rc_spec_as_indtype:?}")
    }
}

impl Display for ModuleItemAccessible {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModuleItemAccessible::Definition(mod_item_definition) => {
                write!(f, "{}", mod_item_definition)
            }
            ModuleItemAccessible::Inductive(mod_item_inductive) => {
                write!(f, "{}", mod_item_inductive)
            }
            ModuleItemAccessible::Record(mod_item_record) => {
                write!(f, "{}", mod_item_record)
            }
        }
    }
}

impl Display for InstantiatedModule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let InstantiatedModule {
            parameters_instantiated,
            items,
        } = self;
        write!(f, "Instantiated Module {{ ")?;
        write!(f, "(")?;
        for (param, inst) in parameters_instantiated {
            write!(f, "{} := {}; ", param, inst)?;
        }
        write!(f, ") ")?;
        for item in items {
            write!(f, "{}; ", item)?;
        }
        write!(f, "}}")
    }
}

impl Display for crate::elaborator::module_manager::ItemAccessResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            crate::elaborator::module_manager::ItemAccessResult::Definition(
                mod_item_definition,
            ) => {
                write!(f, "{}", mod_item_definition)
            }
            crate::elaborator::module_manager::ItemAccessResult::Inductive(mod_item_inductive) => {
                write!(f, "{}", mod_item_inductive)
            }
            crate::elaborator::module_manager::ItemAccessResult::Record(mod_item_record) => {
                write!(f, "{}", mod_item_record)
            }
            crate::elaborator::module_manager::ItemAccessResult::Expression(exp) => {
                write!(f, "{}", exp)
            }
        }
    }
}

impl Display for ModuleManager {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "ModuleManager")?;
        let current = self.current_index();
        for (i, module_elaborated) in self.modules().iter().enumerate() {
            writeln!(
                f,
                "{}{} ",
                if current == i { "**" } else { "  " },
                module_elaborated
            )?;
        }
        write!(f, "}}")
    }
}

impl Display for ModuleElaborated {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ModuleElaborated {
            name,
            parameters,
            items,
            child_modules,
            parent_module,
        } = self;
        write!(f, "ModuleElaborated {{ name: {}, ", name)?;
        write!(f, "parameters: [")?;
        for (i, (var, ty)) in parameters.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{var}: {ty}")?;
        }
        write!(f, "], ")?;
        write!(f, "items: [")?;
        for (i, item) in items.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", item)?;
        }
        write!(f, "], ")?;
        write!(f, "child_modules: [")?;
        for (i, child) in child_modules.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", child)?;
        }
        write!(f, "], ")?;
        write!(f, "parent_module: {:?} ", parent_module)?;
        write!(f, "}}")
    }
}
