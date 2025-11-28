#![allow(dead_code)]

use std::fmt::{self, Display, Formatter};

use front::{
    elaborator::module_manager::{
        InstantiatedModule, ItemAccessResult, ModuleElaborated, ModuleManager,
    },
    syntax::{
        Bind, Block, Identifier, LocalAccess, MacroToken, ModItemDefinition, ModItemInductive,
        ModItemRecord, Module, ModuleItem, ModuleItemAccessible, RightBind, SExp, SProveCommandBy,
        Statement,
    },
};

use super::for_kernel;

pub(super) struct FrontFmt<'a, T: ?Sized>(pub &'a T);

pub(super) fn display<'a, T: ?Sized>(value: &'a T) -> FrontFmt<'a, T> {
    FrontFmt(value)
}

impl<'a> Display for FrontFmt<'a, Identifier> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.as_str())
    }
}

impl<'a> Display for FrontFmt<'a, MacroToken> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.0)
    }
}

impl<'a> Display for FrontFmt<'a, LocalAccess> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            LocalAccess::Current { access } => write!(f, "{}", FrontFmt(access)),
            LocalAccess::Named { access, child } => {
                write!(f, "{}.{}", FrontFmt(access), FrontFmt(child))
            }
        }
    }
}

impl<'a> Display for FrontFmt<'a, RightBind> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let vars_str = self
            .0
            .vars
            .iter()
            .map(|v| format!("{}", FrontFmt(v)))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "({}: {})", vars_str, FrontFmt(self.0.ty.as_ref()))
    }
}

impl<'a> Display for FrontFmt<'a, Box<SExp>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        FrontFmt(self.0.as_ref()).fmt(f)
    }
}

impl<'a> Display for FrontFmt<'a, Box<Module>> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        FrontFmt(self.0.as_ref()).fmt(f)
    }
}

impl<'a> Display for FrontFmt<'a, SExp> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            SExp::AccessPath { access, parameters } => {
                write!(f, "{}", FrontFmt(access))?;
                if !parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", FrontFmt(param))?;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            SExp::AssociatedAccess { base, field } => {
                write!(f, "{}#{}", FrontFmt(base), FrontFmt(field))
            }
            SExp::MathMacro { .. } => todo!(),
            SExp::NamedMacro { .. } => todo!(),
            SExp::Where { exp, clauses } => {
                write!(f, "where {} {{ ", FrontFmt(exp))?;
                for (var, ty, body) in clauses {
                    write!(
                        f,
                        "{}: {} := {}; ",
                        FrontFmt(var),
                        FrontFmt(ty),
                        FrontFmt(body)
                    )?;
                }
                write!(f, "}}")
            }
            SExp::WithProofs { exp, proofs } => {
                write!(f, "with_proofs {} {{ ", FrontFmt(exp))?;
                for proof in proofs {
                    write!(f, "{:?} ", proof)?;
                }
                write!(f, "}}")
            }
            SExp::Sort(sort) => write!(f, "{:?}", sort),
            SExp::Prod { bind, body } | SExp::Lam { bind, body } => {
                let is_prod = matches!(self.0, SExp::Prod { .. });
                match bind {
                    Bind::Named(right_bind) => {
                        let vars_str = right_bind
                            .vars
                            .iter()
                            .map(|v| format!("{}", FrontFmt(v)))
                            .collect::<Vec<_>>()
                            .join(", ");
                        if is_prod {
                            write!(
                                f,
                                "({}: {}) -> {}",
                                vars_str,
                                FrontFmt(right_bind.ty.as_ref()),
                                FrontFmt(body)
                            )
                        } else {
                            write!(
                                f,
                                "({}: {}) => {}",
                                vars_str,
                                FrontFmt(right_bind.ty.as_ref()),
                                FrontFmt(body)
                            )
                        }
                    }
                    Bind::Subset { var, ty, predicate } => {
                        if is_prod {
                            write!(
                                f,
                                "({}: {} | {}) -> {}",
                                FrontFmt(var),
                                FrontFmt(ty),
                                FrontFmt(predicate),
                                FrontFmt(body)
                            )
                        } else {
                            write!(
                                f,
                                "({}: {} | {}) => {}",
                                FrontFmt(var),
                                FrontFmt(ty),
                                FrontFmt(predicate),
                                FrontFmt(body)
                            )
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
                                FrontFmt(var),
                                FrontFmt(ty),
                                FrontFmt(predicate),
                                FrontFmt(proof_var),
                                FrontFmt(body)
                            )
                        } else {
                            write!(
                                f,
                                "({}: {} | {}: {}) => {}",
                                FrontFmt(var),
                                FrontFmt(ty),
                                FrontFmt(predicate),
                                FrontFmt(proof_var),
                                FrontFmt(body)
                            )
                        }
                    }
                }
            }
            SExp::App { func, arg, piped } => {
                if *piped {
                    write!(f, "{} | {}", FrontFmt(func), FrontFmt(arg))
                } else {
                    write!(f, "{} {}", FrontFmt(func), FrontFmt(arg))
                }
            }
            SExp::Cast { exp, to } => write!(f, "{} \\as {}", FrontFmt(exp), FrontFmt(to)),
            SExp::IndElim {
                path,
                elim,
                return_type,
                cases,
            } => {
                write!(f, "ind_elim {}", FrontFmt(path))?;
                write!(f, "elim: {}, ", FrontFmt(elim))?;
                write!(f, "return_type: {}, ", FrontFmt(return_type))?;
                write!(f, " {{")?;
                for (ctor_name, case) in cases {
                    write!(f, "| {} => {} ; ", FrontFmt(ctor_name), FrontFmt(case))?;
                }
                write!(f, "}}")
            }
            SExp::IndElimPrim {
                path,
                parameters,
                sort,
            } => {
                write!(f, "ind_elim_prim {}[", FrontFmt(path))?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", FrontFmt(param))?;
                }
                write!(f, "] : {}", for_kernel::format_sort(sort))
            }
            SExp::RecordTypeCtor {
                access,
                parameters,
                fields,
            } => {
                write!(f, "{}[", FrontFmt(access))?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", FrontFmt(param))?;
                }
                write!(f, "] {{ ")?;
                for (field_name, field_type) in fields {
                    write!(f, "{}: {}; ", FrontFmt(field_name), FrontFmt(field_type))?;
                }
                write!(f, "}}")
            }
            SExp::ProveLater { prop } => write!(f, "prove_later {}", FrontFmt(prop)),
            SExp::PowerSet { set } => write!(f, "PowerSet({})", FrontFmt(set)),
            SExp::SubSet {
                var,
                set,
                predicate,
            } => write!(
                f,
                "{{ {} : {} | {} }}",
                FrontFmt(var),
                FrontFmt(set),
                FrontFmt(predicate)
            ),
            SExp::Pred {
                superset,
                subset,
                element,
            } => write!(
                f,
                "Pred({}, {}, {})",
                FrontFmt(superset),
                FrontFmt(subset),
                FrontFmt(element)
            ),
            SExp::TypeLift { superset, subset } => {
                write!(f, "TypeLift({}, {})", FrontFmt(superset), FrontFmt(subset))
            }
            SExp::Equal { left, right } => write!(f, "{} == {}", FrontFmt(left), FrontFmt(right)),
            SExp::Exists { bind } => match bind {
                Bind::Named(right_bind) => {
                    let vars_str = right_bind
                        .vars
                        .iter()
                        .map(|v| format!("{}", FrontFmt(v)))
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(
                        f,
                        "exists ({}: {}). ",
                        vars_str,
                        FrontFmt(right_bind.ty.as_ref())
                    )
                }
                Bind::Subset { var, ty, predicate } => write!(
                    f,
                    "exists ({}: {} | {}). ",
                    FrontFmt(var),
                    FrontFmt(ty),
                    FrontFmt(predicate)
                ),
                Bind::SubsetWithProof {
                    var,
                    ty,
                    predicate,
                    proof_var,
                } => write!(
                    f,
                    "exists ({}: {} | {}: {}). ",
                    FrontFmt(var),
                    FrontFmt(ty),
                    FrontFmt(predicate),
                    FrontFmt(proof_var)
                ),
            },
            SExp::Take { bind, body } => match bind {
                Bind::Named(right_bind) => {
                    let vars_str = right_bind
                        .vars
                        .iter()
                        .map(|v| format!("{}", FrontFmt(v)))
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(
                        f,
                        "\\take ({}: {}) => {}",
                        vars_str,
                        FrontFmt(right_bind.ty.as_ref()),
                        FrontFmt(body)
                    )
                }
                Bind::Subset { var, ty, predicate } => write!(
                    f,
                    "\\take ({}: {} | {}) => {}",
                    FrontFmt(var),
                    FrontFmt(ty),
                    FrontFmt(predicate),
                    FrontFmt(body)
                ),
                Bind::SubsetWithProof {
                    var,
                    ty,
                    predicate,
                    proof_var,
                } => write!(
                    f,
                    "\\take ({}: {} | {}: {}) => {}",
                    FrontFmt(var),
                    FrontFmt(ty),
                    FrontFmt(predicate),
                    FrontFmt(proof_var),
                    FrontFmt(body)
                ),
            },
            SExp::ProofTermRaw(sprove_command_by) => write!(f, "{}", FrontFmt(sprove_command_by)),
            SExp::Block(block) => {
                write!(f, "\\block {{ ")?;
                let Block { statements, result } = block;
                for stmt in statements {
                    write!(f, "{}; ", FrontFmt(stmt))?;
                }
                write!(f, "return {}; }}", FrontFmt(result))
            }
        }
    }
}

impl<'a> Display for FrontFmt<'a, SProveCommandBy> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            SProveCommandBy::Construct { term } => write!(f, "\\construct {}", FrontFmt(term)),
            SProveCommandBy::Exact { term, set } => {
                write!(f, "\\exact {} : {}", FrontFmt(term), FrontFmt(set))
            }
            SProveCommandBy::SubsetElim {
                superset,
                subset,
                elem,
            } => write!(
                f,
                "\\subset_elim {}, {}, {}",
                FrontFmt(superset),
                FrontFmt(subset),
                FrontFmt(elem)
            ),
            SProveCommandBy::IdRefl { term } => write!(f, "\\id_refl {}", FrontFmt(term)),
            SProveCommandBy::IdElim {
                left,
                right,
                var,
                ty,
                predicate,
            } => write!(
                f,
                "\\id_elim {}, {}, {}, {}, {}",
                FrontFmt(left),
                FrontFmt(right),
                FrontFmt(var),
                FrontFmt(ty),
                FrontFmt(predicate)
            ),
            SProveCommandBy::TakeEq {
                func,
                elem,
                domain,
                codomain,
            } => write!(
                f,
                "\\take_eq {}, {}, {}, {}",
                FrontFmt(func),
                FrontFmt(elem),
                FrontFmt(domain),
                FrontFmt(codomain)
            ),
            SProveCommandBy::Axiom(axiom) => write!(f, "\\axiom {:?}", axiom),
        }
    }
}

impl<'a> Display for FrontFmt<'a, Statement> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Statement::Fix(right_binds) => {
                let binds_str = right_binds
                    .iter()
                    .map(|bind| format!("{}", FrontFmt(bind)))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "\\fix {}", binds_str)
            }
            Statement::Let { var, ty, body } => {
                write!(
                    f,
                    "\\let {}: {} := {}",
                    FrontFmt(var),
                    FrontFmt(ty),
                    FrontFmt(body)
                )
            }
            Statement::Take { bind } => match bind {
                Bind::Named(right_bind) => {
                    let vars_str = right_bind
                        .vars
                        .iter()
                        .map(|v| format!("{}", FrontFmt(v)))
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(
                        f,
                        "\\take ({}: {}) ",
                        vars_str,
                        FrontFmt(right_bind.ty.as_ref())
                    )
                }
                Bind::Subset { var, ty, predicate } => write!(
                    f,
                    "\\take ({}: {} | {}) ",
                    FrontFmt(var),
                    FrontFmt(ty),
                    FrontFmt(predicate)
                ),
                Bind::SubsetWithProof {
                    var,
                    ty,
                    predicate,
                    proof_var,
                } => write!(
                    f,
                    "\\take ({}: {} | {}: {}) ",
                    FrontFmt(var),
                    FrontFmt(ty),
                    FrontFmt(predicate),
                    FrontFmt(proof_var)
                ),
            },
            Statement::Sufficient { map, map_ty } => {
                write!(f, "\\sufficient {}: {}", FrontFmt(map), FrontFmt(map_ty))
            }
        }
    }
}

impl<'a> Display for FrontFmt<'a, ModuleItem> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            ModuleItem::Definition { name, ty, body } => {
                write!(
                    f,
                    "\\def {}: {} := {}",
                    FrontFmt(name),
                    FrontFmt(ty),
                    FrontFmt(body)
                )
            }
            ModuleItem::Inductive {
                type_name,
                parameters,
                indices,
                sort,
                constructors,
            } => {
                write!(f, "\\inductive {}[", FrontFmt(type_name))?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", FrontFmt(param))?;
                }
                write!(f, "] (")?;
                for (i, index) in indices.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", FrontFmt(index))?;
                }
                write!(f, ") : {} {{ ", for_kernel::format_sort(sort))?;
                for (ctor_name, rightbinds, end) in constructors {
                    write!(f, "| {}: ", FrontFmt(ctor_name))?;
                    display_vec_rightbinds(rightbinds, f)?;
                    write!(f, " -> {}; ", FrontFmt(end))?;
                }
                write!(f, "}}")
            }
            ModuleItem::Record {
                type_name,
                parameters,
                sort,
                fields,
            } => {
                write!(f, "\\record {}[", FrontFmt(type_name))?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", FrontFmt(param))?;
                }
                write!(f, "] : {} {{ ", for_kernel::format_sort(sort))?;
                for (field_name, field_type) in fields {
                    write!(f, "{}: {}; ", FrontFmt(field_name), FrontFmt(field_type))?;
                }
                write!(f, "}}")
            }
            ModuleItem::ChildModule { module } => write!(f, "{}", FrontFmt(module)),
            ModuleItem::Import { path, import_name } => {
                write!(f, "\\import {:?} as {}", path, FrontFmt(import_name))
            }
            ModuleItem::MathMacro { .. } => todo!(),
            ModuleItem::UserMacro { .. } => todo!(),
            ModuleItem::Eval { exp } => write!(f, "\\eval {}", FrontFmt(exp)),
            ModuleItem::Normalize { exp } => write!(f, "\\normalize {}", FrontFmt(exp)),
            ModuleItem::Check { exp, ty } => {
                write!(f, "\\check {} : {}", FrontFmt(exp), FrontFmt(ty))
            }
            ModuleItem::Infer { exp } => write!(f, "\\infer {}", FrontFmt(exp)),
        }
    }
}

impl<'a> Display for FrontFmt<'a, Module> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let Module {
            name,
            parameters,
            declarations,
        } = self.0;
        write!(f, "\\module {}", FrontFmt(name))?;
        display_vec_rightbinds(parameters, f)?;
        write!(f, " {{ ")?;
        for decl in declarations {
            write!(f, "{}; ", FrontFmt(decl))?;
        }
        write!(f, "}}")
    }
}

impl<'a> Display for FrontFmt<'a, ModItemDefinition> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let defined_const = self.0.body.as_ref();
        write!(
            f,
            "\\def {}: {} := {}",
            FrontFmt(&self.0.def_name),
            for_kernel::format_exp(&defined_const.ty),
            for_kernel::format_exp(&defined_const.body)
        )
    }
}

impl<'a> Display for FrontFmt<'a, ModItemInductive> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "\\inductive {} {:?} := {:?}",
            FrontFmt(&self.0.type_name),
            self.0.ctor_names,
            self.0.ind_defs
        )
    }
}

impl<'a> Display for FrontFmt<'a, ModItemRecord> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "\\record {} := {:?}",
            FrontFmt(&self.0.type_name),
            self.0.rc_spec_as_indtype
        )
    }
}

impl<'a> Display for FrontFmt<'a, ModuleItemAccessible> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            ModuleItemAccessible::Definition(mod_item_definition) => {
                write!(f, "{}", FrontFmt(mod_item_definition))
            }
            ModuleItemAccessible::Inductive(mod_item_inductive) => {
                write!(f, "{}", FrontFmt(mod_item_inductive))
            }
            ModuleItemAccessible::Record(mod_item_record) => {
                write!(f, "{}", FrontFmt(mod_item_record))
            }
        }
    }
}

impl<'a> Display for FrontFmt<'a, InstantiatedModule> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let InstantiatedModule {
            parameters_instantiated,
            items,
        } = self.0;
        write!(f, "Instantiated Module {{ ")?;
        write!(f, "(")?;
        for (param, inst) in parameters_instantiated {
            write!(
                f,
                "{} := {}; ",
                param.as_str(),
                for_kernel::format_exp(inst)
            )?;
        }
        write!(f, ") ")?;
        for item in items {
            write!(f, "{}; ", FrontFmt(item))?;
        }
        write!(f, "}}")
    }
}

impl<'a> Display for FrontFmt<'a, ItemAccessResult> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            ItemAccessResult::Definition(mod_item_definition) => {
                write!(f, "{}", FrontFmt(mod_item_definition))
            }
            ItemAccessResult::Inductive(mod_item_inductive) => {
                write!(f, "{}", FrontFmt(mod_item_inductive))
            }
            ItemAccessResult::Record(mod_item_record) => {
                write!(f, "{}", FrontFmt(mod_item_record))
            }
            ItemAccessResult::Expression(exp) => write!(f, "{}", for_kernel::format_exp(exp)),
        }
    }
}

impl<'a> Display for FrontFmt<'a, ModuleManager> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "ModuleManager")?;
        let current = self.0.current_index();
        for (i, module_elaborated) in self.0.modules().iter().enumerate() {
            writeln!(
                f,
                "{}{} ",
                if current == i { "**" } else { "  " },
                FrontFmt(module_elaborated)
            )?;
        }
        write!(f, "}}")
    }
}

impl<'a> Display for FrontFmt<'a, ModuleElaborated> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let ModuleElaborated {
            name,
            parameters,
            items,
            child_modules,
            parent_module,
            imports,
        } = self.0;
        write!(f, "ModuleElaborated {{ name: {}, ", name)?;

        write!(f, "parameters: [")?;
        for (i, (var, ty)) in parameters.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", var.as_str(), for_kernel::format_exp(ty))?;
        }
        write!(f, "], ")?;

        write!(f, "items: [")?;
        for (i, item) in items.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", FrontFmt(item))?;
        }
        write!(f, "], ")?;

        write!(f, "imports: [")?;
        for (i, (import_name, instantiated_module)) in imports.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(
                f,
                "{} := {}",
                FrontFmt(import_name),
                FrontFmt(instantiated_module)
            )?;
        }
        write!(f, "], ")?;

        write!(f, "child_modules: [")?;
        for (i, child) in child_modules.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{child}")?;
        }
        write!(f, "], ")?;

        write!(f, "parent_module: {:?} ", parent_module)?;
        write!(f, "}}")
    }
}

fn display_vec_rightbinds(binds: &[RightBind], f: &mut Formatter<'_>) -> fmt::Result {
    for (i, bind) in binds.iter().enumerate() {
        if i > 0 {
            write!(f, " -> ")?;
        }
        write!(f, "{}", FrontFmt(bind))?;
    }
    Ok(())
}
