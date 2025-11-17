use std::fmt::Display;

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
                    Bind::Anonymous { ty } => {
                        if is_prod {
                            write!(f, "{} -> {}", ty, body)
                        } else {
                            write!(f, "{} => {}", ty, body)
                        }
                    }
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
                Bind::Anonymous { ty } => {
                    write!(f, "exists {}. ", ty)
                }
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
                Bind::Anonymous { ty } => {
                    write!(f, "\\take {} => {}", ty, body)
                }
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
                Bind::Anonymous { ty } => {
                    write!(f, "\\take {} ", ty)
                }
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
