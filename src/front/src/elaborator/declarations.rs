//! Validate declarations and generate record projections and datatype mirrors.
use super::*;

impl GlobalEnvironment {
    pub(super) fn program_associated_scope(
        &mut self,
        owner: Option<&AssociatedOwner>,
    ) -> Result<(program_term_elaborator::ProgramScope, Vec<SymbolId>), String> {
        let mut scope = program_term_elaborator::ProgramScope::new();
        let Some(owner) = owner else {
            return Ok((scope, Vec::new()));
        };
        let access = LocalAccess::Current {
            access: owner.type_name.clone(),
        };
        let Some(module_manager::ItemAccessResult::ProgramInductive(item)) =
            self.module_manager.get_item(&self.crate_env, &access)
        else {
            return Err(
                "Program associated item owner must be a Program type in this module".into(),
            );
        };
        if item.inductive.module != self.module_manager.current() {
            return Err("Program associated item owner must be in this module".into());
        }
        let expected = self
            .crate_env
            .program_inductive(item.inductive)
            .parameters()
            .len();
        let mut names = Vec::new();
        for binder in &owner.parameters {
            if !matches!(binder.ty.as_ref(), SExp::ValueType) {
                return Err("Program associated item parameters must have type \\VType".into());
            }
            for name in &binder.vars {
                let symbol = self.crate_env.intern(name.as_str());
                if names.contains(&symbol) {
                    return Err("duplicate Program associated item parameter".into());
                }
                names.push(symbol);
                scope.push_type(symbol);
            }
        }
        if names.len() != expected {
            return Err(format!(
                "Program associated item expects {expected} owner parameter(s), found {}",
                names.len()
            ));
        }
        Ok((scope, names))
    }

    pub(super) fn publish_program_definition(
        &mut self,
        owner: Option<&AssociatedOwner>,
        name: Identifier,
        parameters: Vec<SymbolId>,
        definition: DefinedConstant,
    ) -> Result<(), String> {
        if let Some(owner) = owner {
            let id = self.crate_env.add_parameterized_definition(
                self.module_manager.current(),
                definition,
                parameters,
            )?;
            self.crate_env.publish_associated_definition(
                self.module_manager.current(),
                owner.type_name.as_str(),
                name.0,
                id,
            )
        } else {
            self.module_manager
                .add_def(&mut self.crate_env, name, definition)
        }
    }

    pub(super) fn add_program_record_decl(
        &mut self,
        type_name: &Identifier,
        parameters: &[RightBind],
        fields: &[(Identifier, SExp)],
    ) -> Result<(), ElaborationError> {
        use crate::raw::program::*;
        let mut names = Vec::new();
        for (name, _) in fields {
            if names.contains(&name.0) {
                return Err(format!("duplicate record field name: {}", name.0).into());
            }
            names.push(name.0.clone());
        }
        let constructor = (
            Identifier("<record>".into()),
            fields
                .iter()
                .map(|(name, ty)| RightBind {
                    vars: vec![name.clone()],
                    ty: Box::new(ty.clone()),
                })
                .collect(),
            SExp::AccessPath {
                access: LocalAccess::Current {
                    access: type_name.clone(),
                },
                parameters: Vec::new(),
            },
        );
        self.add_typed_program_inductive_decl(type_name, parameters, &[constructor], Some(names))?;
        let Some(module_manager::ItemAccessResult::ProgramInductive(item)) =
            self.module_manager.get_item(
                &self.crate_env,
                &LocalAccess::Current {
                    access: type_name.clone(),
                },
            )
        else {
            unreachable!()
        };
        let spec = self.crate_env.program_inductive(item.inductive).clone();
        let parameter_names = spec.parameters().to_vec();
        let fields = spec.constructors()[0].fields().to_vec();
        let structure = self.crate_env.intern("structure");
        for (index, (field_name, field_ty)) in fields.iter().enumerate() {
            let arena = self.crate_env.arena();
            let ty = arena.alloc(ComputationTypeNode::Function {
                domain: arena.alloc(ValueTypeNode::Inductive {
                    indspec: item.inductive,
                    parameters: (0..parameter_names.len())
                        .rev()
                        .map(|i| arena.value_type_bound(i))
                        .collect(),
                }),
                codomain: arena.alloc(ComputationTypeNode::Return {
                    value_ty: *field_ty,
                }),
            });
            let ComputationTypeNode::Function { domain, .. } = arena.get(ty) else {
                unreachable!()
            };
            let body = arena.alloc(ComputationTermNode::Lambda {
                var: structure,
                value_ty: domain,
                body: arena.alloc(ComputationTermNode::Case {
                    indspec: item.inductive,
                    scrutinee: arena.value_bound(0),
                    branches: vec![ProgramCaseBranch {
                        binders: fields.iter().map(|(name, _)| *name).collect(),
                        body: arena.alloc(ComputationTermNode::Return {
                            value: arena.value_bound(fields.len() - 1 - index),
                        }),
                    }],
                }),
            });
            let name = self.crate_env.symbol(*field_name).to_owned();
            let definition = self.crate_env.add_parameterized_definition(
                self.module_manager.current(),
                DefinedConstant::ProgramComputation {
                    ty,
                    body,
                    certified_reflection: None,
                },
                parameter_names.clone(),
            )?;
            self.crate_env.publish_associated_definition(
                self.module_manager.current(),
                type_name.as_str(),
                name,
                definition,
            )?;
        }
        Ok(())
    }

    pub(super) fn validate_definition(
        &self,
        context: &mut ExpContext,
        body: Exp,
        ty: Exp,
    ) -> Result<(), String> {
        CheckSession::new(&self.crate_env, self.module_manager.current(), context)
            .check_pts(body, ty)
            .map_err(|error| format!("Set/Prop definition check failed: {error:?}"))
    }

    pub(super) fn add_record_projection_definitions(
        &mut self,
        inductive: InductiveId,
    ) -> Result<Vec<(Identifier, DefId)>, ElaborationError> {
        let module = self.module_manager.current();
        let spec = self.crate_env.inductive(inductive).clone();
        let parameters = spec.parameters().to_vec();
        let field_count = spec.constructors()[0].telescope.len();
        let structure_var = self.crate_env.intern("structure");
        let mut projections = Vec::with_capacity(field_count);

        for field in 0..field_count {
            let preceding_ids = projections
                .iter()
                .map(|(_, definition)| *definition)
                .collect::<Vec<_>>();
            let (name, ty, body) = {
                let arena = self.crate_env.arena();
                let CtorBinder::Simple((field_name, _)) = &spec.constructors()[0].telescope[field]
                else {
                    return Err("record fields must be non-recursive".into());
                };
                let name = Identifier(self.crate_env.symbol(*field_name).to_owned());
                if projections.iter().any(|(existing, _)| existing == &name) {
                    return Err(format!("duplicate record field name: {}", name.as_str()).into());
                }
                let parameter_arguments = (0..parameters.len())
                    .rev()
                    .map(|index| arena.exp_bound(index))
                    .collect::<Vec<_>>();
                let record_ty = arena.alloc(ExpNode::IndType {
                    indspec: inductive,
                    parameters: parameter_arguments.clone(),
                });

                let parameters_under_value = parameter_arguments
                    .iter()
                    .map(|parameter| shift_bound_indices(arena, *parameter, 1, 0))
                    .collect::<Vec<_>>();
                let projected_ty = projected_record_field_type(
                    arena,
                    &spec,
                    field,
                    &parameters_under_value,
                    arena.exp_bound(0),
                    &preceding_ids,
                )?;
                let projection_ty = arena.alloc(ExpNode::Prod {
                    var: structure_var,
                    ty: record_ty,
                    body: projected_ty,
                });
                let ty = crate::raw::utils::assoc_prod(arena, parameters.clone(), projection_ty);

                let parameters_under_motive = parameters_under_value
                    .iter()
                    .map(|parameter| shift_bound_indices(arena, *parameter, 1, 0))
                    .collect::<Vec<_>>();
                let motive_record_ty = arena.alloc(ExpNode::IndType {
                    indspec: inductive,
                    parameters: parameters_under_value.clone(),
                });
                let motive_result = projected_record_field_type(
                    arena,
                    &spec,
                    field,
                    &parameters_under_motive,
                    arena.exp_bound(0),
                    &preceding_ids,
                )?;
                let motive = arena.alloc(ExpNode::Lam {
                    var: structure_var,
                    ty: motive_record_ty,
                    body: motive_result,
                });

                let constructor =
                    spec.constructors()[0].instantiate_parameters(arena, &parameters_under_value);
                let case_telescope = constructor
                    .telescope
                    .into_iter()
                    .map(|binder| match binder {
                        CtorBinder::Simple(binder) => Ok(binder),
                        CtorBinder::StrictPositive { .. } => {
                            Err("record fields must be non-recursive".to_string())
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let selected = arena.exp_bound(field_count - 1 - field);
                let case = crate::raw::utils::assoc_lam(arena, case_telescope, selected);
                let elimination = arena.alloc(ExpNode::IndElim {
                    indspec: inductive,
                    elim: arena.exp_bound(0),
                    return_type: motive,
                    cases: vec![case],
                });
                let projection = arena.alloc(ExpNode::Lam {
                    var: structure_var,
                    ty: record_ty,
                    body: elimination,
                });
                let body = crate::raw::utils::assoc_lam(arena, parameters.clone(), projection);
                (name, ty, body)
            };

            let mut context = self.module_manager.current_context(&self.crate_env);
            CheckSession::new(&self.crate_env, module, &mut context)
                .check_pts(body, ty)
                .map_err(|error| {
                    format!(
                        "Generated projection {} does not typecheck: {error:?}",
                        name.as_str()
                    )
                })?;
            let definition = self
                .crate_env
                .add_definition(module, DefinedConstant::Pts { ty, body })?;
            projections.push((name, definition));
        }

        Ok(projections)
    }

    pub(super) fn add_typed_program_inductive_decl(
        &mut self,
        type_name: &Identifier,
        parameters: &[RightBind],
        constructors: &[(Identifier, Vec<RightBind>, SExp)],
        record_fields: Option<Vec<String>>,
    ) -> Result<(), ElaborationError> {
        let module = self.module_manager.current();
        let inductive = self.crate_env.reserve_program_inductive(module);
        let reflected = self.crate_env.reserve_inductive(module);
        let type_name_symbol = self.crate_env.intern(type_name.as_str());
        let self_ty = self
            .crate_env
            .arena()
            .alloc(crate::raw::program::ValueTypeNode::Inductive {
                indspec: inductive,
                parameters: Vec::new(),
            });
        let mut scope = program_term_elaborator::ProgramScope::new();
        if record_fields.is_none() {
            scope.bind_value_type_name(type_name_symbol, self_ty);
        }

        let mut parameter_names = Vec::new();
        for RightBind { vars, ty } in parameters {
            if !matches!(ty.as_ref(), SExp::ValueType) {
                return Err("Program datatype parameters must have type \\VType".into());
            }
            for variable in vars {
                let variable = self.crate_env.intern(variable.as_str());
                parameter_names.push(variable);
                scope.push_type(variable);
            }
        }

        let mut constructor_names = Vec::new();
        let mut constructor_specs = Vec::new();
        for (constructor_name, fields, result) in constructors {
            if constructor_names
                .iter()
                .any(|existing: &Identifier| existing == constructor_name)
            {
                return Err(format!(
                    "duplicate Program constructor name: {}",
                    constructor_name.as_str()
                )
                .into());
            }
            constructor_names.push(constructor_name.clone());
            let mut elaborated_fields = Vec::new();
            for RightBind { vars, ty } in fields {
                let surface_ty: ValueTypeExp = ty.as_ref().clone().try_into()?;
                let field_ty = scope.elaborate_value_type(&surface_ty, self)?;
                if vars.is_empty() {
                    elaborated_fields.push((SymbolId::ANONYMOUS, field_ty));
                } else {
                    for variable in vars {
                        let variable = self.crate_env.intern(variable.as_str());
                        elaborated_fields.push((variable, field_ty));
                    }
                }
            }
            // A structure cannot refer to itself in fields; bind its result only now.
            if record_fields.is_some() {
                scope.bind_value_type_name(type_name_symbol, self_ty);
            }
            let result: ValueTypeExp = result.clone().try_into()?;
            let result = scope.elaborate_value_type(&result, self)?;
            let crate::raw::program::ValueTypeNode::Inductive {
                indspec,
                parameters,
            } = self.crate_env.arena().get(result)
            else {
                return Err(format!(
                    "Program constructor {} must return {}",
                    constructor_name.as_str(),
                    type_name.as_str()
                )
                .into());
            };
            let exact_parameters = parameters.is_empty()
                || (parameters.len() == parameter_names.len()
                    && parameters.iter().enumerate().all(|(index, parameter)| {
                        matches!(
                            self.crate_env.arena().get(*parameter),
                            crate::raw::program::ValueTypeNode::Bound(bound)
                                if bound == parameter_names.len() - 1 - index
                        )
                    }));
            if indspec != inductive || !exact_parameters {
                return Err(format!(
                    "Program constructor {} must return {} with all datatype parameters",
                    constructor_name.as_str(),
                    type_name.as_str()
                )
                .into());
            }
            constructor_specs.push(ProgramConstructorSpec::new(elaborated_fields));
        }

        let program_spec = ProgramInductiveTypeSpecs::unchecked(
            parameter_names.clone(),
            constructor_specs,
            reflected,
        );
        self.crate_env
            .define_program_inductive(inductive, program_spec);

        let reflected_parameters = parameter_names
            .iter()
            .map(|name| (*name, self.crate_env.arena().sort(Sort::Set(0))))
            .collect();
        let reflected_constructors = self.crate_env.program_inductive(inductive).constructors().iter().map(|constructor| {
            let telescope = constructor.fields().iter().enumerate().map(|(field_index, (name, ty))| {
                let ty = crate::raw::reflection::reflect_value_type(&self.crate_env, *ty)
                    .map_err(|error| format!("cannot reflect Program constructor field: {error}"))?;
                let ty = crate::raw::calculus::shift_bound_indices(
                    self.crate_env.arena(),
                    ty,
                    field_index,
                    0,
                );
                if !exp_contains_inductive(self.crate_env.arena(), ty, reflected) {
                    return Ok(CtorBinder::Simple((*name, ty)));
                }
                let (binders, tail) = crate::raw::utils::decompose_prod(self.crate_env.arena(), ty);
                let (head, self_indices) = crate::raw::utils::decompose_app(self.crate_env.arena(), tail);
                if !matches!(self.crate_env.arena().get(head), ExpNode::IndType { indspec, .. } if indspec == reflected) {
                    return Err("reflected recursive Program field is not strictly positive".to_string());
                }
                Ok(CtorBinder::StrictPositive { binders, self_indices })
            }).collect::<Result<Vec<_>, String>>()?;
            Ok(crate::raw::inductive::CtorType { telescope, indices: Vec::new() })
        }).collect::<Result<Vec<_>, String>>()?;
        self.crate_env.define_inductive(
            reflected,
            InductiveTypeSpecs::unchecked(
                reflected_parameters,
                Vec::new(),
                Sort::Set(0),
                reflected_constructors,
            ),
        );

        let mut program_context = self.module_manager.current_program_context(&self.crate_env);
        self.crate_env
            .program_inductive(inductive)
            .validate(
                &mut ProgramCheckSession::new(&self.crate_env, &mut program_context),
                inductive,
            )
            .map_err(|error| format!("Ill-formed Program datatype: {error:?}"))?;
        let mut reflected_context =
            crate::raw::reflection::reflect_context(&self.crate_env, &program_context)
                .map_err(|error| format!("cannot reflect Program context: {error}"))?;
        self.crate_env
            .inductive(reflected)
            .validate(
                &mut CheckSession::new(&self.crate_env, module, &mut reflected_context),
                reflected,
            )
            .map_err(|error| format!("Ill-formed reflected datatype: {error:?}"))?;
        self.module_manager.publish_reserved_program_inductive(
            &mut self.crate_env,
            type_name.clone(),
            constructor_names,
            inductive,
            reflected,
            record_fields,
        )?;
        Ok(())
    }
}
