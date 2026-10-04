use super::*;

impl Resolver {
    pub(in crate::resolver) fn normalize_structures(
        &mut self,
        expression: &mut SExp,
        locals: &[HashMap<String, Identifier>],
    ) -> Result<(), Diagnostic> {
        let mut error = None;
        macros::walk_sexp_control(expression, &mut |node| {
            if error.is_some() {
                return false;
            }
            let expansion = match node {
                SExp::Block(block)
                    if block
                        .statements
                        .iter()
                        .any(|statement| matches!(statement, Statement::TakeFrom { .. })) =>
                {
                    Some(block.as_term().map_err(|e| self.error(e)))
                }
                SExp::Exists {
                    bind: Bind::Named(bind),
                } if self.is_structure_type(&bind.ty) => {
                    Some(Ok(self.structure_existence(&bind.ty)))
                }
                SExp::ExistsIntro { element, set } if self.is_structure_type(set) => {
                    Some(self.structure_exists_intro(set, element, locals))
                }
                SExp::TakeProp {
                    bind: Bind::Named(bind),
                    body,
                    existence,
                } if self.is_structure_type(&bind.ty) => {
                    if bind.vars.len() != 1 {
                        Some(Err(
                            self.error("existential elimination requires one witness")
                        ))
                    } else {
                        Some(Ok(self.structure_exists_elim(bind, body, existence)))
                    }
                }
                _ => None,
            };
            if let Some(expansion) = expansion {
                match expansion {
                    Ok(mut expression) => {
                        if let Err(e) = self.normalize_structures(&mut expression, locals) {
                            error = Some(e);
                        } else {
                            *node = expression;
                        }
                    }
                    Err(e) => error = Some(e),
                }
                return false;
            }
            if let SExp::AccessPath { access, parameters } = node
                && parameters.is_empty()
                && let Some(id) = self.front_binding(access, locals)
                && self.computation_bindings.contains(&id)
            {
                let mut access = access.clone();
                let reflected = match &mut access {
                    LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. } => {
                        let reflected = access.0.ends_with('^');
                        access.0 = access.0.trim_end_matches('^').to_owned();
                        reflected
                    }
                    LocalAccess::Named { child, .. } => {
                        let reflected = child.0.ends_with('^');
                        child.0 = child.0.trim_end_matches('^').to_owned();
                        reflected
                    }
                };
                let value = SExp::Force {
                    value: Box::new(SExp::ProgramValueReference { access }),
                };
                *node = if reflected {
                    SExp::ReflectTerm {
                        expression: Box::new(value),
                    }
                } else {
                    value
                };
                return false;
            }
            if let SExp::MemberLiteral { ty, fields } = node {
                if let Err(e) = self.normalize_structures(ty, locals) {
                    error = Some(e);
                    return false;
                }
                let SExp::AccessPath { access, parameters } = ty.as_ref() else {
                    error = Some(self.error("expected a structure type before a literal"));
                    return false;
                };
                *node = SExp::RecordTypeCtor {
                    access: access.clone(),
                    parameters: parameters.clone(),
                    fields: fields.clone(),
                };
            }
            if let SExp::AssociatedAccess { base, field, span } = node {
                if let Err(e) = self.normalize_structures(base, locals) {
                    error = Some(e);
                    return false;
                }
                let mut body = (**base).clone();
                let mut checks = Vec::new();
                while let SExp::Checked {
                    checks: inner,
                    body: value,
                } = body
                {
                    checks.extend(inner);
                    body = *value;
                }
                let result = SExp::AssociatedAccess {
                    base: Box::new(body),
                    field: field.clone(),
                    span: *span,
                };
                *node = if checks.is_empty() {
                    result
                } else {
                    SExp::Checked {
                        checks,
                        body: Box::new(result),
                    }
                };
            }
            if matches!(
                node,
                SExp::Prod {
                    bind: Bind::Named(_),
                    ..
                } | SExp::Lam {
                    bind: Bind::Named(_),
                    ..
                }
            ) {
                let lambda = matches!(node, SExp::Lam { .. });
                let (SExp::Prod {
                    bind: Bind::Named(bind),
                    body,
                }
                | SExp::Lam {
                    bind: Bind::Named(bind),
                    body,
                }) = node
                else {
                    unreachable!()
                };
                let mut scope = locals.to_vec();
                let mut parameters = vec![bind.clone()];
                if self.structure_type(&bind.ty).is_some() {
                    if let Err(e) =
                        self.expand_structure_parameters(&mut parameters, &mut scope, false)
                    {
                        error = Some(e);
                        return false;
                    }
                } else {
                    if let Err(e) = self.normalize_structures(&mut parameters[0].ty, &scope) {
                        error = Some(e);
                        return false;
                    }
                    let mut names = HashMap::new();
                    for name in &mut parameters[0].vars {
                        if name.1.is_none() {
                            self.binding(name);
                        }
                        names.insert(name.0.clone(), name.clone());
                    }
                    scope.push(names);
                }
                let parameter_checks = self.last_parameter_checks.clone();
                if let Err(e) = self.normalize_structures(body, &scope) {
                    error = Some(e);
                    return false;
                }
                let mut result = (**body).clone();
                if self.structure_type(&bind.ty).is_some() && !parameter_checks.is_empty() {
                    result = SExp::Checked {
                        checks: parameter_checks,
                        body: Box::new(result),
                    };
                }
                for bind in parameters.into_iter().rev() {
                    result = if lambda {
                        SExp::Lam {
                            bind: Bind::Named(bind),
                            body: Box::new(result),
                        }
                    } else {
                        SExp::Prod {
                            bind: Bind::Named(bind),
                            body: Box::new(result),
                        }
                    };
                }
                *node = result;
                return false;
            }
            let projected = match node {
                SExp::AccessPath {
                    access:
                        LocalAccess::Named {
                            access,
                            child,
                            span,
                        },
                    parameters,
                } => Some((
                    variable(access.clone()),
                    child.clone(),
                    parameters.clone(),
                    *span,
                )),
                SExp::InferredProjection { value, field, span } => {
                    Some(((**value).clone(), field.clone(), Vec::new(), *span))
                }
                SExp::MemberAccess {
                    base,
                    field,
                    parameters,
                    span,
                } => Some(((**base).clone(), field.clone(), parameters.clone(), *span)),
                _ => None,
            };
            if let Some((base, field, parameters, span)) = projected {
                match self.structure_value(&base, locals) {
                    Ok(Some(value)) => {
                        if let Some(location) = &self.location
                            && span.end > span.start
                            && let Some(binding) = self.global_bindings.get(&value.signature)
                        {
                            self.references.borrow_mut().push(Reference {
                                module: self.path(self.current),
                                location: SourceLocation {
                                    source: location.source.clone(),
                                    span,
                                },
                                target_module: self.path(binding.module),
                                target_name: format!(
                                    "{}::{}",
                                    binding.name,
                                    field.as_str().trim_end_matches('^')
                                ),
                            });
                        }
                        if !value.parameters.is_empty() {
                            error = Some(
                                self.error("structure declaration needs its remaining arguments"),
                            );
                            return false;
                        }
                        if let Some((_, expression)) = value
                            .fields
                            .iter()
                            .find(|(name, _)| name == field.as_str().trim_end_matches('^'))
                        {
                            let expression = if field.as_str().ends_with('^') {
                                let is_type =
                                    self.structures.get(&value.signature).is_some_and(|shape| {
                                        shape.fields.iter().any(|(name, ty, _)| {
                                            name.as_str() == field.as_str().trim_end_matches('^')
                                                && matches!(ty, SExp::ValueType)
                                        })
                                    });
                                if is_type {
                                    match self.reflect_type(expression.clone()) {
                                        Ok(expression) => expression,
                                        Err(e) => {
                                            error = Some(e);
                                            return false;
                                        }
                                    }
                                } else {
                                    SExp::ReflectTerm {
                                        expression: Box::new(expression.clone()),
                                    }
                                }
                            } else {
                                expression.clone()
                            };
                            let mut expression = expression;
                            for argument in &parameters {
                                expression = SExp::App {
                                    func: Box::new(expression),
                                    arg: Box::new(argument.clone()),
                                };
                            }
                            *node = if value.checks.is_empty() {
                                expression.clone()
                            } else {
                                SExp::Checked {
                                    checks: value.checks.clone(),
                                    body: Box::new(expression.clone()),
                                }
                            };
                        } else {
                            error =
                                Some(self.error(format!("unknown structure field: {}", field.0)));
                        }
                    }
                    Err(e) => error = Some(e),
                    _ => {
                        if matches!(node, SExp::MemberAccess { .. })
                            || matches!(&base, SExp::AccessPath { access, .. } if self.front_binding(access, locals).is_some())
                        {
                            let mut result = SExp::InferredProjection {
                                value: Box::new(base),
                                field,
                                span,
                            };
                            for argument in parameters {
                                result = SExp::App {
                                    func: Box::new(result),
                                    arg: Box::new(argument),
                                };
                            }
                            *node = result;
                        }
                    }
                }
            }
            let mut arguments = Vec::new();
            let mut head = &*node;
            while let SExp::App { func, arg } = head {
                arguments.push((**arg).clone());
                head = func;
            }
            arguments.reverse();
            if let SExp::AccessPath { access, parameters } = head
                && let Some(id) = self.front_binding(access, locals)
                && let Some(definition) = self.front_definitions.get(&id).cloned()
            {
                let mut definition = definition;
                for input in &mut definition.inputs {
                    self.instantiate_input(input, access);
                }
                definition.body = self.instantiate_front_expression(&definition.body, access);
                definition.ty = self.instantiate_front_expression(&definition.ty, access);
                for bind in &mut definition.parameters {
                    *bind.ty = self.instantiate_front_expression(&bind.ty, access);
                }
                let mut supplied = parameters.clone();
                supplied.extend(arguments.clone());
                {
                    let mut actual = Vec::new();
                    let mut checks = Vec::new();
                    for (input, argument) in definition.inputs.iter().zip(&supplied) {
                        if input.signature.is_some() {
                            match self.callback_arguments(input, argument, locals) {
                                Ok((fields, guards)) => {
                                    actual.extend(fields);
                                    checks.extend(guards);
                                }
                                Err(e) => {
                                    error = Some(e);
                                    return false;
                                }
                            }
                        } else {
                            actual.push(if input.computation {
                                thunk(argument.clone())
                            } else {
                                argument.clone()
                            });
                        }
                    }
                    let consumed = actual.len();
                    let mut substitutions = HashMap::new();
                    for (bind, value) in definition.parameters.iter().zip(actual) {
                        checks.push((value.clone(), substitute(&bind.ty, &substitutions)));
                        substitutions.insert(bind.vars[0].1.unwrap(), value);
                    }
                    checks = checks
                        .into_iter()
                        .map(|(value, ty)| {
                            (
                                substitute(&value, &substitutions),
                                substitute(&ty, &substitutions),
                            )
                        })
                        .collect();
                    let remaining: Vec<_> = definition
                        .parameters
                        .iter()
                        .skip(consumed)
                        .map(|bind| RightBind {
                            vars: bind.vars.clone(),
                            ty: Box::new(substitute(&bind.ty, &substitutions)),
                        })
                        .collect();
                    let body = substitute(&definition.body, &substitutions);
                    let ty = substitute(&definition.ty, &substitutions);
                    checks.push((body.clone(), ty));
                    let reflected = match access {
                        LocalAccess::Current { access, .. }
                        | LocalAccess::Resolved { access, .. } => access.as_str().ends_with('^'),
                        LocalAccess::Named { child, .. } => child.as_str().ends_with('^'),
                    };
                    let mut result = abstract_parameters(
                        &remaining,
                        SExp::Checked {
                            checks,
                            body: Box::new(body),
                        },
                    );
                    if reflected {
                        result = SExp::ReflectTerm {
                            expression: Box::new(result),
                        };
                    }
                    for argument in supplied.into_iter().skip(definition.inputs.len()) {
                        result = SExp::App {
                            func: Box::new(result),
                            arg: Box::new(argument),
                        };
                    }
                    *node = result;
                    return true;
                }
            }
            true
        });
        error.map_or(Ok(()), Err)
    }
}
