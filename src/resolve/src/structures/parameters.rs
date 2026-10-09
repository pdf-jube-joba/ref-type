use super::*;

impl Resolver {
    pub(in crate::resolver) fn register_parameter_signature(
        &mut self,
        name: &Identifier,
        parameters: &[RightBind],
    ) {
        if self
            .last_inputs
            .iter()
            .any(|input| input.signature.is_some())
        {
            self.parameter_signatures.insert(
                name.1.unwrap(),
                ParameterSignature {
                    parameters: parameters.to_vec(),
                    inputs: self.last_inputs.clone(),
                    checks: self.last_parameter_checks.clone(),
                },
            );
        }
    }

    pub(in crate::resolver) fn expand_type_arguments(
        &self,
        parameters: &[RightBind],
        inputs: &[Input],
        supplied: &[SExp],
        access: &LocalAccess,
        locals: &[LocalScope],
    ) -> Result<(Vec<SExp>, Vec<(SExp, SExp)>), Diagnostic> {
        // Explicit field arguments remain useful when constructing a telescope.
        let flattened = supplied.len() == parameters.len();
        if supplied.len() != inputs.len() {
            if flattened {
                return Ok((supplied.to_vec(), Vec::new()));
            }
            return Err(self.error(format!(
                "structure argument count mismatch: expected {}, got {}",
                inputs.len(),
                supplied.len()
            )));
        }
        let mut actual = Vec::new();
        let mut checks = Vec::new();
        let mut substitutions = HashMap::new();
        for (input, argument) in inputs.iter().zip(supplied) {
            let mut input = input.clone();
            self.instantiate_input(&mut input, access);
            for value in input.arguments.values_mut() {
                *value = substitute(value, &substitutions);
            }
            let fields = if input.signature.is_some()
                && !(flattened && self.structure_value(argument, locals)?.is_none())
            {
                let (fields, guards) = self.callback_arguments(&input, argument, locals)?;
                checks.extend(guards);
                fields
            } else {
                vec![if input.computation {
                    thunk(argument.clone())
                } else {
                    argument.clone()
                }]
            };
            for field in fields {
                let parameter = &parameters[actual.len()];
                substitutions.insert(parameter.vars[0].1.unwrap(), field.clone());
                actual.push(field);
            }
            if input.signature.is_some() {
                self.bind_structure_field(input.binding, argument.clone(), &mut substitutions)?;
            }
        }
        Ok((actual, checks))
    }

    pub(in crate::resolver) fn declaration_signature(
        &self,
        ty: &SExp,
    ) -> Option<(Vec<RightBind>, SExp)> {
        let mut parameters = Vec::new();
        let mut result = ty;
        while let SExp::Prod {
            bind: Bind::Named(bind),
            body,
        } = result
        {
            parameters.push(bind);
            result = body;
        }
        if parameters.is_empty() || !self.is_structure_type(result) {
            return None;
        }
        let parameters = parameters
            .into_iter()
            .enumerate()
            .map(|(index, bind)| {
                let mut bind = bind.clone();
                if bind.vars.is_empty() {
                    bind.vars.push(Identifier(format!("<argument:{index}>")));
                }
                bind
            })
            .collect();
        Some((parameters, result.clone()))
    }

    pub(in crate::resolver) fn callback_arguments(
        &self,
        input: &Input,
        argument: &SExp,
        locals: &[LocalScope],
    ) -> Result<(Vec<SExp>, Vec<(SExp, SExp)>), Diagnostic> {
        let value = self
            .structure_value(argument, locals)?
            .filter(|value| Some(value.signature) == input.signature)
            .ok_or_else(|| self.error("argument does not satisfy declaration signature"))?;
        if !input.callback && !value.parameters.is_empty() {
            return Err(self.error("structure declaration needs its remaining arguments"));
        }
        if input.callback && value.parameters.len() != input.callback_parameters.len() {
            return Err(self.error("declaration parameter count mismatch"));
        }
        let domain: HashMap<_, _> = input
            .callback_parameters
            .iter()
            .zip(&value.parameters)
            .map(|(expected, actual)| {
                (
                    expected.vars[0].1.unwrap(),
                    variable(actual.vars[0].clone()),
                )
            })
            .collect();
        let mut checks = value.checks.clone();
        for (id, expected) in ordered_arguments(&input.arguments) {
            if let Some(actual) = value.arguments.get(&id) {
                checks.push((
                    actual.clone(),
                    SExp::ConversionTarget {
                        expression: Box::new(substitute(&expected, &domain)),
                    },
                ));
            }
        }
        for (expected, actual) in input.callback_parameters.iter().zip(&value.parameters) {
            checks.push((
                variable(actual.vars[0].clone()),
                substitute(&expected.ty, &domain),
            ));
        }
        let fields = input
            .fields
            .iter()
            .map(|field| {
                let mut expression = value
                    .fields
                    .iter()
                    .find(|(name, _)| name == field)
                    .unwrap()
                    .1
                    .clone();
                if input.thunks.contains(field) {
                    expression = thunk(expression);
                }
                if input.callback {
                    expression = abstract_parameters(
                        &value.parameters,
                        SExp::Checked {
                            checks: checks.clone(),
                            body: Box::new(expression),
                        },
                    );
                }
                expression
            })
            .collect();
        if input.callback {
            checks.clear();
        }
        Ok((fields, checks))
    }

    pub(in crate::resolver) fn expand_structure_parameters(
        &mut self,
        parameters: &mut Vec<RightBind>,
        locals: &mut Vec<LocalScope>,
        module: bool,
    ) -> Result<(), Diagnostic> {
        let _cost = timing::costs::Scope::enter("resolve.structure-parameters");
        let mut flattened = Vec::new();
        let mut inputs = Vec::new();
        let mut parameter_checks = Vec::new();
        let mut position = 0;
        for mut bind in std::mem::take(parameters) {
            self.normalize_structures(&mut bind.ty, locals)?;
            if let Some((domain, result)) = self.declaration_signature(&bind.ty) {
                for mut name in bind.vars {
                    let mut domain = domain.clone();
                    let mut context = locals.clone();
                    self.expand_structure_parameters(&mut domain, &mut context, false)?;
                    let domain_inputs = self.last_inputs.clone();
                    let checks = self.last_parameter_checks.clone();
                    let mut result_parameters = vec![RightBind {
                        vars: vec![Identifier("<result>".into())],
                        ty: Box::new(result.clone()),
                    }];
                    self.expand_structure_parameters(&mut result_parameters, &mut context, false)?;
                    let result_input = self.last_inputs[0].clone();
                    let root = context
                        .iter()
                        .rev()
                        .find_map(|scope| scope.get("<result>"))
                        .unwrap();
                    let mut value = self.structure_values[&root.1.unwrap()].clone();
                    let mut substitutions = HashMap::new();
                    for (path, leaf) in result_input.fields.iter().zip(&result_parameters) {
                        let ty = substitute(&leaf.ty, &substitutions);
                        let mut scalar = Identifier(format!("{}.{}", name.0, path));
                        if module {
                            self.publish(&mut scalar);
                            self.global_bindings
                                .get_mut(&scalar.1.unwrap())
                                .unwrap()
                                .parameter = Some(position);
                            position += 1;
                        } else {
                            self.binding(&mut scalar);
                        }
                        let mut application = variable(scalar.clone());
                        for parameter in &domain {
                            for parameter in &parameter.vars {
                                application = SExp::App {
                                    func: Box::new(application),
                                    arg: Box::new(variable(parameter.clone())),
                                };
                            }
                        }
                        substitutions.insert(leaf.vars[0].1.unwrap(), application);
                        let mut ty = ty;
                        for parameter in domain.iter().rev() {
                            ty = SExp::Prod {
                                bind: Bind::Named(parameter.clone()),
                                body: Box::new(ty),
                            };
                        }
                        flattened.push(RightBind {
                            vars: vec![scalar],
                            ty: Box::new(ty),
                        });
                    }
                    for (_, expression) in &mut value.fields {
                        *expression = substitute(expression, &substitutions);
                    }
                    value.parameters = domain.clone();
                    value.inputs = domain_inputs;
                    value.checks.extend(checks);
                    if module {
                        self.publish(&mut name);
                    } else {
                        self.binding(&mut name);
                    }
                    locals.push(LocalScope::from_iter([(name.0.clone(), name.clone())]));
                    let signature = value.signature;
                    self.structure_values.insert(name.1.unwrap(), value);
                    inputs.push(Input {
                        binding: name.1.unwrap(),
                        callback_parameters: domain.clone(),
                        arguments: self.structure_values[&name.1.unwrap()].arguments.clone(),
                        name: name.0.clone(),
                        callback: true,
                        signature: Some(signature),
                        fields: result_input.fields,
                        computation: false,
                        thunks: result_input.thunks,
                    });
                }
            } else if let Some((signature, shape, mut arguments)) =
                self.structure_type(&bind.ty, locals)?
            {
                for (id, mut argument) in ordered_arguments(&arguments) {
                    self.expression(&mut argument, locals)?;
                    arguments.insert(id, argument);
                }
                let mut checks = self.signature_checks(&shape, &arguments);
                for (value, ty) in &mut checks {
                    self.expression(value, locals)?;
                    self.expression(ty, locals)?;
                }
                parameter_checks.extend(checks.clone());
                for mut name in bind.vars {
                    if module {
                        self.publish(&mut name);
                    } else {
                        self.binding(&mut name);
                    }
                    locals.push(LocalScope::from_iter([(name.0.clone(), name.clone())]));
                    let mut values = arguments.clone();
                    let mut fields = Vec::new();
                    let mut paths = Vec::new();
                    let mut thunks = HashSet::new();
                    for (field, ty, _) in &shape.fields {
                        let mut ty = substitute(ty, &values);
                        if self.structure_type(&ty, locals)?.is_some() {
                            let child_name = format!("{}.{}", name.0, field.0);
                            let mut nested = vec![RightBind {
                                vars: vec![Identifier(child_name.clone())],
                                ty: Box::new(ty),
                            }];
                            self.expand_structure_parameters(&mut nested, locals, module)?;
                            parameter_checks.extend(self.last_parameter_checks.clone());
                            for input in &self.last_inputs {
                                thunks.extend(
                                    input
                                        .thunks
                                        .iter()
                                        .map(|path| format!("{}.{}", field.0, path)),
                                );
                            }
                            if module {
                                for bind in &nested {
                                    for name in &bind.vars {
                                        self.global_bindings
                                            .get_mut(&name.1.unwrap())
                                            .unwrap()
                                            .parameter = Some(position);
                                        position += 1;
                                    }
                                }
                            }
                            let root = locals
                                .iter()
                                .rev()
                                .find_map(|scope| scope.get(&child_name))
                                .unwrap()
                                .clone();
                            let value = variable(root.clone());
                            let child = self.structure_values[&root.1.unwrap()].clone();
                            self.bind_structure_field(
                                field.1.unwrap(),
                                value.clone(),
                                &mut values,
                            )?;
                            fields.push((field.0.clone(), value));
                            for (path, expression) in child.fields {
                                fields.push((format!("{}.{}", field.0, path), expression));
                            }
                            paths.extend(nested.iter().flat_map(|bind| bind.vars.iter()).map(
                                |scalar| {
                                    scalar
                                        .0
                                        .strip_prefix(&format!("{}.", name.0))
                                        .unwrap()
                                        .to_owned()
                                },
                            ));
                            flattened.extend(nested);
                            continue;
                        }
                        let computation = computation_type(&ty);
                        if computation {
                            ty = SExp::ThunkType {
                                computation_ty: Box::new(ty),
                            };
                            thunks.insert(field.0.clone());
                        }
                        self.expression(&mut ty, locals)?;
                        let mut scalar = Identifier(format!("{}.{}", name.0, field.0));
                        if module {
                            self.publish(&mut scalar);
                            self.global_bindings
                                .get_mut(&scalar.1.unwrap())
                                .unwrap()
                                .parameter = Some(position);
                            position += 1;
                        } else {
                            self.binding(&mut scalar);
                        }
                        locals.push(LocalScope::from_iter([(scalar.0.clone(), scalar.clone())]));
                        let value = if computation {
                            force_reference(scalar.clone())
                        } else {
                            variable(scalar.clone())
                        };
                        self.bind_structure_field(field.1.unwrap(), value.clone(), &mut values)?;
                        fields.push((field.0.clone(), value));
                        paths.push(field.0.clone());
                        flattened.push(RightBind {
                            vars: vec![scalar],
                            ty: Box::new(ty),
                        });
                    }
                    self.structure_values.insert(
                        name.1.unwrap(),
                        Value {
                            arguments: arguments.clone(),
                            signature,
                            parameters: Vec::new(),
                            fields,
                            inputs: Vec::new(),
                            checks: checks.clone(),
                        },
                    );
                    inputs.push(Input {
                        binding: name.1.unwrap(),
                        callback_parameters: Vec::new(),
                        arguments: arguments.clone(),
                        name: name.0.clone(),
                        callback: false,
                        signature: Some(signature),
                        fields: paths,
                        computation: false,
                        thunks,
                    });
                }
            } else {
                let computation = computation_type(&bind.ty);
                if computation {
                    bind.ty = Box::new(SExp::ThunkType {
                        computation_ty: bind.ty,
                    });
                }
                self.expression(&mut bind.ty, locals)?;
                let mut scope = LocalScope::default();
                for name in &mut bind.vars {
                    if module {
                        self.publish(name);
                        self.global_bindings
                            .get_mut(&name.1.unwrap())
                            .unwrap()
                            .parameter = Some(position);
                        position += 1;
                    } else {
                        self.binding(name);
                    }
                    if computation {
                        self.computation_bindings.insert(name.1.unwrap());
                    }
                    scope.insert(name.0.clone(), name.clone());
                    inputs.push(Input {
                        binding: name.1.unwrap(),
                        callback_parameters: Vec::new(),
                        arguments: HashMap::new(),
                        name: name.0.clone(),
                        callback: false,
                        signature: None,
                        fields: Vec::new(),
                        computation,
                        thunks: HashSet::new(),
                    });
                }
                if !module {
                    locals.push(scope);
                }
                if bind.vars.is_empty() {
                    flattened.push(bind);
                } else {
                    flattened.extend(bind.vars.into_iter().map(|name| RightBind {
                        vars: vec![name],
                        ty: bind.ty.clone(),
                    }));
                }
            }
        }
        *parameters = flattened;
        self.last_inputs = inputs;
        self.last_parameter_checks = parameter_checks;
        Ok(())
    }
}
