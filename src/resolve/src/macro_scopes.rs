//! Module-wide macro collection and declaration-position dependency scheduling.
use super::*;

#[derive(Default)]
pub(super) struct MacroWork {
    pub(super) items: Vec<ModuleItem>,
    spans: Vec<SourceSpan>,
    source: Option<Arc<SourceFile>>,
    states: Vec<u8>,
    deltas: Vec<Option<TermScope>>,
    pub output: Vec<ModuleItem>,
    pub output_spans: Vec<SourceSpan>,
}

impl Resolver {
    pub(super) fn collect_macro_scope(
        &mut self,
        module: ModuleId,
        items: &[ModuleItem],
        spans: &[SourceSpan],
        source: Option<Arc<SourceFile>>,
    ) -> Result<(), Diagnostic> {
        let mut names = HashMap::new();
        for (index, item) in items.iter().enumerate() {
            if matches!(item, ModuleItem::Scoped { .. }) {
                let span = spans.get(index).copied().unwrap_or_default();
                for name in macro_exports(item) {
                    if let Some(first) = names.insert(name.0.clone(), span) {
                        return Err(self.error(crate::error::Error::DuplicateMacroDeclarations {
                            name: name.0.clone(),
                            first,
                            second: span,
                        }));
                    }
                }
                continue;
            }
            let (name, definition) = match item {
                ModuleItem::MathMacro {
                    name,
                    before,
                    after,
                } => (name, Some((MacroKind::Math, before, after))),
                ModuleItem::UserMacro {
                    name,
                    before,
                    after,
                } => (name, Some((MacroKind::Named, before, after))),
                ModuleItem::UseMacro { name, .. } => (name, None),
                _ => continue,
            };
            let span = spans.get(index).copied().unwrap_or_default();
            if let Some(first) = names.insert(name.0.clone(), span) {
                return Err(self.error(crate::error::Error::DuplicateMacroDeclarations {
                    name: name.0.clone(),
                    first,
                    second: span,
                }));
            }
            if let Some((kind, pattern, template)) = definition {
                let location = source.as_ref().map(|source| SourceLocation {
                    source: source.clone(),
                    span,
                });
                if let Some(location) = &location {
                    let mut declaration_location = location.clone();
                    let text = location.source.text.get(span.start..span.end).unwrap_or("");
                    if let Some(name_span) =
                        syntax::parse::macro_declaration_name_span(text, name.as_str())
                    {
                        declaration_location.span = SourceSpan {
                            start: span.start + name_span.start,
                            end: span.start + name_span.end,
                        };
                    }
                    self.declarations.push(Declaration {
                        module: self.path(module),
                        name: name.0.clone(),
                        kind: "macro",
                        location: declaration_location,
                        ty: None,
                    });
                }
                self.scopes[module.0 as usize].macros.push(MacroBinding {
                    name: name.clone(),
                    instance: module,
                    declaration_order: (span.start, index),
                    introduction_location: location.clone(),
                    definition: Arc::new(MacroDefinition {
                        id: MacroDefinitionId(self.next_macro),
                        kind,
                        pattern: pattern.clone(),
                        template: template.clone(),
                        definition_scope: module,
                        definition_name: name.0.clone(),
                        prepared: false,
                        location,
                    }),
                });
                self.next_macro += 1;
            }
        }
        self.work.insert(
            module,
            MacroWork {
                items: items.to_vec(),
                spans: spans.to_vec(),
                source,
                states: vec![0; items.len()],
                deltas: vec![None; items.len()],
                ..MacroWork::default()
            },
        );
        Ok(())
    }

    fn apply_term_delta(&mut self, module: ModuleId, delta: &TermScope) {
        let scope = &mut self.scopes[module.0 as usize];
        Arc::make_mut(&mut scope.names).extend(delta.names.iter().map(|(n, &id)| (n.clone(), id)));
        scope.imports.extend(delta.imports.clone());
        scope.import_ids.extend(delta.import_ids.clone());
    }

    pub(super) fn resolve_macro_item(
        &mut self,
        module: ModuleId,
        index: usize,
    ) -> Result<(), Diagnostic> {
        let state = self.work[&module].states[index];
        if state == 2 {
            if let Some(delta) = self.work[&module].deltas[index].clone() {
                self.apply_term_delta(module, &delta);
            }
            return Ok(());
        }
        if state == 1 {
            return Err(self.macro_cycle(module, index));
        }
        self.work.get_mut(&module).unwrap().states[index] = 1;
        self.dependency_stack.push((module, index));
        let current = self.current;
        let location = self.location.clone();
        self.current = module;
        let item = self.work[&module].items[index].clone();
        let preparing_macro = self.dependency_stack.iter().any(|&(module, index)| {
            self.work
                .get(&module)
                .and_then(|work| work.items.get(index))
                .is_some_and(|item| {
                    matches!(
                        item,
                        ModuleItem::UseMacro { .. }
                            | ModuleItem::UserMacro { .. }
                            | ModuleItem::MathMacro { .. }
                    )
                })
        });
        let dependencies = preparing_macro.then(|| term_dependencies(&item));
        for previous in 0..index {
            let preceding = &self.work[&module].items[previous];
            if matches!(
                preceding,
                ModuleItem::ChildModule { .. }
                    | ModuleItem::UserMacro { .. }
                    | ModuleItem::MathMacro { .. }
                    | ModuleItem::UseMacro { .. }
            ) {
                continue;
            }
            if let Some(dependencies) = &dependencies {
                if !term_names(preceding)
                    .iter()
                    .any(|name| dependencies.contains(name.as_str()))
                {
                    continue;
                }
            } else if self.work[&module].states[previous] == 1 {
                continue;
            }
            self.resolve_macro_item(module, previous)?;
        }
        let before = self.scopes[module.0 as usize].terms();
        let work = &self.work[&module];
        let span = work.spans.get(index).copied().unwrap_or_default();
        self.location = work.source.as_ref().map(|source| SourceLocation {
            source: source.clone(),
            span,
        });
        if std::env::var_os("REF_TYPE_PROFILE_RESOLVE").is_some() {
            eprintln!(
                "resolve item={}.{:?} scopes={}",
                self.path(module).join("."),
                term_names(&item),
                self.scopes.len()
            );
        }
        let mut output = Vec::new();
        self.scoped_item(item, &mut output)?;
        let scope = &self.scopes[module.0 as usize];
        let delta = TermScope {
            names: Arc::new(
                scope
                    .names
                    .iter()
                    .filter(|(n, id)| before.names.get(*n) != Some(*id))
                    .map(|(n, &id)| (n.clone(), id))
                    .collect(),
            ),
            imports: scope
                .imports
                .iter()
                .filter(|(n, id)| before.imports.get(*n) != Some(*id))
                .map(|(n, &id)| (n.clone(), id))
                .collect(),
            import_ids: scope
                .import_ids
                .iter()
                .filter(|(n, id)| before.import_ids.get(*n) != Some(*id))
                .map(|(n, &id)| (n.clone(), id))
                .collect(),
        };
        let work = self.work.get_mut(&module).unwrap();
        work.output_spans
            .extend(std::iter::repeat_n(span, output.len()));
        work.output.extend(output);
        work.states[index] = 2;
        work.deltas[index] = Some(delta);
        self.dependency_stack.pop();
        self.current = current;
        self.location = location;
        Ok(())
    }

    pub(super) fn macro_cycle(&self, module: ModuleId, index: usize) -> Diagnostic {
        let mut path = self.macro_dependency_path();
        let span = self.work[&module]
            .spans
            .get(index)
            .copied()
            .unwrap_or_default();
        path.push(format!(
            "{}:{}..{}",
            self.path(module).join("."),
            span.start,
            span.end
        ));
        self.error(crate::error::Error::MacroDependencyCycle { path })
    }

    pub(super) fn macro_dependency_path(&self) -> Vec<String> {
        self.dependency_stack
            .iter()
            .map(|&(module, index)| {
                let span = self
                    .work
                    .get(&module)
                    .and_then(|work| work.spans.get(index))
                    .copied()
                    .unwrap_or_default();
                format!(
                    "{}:{}..{}",
                    self.path(module).join("."),
                    span.start,
                    span.end
                )
            })
            .collect()
    }

    pub(super) fn ensure_macro_bindings(
        &mut self,
        mut module: ModuleId,
        name: Option<&Identifier>,
    ) -> Result<(), Diagnostic> {
        loop {
            let indexes = self
                .work
                .get(&module)
                .map(|work| {
                    work.items
                        .iter()
                        .enumerate()
                        .filter_map(|(i, item)| match item {
                            ModuleItem::UseMacro {
                                name: introduced, ..
                            } if name.is_none_or(|name| name.as_str() == introduced.as_str()) => {
                                Some(i)
                            }
                            item @ ModuleItem::Scoped { .. }
                                if macro_exports(item).iter().any(|introduced| {
                                    name.is_none_or(|name| name.as_str() == introduced.as_str())
                                }) =>
                            {
                                Some(i)
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            for index in indexes {
                // Math expressions can use an already collected local definition
                // while a use argument is being expanded.
                if name.is_none() && self.work[&module].states[index] == 1 {
                    continue;
                }
                let saved = self.scopes[module.0 as usize].clone();
                self.resolve_macro_item(module, index)?;
                let scope = &mut self.scopes[module.0 as usize];
                scope.names = saved.names;
                scope.imports = saved.imports;
                scope.import_ids = saved.import_ids;
            }
            // A local name hides every parent binding with the same spelling.
            if let Some(name) = name
                && self.scopes[module.0 as usize]
                    .macros
                    .iter()
                    .chain(&self.scopes[module.0 as usize].used)
                    .any(|d| d.name.as_str() == name.as_str())
            {
                break;
            }
            let Some(parent) = self.scopes[module.0 as usize].parent else {
                break;
            };
            module = parent;
        }
        Ok(())
    }

    pub(super) fn active_macro_use(&self, mut module: ModuleId) -> Option<(ModuleId, usize)> {
        loop {
            if let Some(work) = self.work.get(&module)
                && let Some(index) = work.items.iter().enumerate().find_map(|(index, item)| {
                    (work.states[index] == 1 && matches!(item, ModuleItem::UseMacro { .. }))
                        .then_some(index)
                })
            {
                return Some((module, index));
            }
            module = self.scopes[module.0 as usize].parent?;
        }
    }

    pub(super) fn prepare_macro_definition(
        &mut self,
        _: ModuleId,
        definition: &mut MacroBinding,
    ) -> Result<(), Diagnostic> {
        if definition.prepared {
            return Ok(());
        }
        let module = definition.definition_scope;
        let index = self.work.get(&module).and_then(|work| {
            work.items.iter().position(|item| match item {
                ModuleItem::MathMacro { name, .. } | ModuleItem::UserMacro { name, .. } => {
                    name.as_str() == definition.definition_name
                }
                _ => false,
            })
        });
        if let Some(index) = index {
            let saved = self.scopes[module.0 as usize].clone();
            self.resolve_macro_item(module, index)?;
            let scope = &mut self.scopes[module.0 as usize];
            scope.names = saved.names;
            scope.imports = saved.imports;
            scope.import_ids = saved.import_ids;
            *definition = scope
                .macros
                .iter()
                .find(|d| d.name.as_str() == definition.definition_name)
                .unwrap()
                .clone();
        }
        Ok(())
    }

    pub(super) fn macro_distance(&self, mut module: ModuleId, definition: &MacroBinding) -> usize {
        let mut distance = 0;
        loop {
            if self.scopes[module.0 as usize]
                .macros
                .iter()
                .chain(&self.scopes[module.0 as usize].used)
                .any(|d| d.name == definition.name)
            {
                return distance;
            }
            let Some(parent) = self.scopes[module.0 as usize].parent else {
                return usize::MAX;
            };
            module = parent;
            distance += 1;
        }
    }
}

fn macro_exports(item: &ModuleItem) -> Vec<&Identifier> {
    match item {
        ModuleItem::UseMacro { name, .. }
        | ModuleItem::UserMacro { name, .. }
        | ModuleItem::MathMacro { name, .. } => vec![name],
        ModuleItem::Scoped { exports, items } => items
            .iter()
            .flat_map(macro_exports)
            .filter(|name| {
                exports
                    .iter()
                    .any(|export| export.as_str() == name.as_str())
            })
            .collect(),
        _ => Vec::new(),
    }
}

pub(super) fn work_macro_names(work: &MacroWork) -> impl Iterator<Item = String> + '_ {
    work.items
        .iter()
        .flat_map(macro_exports)
        .map(|name| name.0.clone())
}
impl Resolver {
    pub(super) fn record_macro_template_references(&mut self, module: ModuleId) {
        let current = self.current;
        let location = self.location.clone();
        self.current = module;
        for definition in self.scopes[module.0 as usize].macros.clone() {
            self.location = definition.location.clone();
            let mut template = definition.template.clone();
            macros::walk_sexp_mut(&mut template, &mut |node| {
                if let SExp::NamedMacro {
                    name,
                    scope: Some(scope),
                    ..
                } = node
                    && let Some(target) = self
                        .visible(*scope)
                        .into_iter()
                        .find(|d| d.kind == MacroKind::Named && d.name.as_str() == name.as_str())
                {
                    self.record_macro_reference(target, Some(name));
                }
            });
        }
        self.current = current;
        self.location = location;
    }

    pub(super) fn record_macro_reference(
        &self,
        definition: &MacroBinding,
        name: Option<&Identifier>,
    ) {
        let Some(location) = &self.location else {
            return;
        };
        let Some(name) = name else {
            return;
        };
        let text = location
            .source
            .text
            .get(location.span.start..location.span.end)
            .unwrap_or("");
        for span in syntax::parse::named_macro_call_spans(text, name.as_str()) {
            let start = location.span.start + span.start;
            let end = location.span.start + span.end;
            let key = (
                Arc::as_ptr(&location.source) as usize,
                self.current,
                start,
                end,
                BindingId(definition.id.0),
            );
            if !self.reference_occurrences.borrow_mut().insert(key) {
                continue;
            }
            self.references.borrow_mut().push(Reference {
                module: self.path(self.current),
                location: SourceLocation {
                    source: location.source.clone(),
                    span: SourceSpan { start, end },
                },
                target_module: self.path(definition.definition_scope),
                target_name: definition.definition_name.clone(),
            });
        }
    }
}

impl Resolver {
    pub(super) fn resolve_macro_block(
        &mut self,
        items: Vec<ModuleItem>,
        output: &mut Vec<ModuleItem>,
    ) -> Result<Scope, Diagnostic> {
        let module = self.current;
        let saved_work = self.work.remove(&module);
        // Retain the enclosing macro environment as an independent lexical parent.
        let parent = ModuleId(self.scopes.len() as u32);
        self.scopes.push(self.scopes[module.0 as usize].clone());
        let scope = &mut self.scopes[module.0 as usize];
        scope.parent = Some(parent);
        scope.macros.clear();
        scope.used.clear();
        let span = self
            .location
            .as_ref()
            .map_or(SourceSpan::default(), |l| l.span);
        let source = self.location.as_ref().map(|l| l.source.clone());
        self.collect_macro_scope(module, &items, &vec![span; items.len()], source)?;
        for index in 0..items.len() {
            self.resolve_macro_item(module, index)?;
        }
        let work = self.work.remove(&module).unwrap();
        output.extend(work.output);
        if let Some(saved) = saved_work {
            self.work.insert(module, saved);
        }
        let pinned = ModuleId(self.scopes.len() as u32);
        let mut local = self.scopes[module.0 as usize].clone();
        for definition in local.macros.iter_mut().chain(&mut local.used) {
            if definition.definition_scope == module {
                definition.definition_scope = pinned;
                macros::walk_sexp_mut(&mut definition.template, &mut |node| {
                    if let SExp::NamedMacro {
                        scope: Some(scope), ..
                    }
                    | SExp::MathMacro {
                        scope: Some(scope), ..
                    } = node
                        && *scope == module
                    {
                        *scope = pinned;
                    }
                });
            }
        }
        self.origins.insert(pinned, module);
        self.scopes.push(local.clone());
        Ok(local)
    }
}

fn term_names(item: &ModuleItem) -> Vec<&Identifier> {
    match item {
        ModuleItem::Definition {
            owner: None, name, ..
        }
        | ModuleItem::Structure { name, .. }
        | ModuleItem::SetStructure { name, .. } => vec![name],
        ModuleItem::Record { type_name, .. } => vec![type_name],
        ModuleItem::Inductive {
            type_name,
            constructors,
            ..
        } => std::iter::once(type_name)
            .chain(constructors.iter().map(|(name, _, _)| name))
            .collect(),
        ModuleItem::Import { import_name, .. } => vec![import_name],
        ModuleItem::Scoped { exports, .. } => exports.iter().collect(),
        _ => Vec::new(),
    }
}

fn term_dependencies(item: &ModuleItem) -> HashSet<String> {
    fn expression(exp: &SExp, binders: &[RightBind], names: &mut HashSet<String>) {
        let mut exp = exp.clone();
        for bind in binders.iter().rev() {
            exp = SExp::Prod {
                bind: Bind::Named(bind.clone()),
                body: Box::new(exp),
            };
        }
        macros::rename_template_binders(&mut exp, u64::MAX);
        macros::walk_sexp_mut(&mut exp, &mut |node| {
            let access = match node {
                SExp::AccessPath { access, .. }
                | SExp::ProgramValueReference { access }
                | SExp::RecordTypeCtor { access, .. }
                | SExp::IndCase { path: access, .. }
                | SExp::ProgramCase { path: access, .. } => Some(access),
                _ => None,
            };
            if let Some(access) = access {
                match access {
                    LocalAccess::Current { access, .. } => {
                        names.insert(access.as_str().trim_end_matches('^').to_owned());
                    }
                    LocalAccess::Named { access, .. } => {
                        names.insert(access.0.clone());
                    }
                    _ => {}
                }
            }
            if let SExp::ModuleInstance { path, .. } = node {
                selection(path, names);
            }
        });
    }
    fn selection(path: &ModuleInstantiatePath, names: &mut HashSet<String>) {
        let calls = match path {
            ModuleInstantiatePath::FromImport { import_name, calls } => {
                names.insert(import_name.0.clone());
                calls
            }
            ModuleInstantiatePath::FromModule { calls, .. }
            | ModuleInstantiatePath::FromRoot { calls }
            | ModuleInstantiatePath::FromCurrent { calls, .. } => calls,
        };
        for (_, arguments) in calls {
            for (_, argument) in arguments {
                expression(argument, &[], names);
            }
        }
    }
    let mut names = HashSet::new();
    match item {
        ModuleItem::UserMacro { after, .. } | ModuleItem::MathMacro { after, .. } => {
            expression(after, &[], &mut names);
        }
        ModuleItem::UseMacro { path, .. } => selection(path, &mut names),
        ModuleItem::Import { path, checks, .. } => {
            selection(path, &mut names);
            for (value, ty) in checks {
                expression(value, &[], &mut names);
                expression(ty, &[], &mut names);
            }
        }
        ModuleItem::Definition {
            owner,
            binders,
            ty,
            body,
            ..
        } => {
            let mut parameters = Vec::new();
            if let Some(owner) = owner {
                names.insert(owner.type_name.0.clone());
                parameters.extend(owner.parameters.clone());
            }
            parameters.extend(binders.clone());
            expression(ty, &parameters, &mut names);
            expression(body, &parameters, &mut names);
        }
        ModuleItem::Structure {
            parameters, fields, ..
        } => {
            let mut parameters = parameters.clone();
            for (index, bind) in parameters.iter().enumerate() {
                expression(&bind.ty, &parameters[..index], &mut names);
            }
            for (name, ty, default) in fields {
                expression(ty, &parameters, &mut names);
                if let Some(value) = default {
                    expression(value, &parameters, &mut names);
                }
                parameters.push(RightBind {
                    vars: vec![name.clone()],
                    ty: Box::new(ty.clone()),
                });
            }
        }
        ModuleItem::SetStructure {
            parameters, fields, ..
        }
        | ModuleItem::Record {
            parameters, fields, ..
        } => {
            let mut parameters = parameters.clone();
            for (index, bind) in parameters.iter().enumerate() {
                expression(&bind.ty, &parameters[..index], &mut names);
            }
            for (name, ty) in fields {
                expression(ty, &parameters, &mut names);
                parameters.push(RightBind {
                    vars: vec![name.clone()],
                    ty: Box::new(ty.clone()),
                });
            }
        }
        ModuleItem::Inductive {
            parameters,
            indices,
            constructors,
            ..
        } => {
            let mut parameters = parameters.clone();
            parameters.extend(indices.clone());
            for (index, bind) in parameters.iter().enumerate() {
                expression(&bind.ty, &parameters[..index], &mut names);
            }
            for (_, binders, ty) in constructors {
                let mut binders_with_parameters = parameters.clone();
                binders_with_parameters.extend(binders.clone());
                expression(ty, &binders_with_parameters, &mut names);
            }
        }
        ModuleItem::Eval { exp } | ModuleItem::Normalize { exp } | ModuleItem::Infer { exp } => {
            expression(exp, &[], &mut names)
        }
        ModuleItem::Check { exp, ty } => {
            expression(exp, &[], &mut names);
            expression(ty, &[], &mut names);
        }
        ModuleItem::MemberCheck { value, ty } => {
            expression(value, &[], &mut names);
            expression(ty, &[], &mut names);
        }
        ModuleItem::ValueTypeCheck { ty } => expression(&ty.clone().into(), &[], &mut names),
        ModuleItem::Scoped { items, .. } => {
            for item in items {
                names.extend(term_dependencies(item));
            }
        }
        ModuleItem::ChildModule { .. } => {}
    }
    names
}
