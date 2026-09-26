use crate::{
    bindings,
    hir::*,
    lower,
    macros::{self, MacroDefinition, MacroKind},
};
use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet},
};

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub message: String,
    pub location: Option<SourceLocation>,
    pub module: Vec<String>,
}
impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for Diagnostic {}

/// A source occurrence whose lexical target is known before type inference.
#[derive(Debug, Clone)]
pub struct Reference {
    pub module: Vec<String>,
    pub location: SourceLocation,
    pub target_module: Vec<String>,
    pub target_name: String,
}

#[derive(Debug, Clone)]
pub struct Binding {
    pub module: ModuleId,
    pub name: String,
    pub parameter: Option<usize>,
}

/// Namespace correspondence for a syntactic module instantiation.
/// Elaboration fills in the corresponding typed instances after checking arguments.
#[derive(Debug, Clone)]
pub struct Import {
    pub owner: ModuleId,
    pub name: String,
    pub target: ModuleId,
    pub remapping: HashMap<ModuleId, ModuleId>,
}

#[derive(Debug, Clone)]
pub struct Project {
    pub modules: Vec<Module>,
    pub references: Vec<Reference>,
    pub bindings: HashMap<BindingId, Binding>,
    pub order: Vec<ModuleId>,
    pub imports: HashMap<BindingId, Import>,
}

#[derive(Clone, Default)]
struct Scope {
    parent: Option<ModuleId>,
    children: HashMap<String, ModuleId>,
    names: HashMap<String, BindingId>,
    imports: HashMap<String, ModuleId>,
    import_ids: HashMap<String, BindingId>,
    macros: Vec<MacroDefinition>,
    used: Vec<MacroDefinition>,
    remapping: HashMap<ModuleId, ModuleId>,
    substitutions: HashMap<BindingId, SExp>,
}

#[derive(Default)]
struct Resolver {
    scopes: Vec<Scope>,
    input: HashMap<ModuleId, Module>,
    output: HashMap<ModuleId, Module>,
    origins: HashMap<ModuleId, ModuleId>,
    paths: HashMap<ModuleId, Vec<String>>,
    occurrences: HashMap<(ModuleId, String), usize>,
    states: HashMap<ModuleId, u8>,
    imports: HashMap<BindingId, Import>,
    next_binding: u64,
    next_expression: u64,
    next_macro: u64,
    next_hygiene: Cell<u64>,
    location: Option<SourceLocation>,
    current: ModuleId,
    references: RefCell<Vec<Reference>>,
    global_bindings: HashMap<BindingId, Binding>,
    order: Vec<ModuleId>,
}

pub fn resolve(modules: &[syntax::syntax::Module]) -> Result<Project, Diagnostic> {
    let mut resolver = Resolver::default();
    resolver.scopes.push(Scope::default());
    let mut roots: Vec<_> = modules.iter().cloned().map(lower::module).collect();
    for module in &mut roots {
        resolver.reserve(ModuleId(0), module);
    }
    let mut ids: Vec<_> = resolver.input.keys().copied().collect();
    ids.sort_by_key(|id| id.0);
    for id in ids {
        resolver.module(id)?;
    }
    fn assemble(module: &mut Module, outputs: &HashMap<ModuleId, Module>) {
        *module = outputs[&module.id].clone();
        if let ModuleBody::Inline(items) = &mut module.body {
            for item in items {
                if let ModuleItem::ChildModule { module } = item {
                    assemble(module, outputs);
                }
            }
        }
    }
    for module in &mut roots {
        assemble(module, &resolver.output);
    }
    let order = resolver
        .order
        .iter()
        .copied()
        .filter(|id| {
            let parent = resolver.scopes[id.0 as usize].parent;
            let Some(module) = parent.and_then(|parent| resolver.output.get(&parent)) else {
                return true;
            };
            matches!(&module.body, ModuleBody::Inline(items)
                if items.iter().all(|item| matches!(item, ModuleItem::ChildModule { .. })))
        })
        .collect();
    Ok(Project {
        order,
        modules: roots,
        imports: resolver.imports,
        references: resolver.references.into_inner(),
        bindings: resolver.global_bindings,
    })
}

impl Resolver {
    fn fresh_hygiene(&self) -> u64 {
        let identity = self.next_hygiene.get();
        self.next_hygiene.set(identity + 1);
        identity
    }

    fn binding(&mut self, name: &mut Identifier) -> BindingId {
        let id = BindingId(self.next_binding);
        self.next_binding += 1;
        name.1 = Some(id);
        id
    }
    fn reserve(&mut self, parent: ModuleId, module: &mut Module) {
        module.id = ModuleId(self.scopes.len() as u32);
        self.binding(&mut module.name);
        let occurrence = self
            .occurrences
            .entry((parent, module.name.0.clone()))
            .or_default();
        *occurrence += 1;
        let component = if *occurrence == 1 {
            module.name.0.clone()
        } else {
            format!("{}#{occurrence}", module.name.0)
        };
        let mut path = self.paths.get(&parent).cloned().unwrap_or_default();
        path.push(component);
        self.paths.insert(module.id, path);
        self.scopes.push(Scope {
            parent: Some(parent),
            ..Scope::default()
        });
        self.scopes[parent.0 as usize]
            .children
            .entry(module.name.0.clone())
            .or_insert(module.id);
        if let ModuleBody::Inline(items) = &mut module.body {
            for item in items {
                if let ModuleItem::ChildModule { module: child } = item {
                    self.reserve(module.id, child);
                }
            }
        }
        self.input.insert(module.id, module.clone());
    }
    fn path(&self, module: ModuleId) -> Vec<String> {
        let source = self.origins.get(&module).copied().unwrap_or(module);
        self.paths.get(&source).cloned().unwrap_or_default()
    }
    fn error(&self, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            message: message.into(),
            location: self.location.clone(),
            module: self.path(self.current),
        }
    }
    fn lexical(&mut self, exp: &mut SExp, scopes: &mut Vec<HashMap<String, Identifier>>) {
        let order = self.next_expression;
        self.next_expression += 1;
        bindings::alpha_rename(exp, bindings::Mode::Resolved(order), &mut 0, scopes);
    }
    fn expression(
        &mut self,
        exp: &mut SExp,
        scopes: &mut Vec<HashMap<String, Identifier>>,
    ) -> Result<(), Diagnostic> {
        self.expand(exp)?;
        self.lexical(exp, scopes);
        self.resolve_expressions(exp)
    }
    fn resolve_expressions(&self, exp: &mut SExp) -> Result<(), Diagnostic> {
        let mut result = Ok(());
        macros::walk_sexp_mut(exp, &mut |node| {
            if result.is_err() {
                return;
            }
            match node {
                SExp::AccessPath { access, .. }
                | SExp::RecordTypeCtor { access, .. }
                | SExp::IndCase { path: access, .. }
                | SExp::IndElimPrim { path: access, .. }
                | SExp::ProgramCase { path: access, .. } => {
                    result = self.access(self.current, access);
                }
                SExp::MacroParameter(_) | SExp::TokenMatch { .. } => {
                    result = Err(self.error("macro template syntax outside a macro expansion"));
                }
                _ => {}
            }
        });
        result
    }
    fn access(&self, from: ModuleId, access: &mut LocalAccess) -> Result<(), Diagnostic> {
        let display = access.to_string();
        let (mut module, name, inherit, span) = match access {
            LocalAccess::Current { access, span } => {
                if access.1.is_some() {
                    return Ok(());
                }
                (from, access.clone(), true, *span)
            }
            LocalAccess::Named {
                access,
                child,
                span,
            } => (
                self.import(from, access.as_str()).ok_or_else(|| {
                    self.error(format!("Module import '{}' was not found", access.as_str()))
                })?,
                child.clone(),
                false,
                *span,
            ),
            LocalAccess::Resolved { .. } => return Ok(()),
        };
        let spelling = name.as_str().trim_end_matches('^');
        loop {
            if let Some(id) = self.scopes[module.0 as usize].names.get(spelling) {
                if let Some(location) = &self.location
                    && span.end > span.start
                {
                    self.references.borrow_mut().push(Reference {
                        module: self.path(self.current),
                        location: SourceLocation {
                            source: location.source.clone(),
                            span,
                        },
                        target_module: self.path(module),
                        target_name: spelling.to_owned(),
                    });
                }
                *access = LocalAccess::Resolved {
                    module,
                    span,
                    access: Name(name.0, Some(*id)),
                    display,
                };
                return Ok(());
            }
            if !inherit {
                break;
            }
            let Some(parent) = self.scopes[module.0 as usize].parent else {
                break;
            };
            module = parent;
        }
        Err(self.error(format!(
            "Name '{}' was not found in its scope",
            name.as_str()
        )))
    }
    fn import(&self, mut module: ModuleId, name: &str) -> Option<ModuleId> {
        loop {
            let scope = &self.scopes[module.0 as usize];
            if let Some(target) = scope.imports.get(name) {
                return Some(*target);
            }
            module = scope.parent?;
        }
    }
    fn publish(&mut self, name: &mut Identifier) {
        let id = self.binding(name);
        self.scopes[self.current.0 as usize]
            .names
            .insert(name.0.clone(), id);
        self.global_bindings.insert(
            id,
            Binding {
                module: self.current,
                name: name.0.clone(),
                parameter: None,
            },
        );
    }
    fn parameters(
        &mut self,
        parameters: &mut [RightBind],
        locals: &mut Vec<HashMap<String, Identifier>>,
        module: bool,
    ) -> Result<(), Diagnostic> {
        let mut position = 0;
        for bind in parameters {
            self.expression(&mut bind.ty, locals)?;
            let mut scope = HashMap::new();
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
                scope.insert(name.0.clone(), name.clone());
            }
            if !module {
                locals.push(scope);
            }
        }
        Ok(())
    }
    fn module(&mut self, id: ModuleId) -> Result<(), Diagnostic> {
        match self.states.get(&id) {
            Some(2) => return Ok(()),
            Some(1) => return Err(self.error("cyclic module import dependency")),
            _ => {}
        }
        let parent = self.scopes[id.0 as usize].parent;
        if let Some(parent) = parent.filter(|parent| *parent != ModuleId(0)) {
            if self.states.get(&parent) != Some(&1) {
                self.module(parent)?;
            }
            if self.states.get(&id) == Some(&2) {
                return Ok(());
            }
        }
        self.states.insert(id, 1);
        let previous = self.current;
        let location = self.location.clone();
        self.current = id;
        let mut module = self.input[&id].clone();
        self.location = module
            .header_source
            .as_ref()
            .or(module.source.as_ref())
            .map(|source| SourceLocation {
                source: source.clone(),
                span: module.span,
            });
        self.parameters(&mut module.parameters, &mut Vec::new(), true)?;
        let ModuleBody::Inline(items) = &mut module.body else {
            return Err(self.error("External module was not loaded"));
        };
        let namespace = items.iter().all(|item| {
            matches!(
                item,
                ModuleItem::ChildModule { .. }
                    | ModuleItem::MathMacro { .. }
                    | ModuleItem::UserMacro { .. }
                    | ModuleItem::UseMacro { .. }
            )
        });
        for (index, item) in items.iter_mut().enumerate() {
            if namespace && matches!(item, ModuleItem::ChildModule { .. }) {
                continue;
            }
            self.location = module.source.as_ref().map(|source| SourceLocation {
                source: source.clone(),
                span: module
                    .declaration_spans
                    .get(index)
                    .copied()
                    .unwrap_or(module.span),
            });
            self.item(item)?;
        }
        let mut index = 0;
        let mut spans = Vec::new();
        items.retain(|item| {
            let keep = !matches!(
                item,
                ModuleItem::MathMacro { .. }
                    | ModuleItem::UserMacro { .. }
                    | ModuleItem::UseMacro { .. }
            );
            if keep {
                spans.push(
                    module
                        .declaration_spans
                        .get(index)
                        .copied()
                        .unwrap_or(module.span),
                );
            }
            index += 1;
            keep
        });
        module.declaration_spans = spans;
        self.output.insert(id, module);
        self.states.insert(id, 2);
        self.order.push(id);
        self.current = previous;
        self.location = location;
        Ok(())
    }
    fn item(&mut self, item: &mut ModuleItem) -> Result<(), Diagnostic> {
        let mut locals = Vec::new();
        match item {
            ModuleItem::Definition {
                owner,
                name,
                binders,
                ty,
                body,
            } => {
                if let Some(owner) = owner {
                    self.parameters(&mut owner.parameters, &mut locals, false)?;
                }
                self.parameters(binders, &mut locals, false)?;
                self.expression(ty, &mut locals)?;
                self.expression(body, &mut locals)?;
                if owner.is_none() {
                    self.publish(name);
                } else {
                    self.binding(name);
                }
            }
            ModuleItem::Inductive {
                type_name,
                parameters,
                indices,
                constructors,
                ..
            } => {
                self.parameters(parameters, &mut locals, false)?;
                self.parameters(indices, &mut locals.clone(), false)?;
                self.publish(type_name);
                for (name, binders, ty) in constructors {
                    self.binding(name);
                    let mut scope = locals.clone();
                    self.parameters(binders, &mut scope, false)?;
                    self.expression(ty, &mut scope)?;
                }
            }
            ModuleItem::Record {
                type_name,
                parameters,
                fields,
                ..
            } => {
                self.parameters(parameters, &mut locals, false)?;
                self.publish(type_name);
                for (name, ty) in fields {
                    self.expression(ty, &mut locals)?;
                    self.binding(name);
                    locals.push(HashMap::from([(name.0.clone(), name.clone())]));
                }
            }
            ModuleItem::ChildModule { module } => self.module(module.id)?,
            ModuleItem::Import { path, import_name } => self.resolve_import(path, import_name)?,
            ModuleItem::MathMacro {
                name,
                before,
                after,
            } => self.register_macro(name, MacroKind::Math, before, after)?,
            ModuleItem::UserMacro {
                name,
                before,
                after,
            } => self.register_macro(name, MacroKind::Named, before, after)?,
            ModuleItem::UseMacro {
                import_name,
                macro_name,
            } => {
                let target = self
                    .import(self.current, import_name.as_str())
                    .ok_or_else(|| {
                        self.error(format!(
                            "Module import '{}' was not found",
                            import_name.as_str()
                        ))
                    })?;
                let definition = self.scopes[target.0 as usize]
                    .macros
                    .iter()
                    .find(|definition| definition.name.as_str() == macro_name.as_str())
                    .cloned()
                    .ok_or_else(|| {
                        self.error(format!(
                            "Macro '{}.{}' was not found",
                            import_name.as_str(),
                            macro_name.as_str()
                        ))
                    })?;
                if self
                    .visible(self.current)
                    .iter()
                    .any(|d| d.name.as_str() == macro_name.as_str())
                {
                    return Err(self.error(format!(
                        "Macro '{}' is already visible",
                        macro_name.as_str()
                    )));
                }
                self.scopes[self.current.0 as usize].used.push(definition);
            }
            ModuleItem::Eval { exp }
            | ModuleItem::Normalize { exp }
            | ModuleItem::Infer { exp } => self.expression(exp, &mut locals)?,
            ModuleItem::Check { exp, ty } => {
                self.expression(exp, &mut locals)?;
                self.expression(ty, &mut locals)?;
            }
            ModuleItem::ComputationEval { exp }
            | ModuleItem::ComputationNormalize { exp }
            | ModuleItem::ComputationInfer { exp } => self.computation(exp, &mut locals)?,
            ModuleItem::ValueInfer { exp } => self.value(exp, &mut locals)?,
            ModuleItem::ValueCheck { exp, ty } => {
                self.value(exp, &mut locals)?;
                self.value_type(ty, &mut locals)?;
            }
            ModuleItem::ComputationCheck { exp, ty } => {
                self.computation(exp, &mut locals)?;
                self.computation_type(ty, &mut locals)?;
            }
        }
        Ok(())
    }
    fn visible(&self, mut module: ModuleId) -> Vec<&MacroDefinition> {
        let mut result = Vec::new();
        loop {
            let scope = &self.scopes[module.0 as usize];
            result.extend(&scope.macros);
            result.extend(&scope.used);
            let Some(parent) = scope.parent else { break };
            module = parent;
        }
        result
    }
    fn register_macro(
        &mut self,
        name: &Identifier,
        kind: MacroKind,
        pattern: &[MacroSeqAtom],
        template: &mut SExp,
    ) -> Result<(), Diagnostic> {
        if self
            .visible(self.current)
            .iter()
            .any(|d| d.name.as_str() == name.as_str())
        {
            return Err(self.error(format!("Macro '{}' is already visible", name.as_str())));
        }
        let mut captures = HashMap::new();
        let mut fixed = 0;
        macros::pattern_captures(pattern, &mut captures, &mut fixed, kind)
            .map_err(|e| self.error(e))?;
        if kind == MacroKind::Math && fixed == 0 {
            return Err(self.error(format!(
                "Math macro '{}' must contain at least one fixed token",
                name.as_str()
            )));
        }
        let mut has_match = false;
        macros::walk_sexp_mut(template, &mut |node| {
            has_match |= matches!(node, SExp::TokenMatch { .. })
        });
        if kind == MacroKind::Math && has_match {
            return Err(self.error("Token matching is only valid in named macros"));
        }
        macros::validate_template(template, &captures).map_err(|e| self.error(e))?;
        macros::rename_template_binders(template, self.fresh_hygiene());
        let order = self.next_macro;
        self.next_macro += 1;
        let mut result = Ok(());
        macros::walk_sexp_mut(template, &mut |node| {
            if result.is_err() {
                return;
            }
            match node {
                SExp::MathMacro {
                    scope, max_order, ..
                }
                | SExp::NamedMacro {
                    scope, max_order, ..
                } => {
                    *scope = Some(self.current);
                    *max_order = Some(order);
                }
                SExp::AccessPath { access, .. }
                | SExp::RecordTypeCtor { access, .. }
                | SExp::IndCase { path: access, .. }
                | SExp::IndElimPrim { path: access, .. }
                | SExp::ProgramCase { path: access, .. } => {
                    if !matches!(access, LocalAccess::Current { access, .. } if access.as_str().starts_with("<macro:"))
                    {
                        result = self.access(self.current, access);
                    }
                }
                _ => {}
            }
        });
        result?;
        let mut result = Ok(());
        let visible: HashSet<_> = self
            .visible(self.current)
            .iter()
            .filter(|d| d.kind == MacroKind::Named)
            .map(|d| d.name.0.clone())
            .collect();
        macros::walk_sexp_mut(template, &mut |node| {
            if let SExp::NamedMacro { name: nested, .. } = node
                && !visible.contains(nested.as_str())
                && !(kind == MacroKind::Named && nested.as_str() == name.as_str())
            {
                result = Err(self.error(format!(
                    "Named macro '{}' is not visible at template declaration",
                    nested.as_str()
                )));
            }
        });
        result?;
        self.scopes[self.current.0 as usize]
            .macros
            .push(MacroDefinition {
                name: name.clone(),
                kind,
                pattern: pattern.to_vec(),
                template: template.clone(),
                declaration_order: order,
            });
        Ok(())
    }
    fn expand(&self, exp: &mut SExp) -> Result<(), Diagnostic> {
        let mut result = Ok(());
        macros::walk_sexp_control(exp, &mut |node| {
            if result.is_err() {
                return false;
            }
            loop {
                let next = match node {
                    SExp::NamedMacro {
                        name,
                        tokens,
                        scope,
                        depth,
                        max_order,
                    } => self.expand_one(
                        scope.unwrap_or(self.current),
                        Some(name),
                        tokens,
                        *depth,
                        *max_order,
                    ),
                    SExp::MathMacro {
                        tokens,
                        scope,
                        depth,
                        max_order,
                    } => self.expand_one(
                        scope.unwrap_or(self.current),
                        None,
                        tokens,
                        *depth,
                        *max_order,
                    ),
                    _ => return true,
                };
                match next {
                    Ok(next) => *node = next,
                    Err(error) => {
                        result = Err(error);
                        return false;
                    }
                }
            }
        });
        result
    }
    fn expand_one(
        &self,
        scope: ModuleId,
        name: Option<&Identifier>,
        tokens: &[MacroExp],
        depth: u16,
        order: Option<u64>,
    ) -> Result<SExp, Diagnostic> {
        if depth >= macros::MAX_MACRO_EXPANSION_DEPTH {
            return Err(self.error(format!(
                "Macro expansion exceeded depth {}",
                macros::MAX_MACRO_EXPANSION_DEPTH
            )));
        }
        let tokens = if name.is_none() {
            tokens
                .iter()
                .map(|token| match token {
                    MacroExp::Seq(tokens) => self
                        .expand_one(scope, None, tokens, depth + 1, order)
                        .map(MacroExp::RawExp),
                    token => Ok(token.clone()),
                })
                .collect::<Result<Vec<_>, _>>()?
        } else {
            tokens.to_vec()
        };
        if name.is_none()
            && let [MacroExp::RawExp(exp)] = tokens.as_slice()
        {
            return Ok(exp.clone());
        }
        let mut candidates = self
            .visible(scope)
            .into_iter()
            .filter(|d| {
                if let Some(name) = name {
                    d.kind == MacroKind::Named
                        && d.name.as_str() == name.as_str()
                        && order.is_none_or(|max| d.declaration_order <= max)
                } else {
                    d.kind == MacroKind::Math && order.is_none_or(|max| d.declaration_order < max)
                }
            })
            .collect::<Vec<_>>();
        if name.is_none() {
            candidates.sort_by_key(|d| {
                (
                    macros::first_fixed_position(&d.pattern),
                    d.declaration_order,
                )
            });
        }
        for definition in candidates {
            let mut captures = HashMap::new();
            if macros::match_pattern(&definition.pattern, &tokens, &mut captures) {
                return macros::instantiate_template(
                    definition,
                    &captures,
                    depth,
                    self.fresh_hygiene(),
                )
                .map_err(|e| self.error(e));
            }
            if name.is_some() {
                return Err(self.error(format!(
                    "Input does not match the complete pattern of macro '{}'",
                    definition.name.as_str()
                )));
            }
        }
        Err(self.error(name.map_or_else(
            || "No visible math macro matches the complete token sequence".into(),
            |name| format!("Named macro '{}' is not visible", name.as_str()),
        )))
    }
    fn resolve_import(
        &mut self,
        path: &mut ModuleInstantiatePath,
        name: &mut Identifier,
    ) -> Result<(), Diagnostic> {
        let (mut target, calls) = match path {
            ModuleInstantiatePath::FromRoot { calls } => (ModuleId(0), calls),
            ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                let mut base = self.current;
                for _ in 0..*back_parent {
                    base = self.scopes[base.0 as usize]
                        .parent
                        .ok_or_else(|| self.error("already at root module"))?;
                }
                (base, calls)
            }
            ModuleInstantiatePath::FromImport { import_name, calls } => {
                let mut scope = self.current;
                loop {
                    if let Some(id) = self.scopes[scope.0 as usize]
                        .import_ids
                        .get(import_name.as_str())
                    {
                        import_name.1 = Some(*id);
                        break;
                    }
                    let Some(parent) = self.scopes[scope.0 as usize].parent else {
                        break;
                    };
                    scope = parent;
                }
                (
                    self.import(self.current, import_name.as_str())
                        .ok_or_else(|| {
                            self.error(format!(
                                "Module import '{}' was not found",
                                import_name.as_str()
                            ))
                        })?,
                    calls,
                )
            }
        };
        let mut remapping = self.scopes[target.0 as usize].remapping.clone();
        let mut substitutions = self.scopes[target.0 as usize].substitutions.clone();
        let mut route = Vec::new();
        for (child, arguments) in calls {
            for (_, argument) in arguments.iter_mut() {
                self.expression(argument, &mut Vec::new())?;
            }
            target = *self.scopes[target.0 as usize]
                .children
                .get(child.as_str())
                .ok_or_else(|| {
                    self.error(format!("child module '{}' was not found", child.as_str()))
                })?;
            target = self.origins.get(&target).copied().unwrap_or(target);
            if self.input.contains_key(&target) {
                let mut ancestor = Some(self.current);
                while let Some(id) = ancestor {
                    if id == target {
                        break;
                    }
                    ancestor = self.scopes[id.0 as usize].parent;
                }
                if ancestor.is_none() {
                    self.module(target)?;
                }
            }
            child.1 = self.input.get(&target).and_then(|module| module.name.1);
            for (name, argument) in arguments {
                if let Some(id) = self.scopes[target.0 as usize].names.get(name.as_str()) {
                    name.1 = Some(*id);
                    substitutions.insert(*id, argument.clone());
                }
            }
            route.push(target);
        }
        for source in route {
            target = self.instantiate(source, &mut remapping, &substitutions);
        }
        let id = self.binding(name);
        self.scopes[self.current.0 as usize]
            .imports
            .insert(name.0.clone(), target);
        self.scopes[self.current.0 as usize]
            .import_ids
            .insert(name.0.clone(), id);
        self.imports.insert(
            id,
            Import {
                owner: self.current,
                name: name.0.clone(),
                target,
                remapping,
            },
        );
        Ok(())
    }
    fn instantiate(
        &mut self,
        source: ModuleId,
        remapping: &mut HashMap<ModuleId, ModuleId>,
        substitutions: &HashMap<BindingId, SExp>,
    ) -> ModuleId {
        fn allocate(
            resolver: &mut Resolver,
            source: ModuleId,
            map: &mut HashMap<ModuleId, ModuleId>,
            pairs: &mut Vec<(ModuleId, ModuleId)>,
        ) -> ModuleId {
            if let Some((_, id)) = pairs.iter().find(|(existing, _)| *existing == source) {
                return *id;
            }
            let id = ModuleId(resolver.scopes.len() as u32);
            resolver.scopes.push(Scope::default());
            map.insert(source, id);
            pairs.push((source, id));
            resolver
                .origins
                .insert(id, resolver.origins.get(&source).copied().unwrap_or(source));
            let mut children: Vec<_> = resolver.scopes[source.0 as usize]
                .children
                .values()
                .copied()
                .collect();
            children.sort_by_key(|id| id.0);
            for child in children {
                allocate(resolver, child, map, pairs);
            }
            id
        }
        let mut pairs = Vec::new();
        let mut imports: Vec<_> = self.scopes[source.0 as usize]
            .imports
            .values()
            .copied()
            .collect();
        imports.sort_by_key(|id| id.0);
        for import in imports {
            allocate(self, import, remapping, &mut pairs);
        }
        let result = allocate(self, source, remapping, &mut pairs);
        for (source, id) in pairs {
            let mut scope = self.scopes[source.0 as usize].clone();
            scope.parent = scope
                .parent
                .map(|id| remapping.get(&id).copied().unwrap_or(id));
            for child in scope.children.values_mut() {
                *child = remapping.get(child).copied().unwrap_or(*child);
            }
            for import in scope.imports.values_mut() {
                *import = remapping.get(import).copied().unwrap_or(*import);
            }
            for definition in scope.macros.iter_mut().chain(&mut scope.used) {
                macros::walk_sexp_control(&mut definition.template, &mut |node| {
                    if let SExp::AccessPath {
                        access: LocalAccess::Resolved { access, .. },
                        parameters,
                    } = node
                        && parameters.is_empty()
                        && let Some(argument) = access.1.and_then(|id| substitutions.get(&id))
                    {
                        *node = if access.as_str().ends_with('^') {
                            SExp::Reflect {
                                parameter: access.1.unwrap(),
                                expression: Box::new(argument.clone()),
                            }
                        } else {
                            argument.clone()
                        };
                        return false;
                    }
                    true
                });
                macros::walk_sexp_mut(&mut definition.template, &mut |node| match node {
                    SExp::AccessPath {
                        access: LocalAccess::Resolved { module, .. },
                        ..
                    }
                    | SExp::RecordTypeCtor {
                        access: LocalAccess::Resolved { module, .. },
                        ..
                    }
                    | SExp::IndCase {
                        path: LocalAccess::Resolved { module, .. },
                        ..
                    }
                    | SExp::IndElimPrim {
                        path: LocalAccess::Resolved { module, .. },
                        ..
                    }
                    | SExp::ProgramCase {
                        path: LocalAccess::Resolved { module, .. },
                        ..
                    } => *module = remapping.get(module).copied().unwrap_or(*module),
                    SExp::MathMacro {
                        scope: Some(module),
                        ..
                    }
                    | SExp::NamedMacro {
                        scope: Some(module),
                        ..
                    } => *module = remapping.get(module).copied().unwrap_or(*module),
                    _ => {}
                });
            }
            scope.remapping = remapping.clone();
            scope.substitutions.extend(substitutions.clone());
            self.scopes[id.0 as usize] = scope;
        }
        result
    }
}

impl Resolver {
    fn value(
        &mut self,
        value: &mut ValueTermExp,
        locals: &mut Vec<HashMap<String, Identifier>>,
    ) -> Result<(), Diagnostic> {
        let mut expression: SExp = value.clone().into();
        self.expression(&mut expression, locals)?;
        *value = expression.try_into().map_err(|e| self.error(e))?;
        Ok(())
    }
    fn computation(
        &mut self,
        value: &mut ComputationTermExp,
        locals: &mut Vec<HashMap<String, Identifier>>,
    ) -> Result<(), Diagnostic> {
        let mut expression: SExp = value.clone().into();
        self.expression(&mut expression, locals)?;
        *value = expression.try_into().map_err(|e| self.error(e))?;
        Ok(())
    }
    fn value_type(
        &mut self,
        value: &mut ValueTypeExp,
        locals: &mut Vec<HashMap<String, Identifier>>,
    ) -> Result<(), Diagnostic> {
        let mut expression: SExp = value.clone().into();
        self.expression(&mut expression, locals)?;
        *value = expression.try_into().map_err(|e| self.error(e))?;
        Ok(())
    }
    fn computation_type(
        &mut self,
        value: &mut ComputationTypeExp,
        locals: &mut Vec<HashMap<String, Identifier>>,
    ) -> Result<(), Diagnostic> {
        let mut expression: SExp = value.clone().into();
        self.expression(&mut expression, locals)?;
        *value = expression.try_into().map_err(|e| self.error(e))?;
        Ok(())
    }
}
