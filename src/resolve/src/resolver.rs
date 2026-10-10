#[path = "scoped.rs"]
mod scoped;
use crate::ModuleMap;
use crate::{
    bindings::{self, LocalScope},
    hir::*,
    lower,
    macros::{self, MacroBinding, MacroDefinition, MacroDefinitionId, MacroKind},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet},
    sync::Arc,
};

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct Diagnostic {
    pub error: crate::error::Error,
    pub location: Option<SourceLocation>,
    pub module: Vec<String>,
}
impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
impl std::error::Error for Diagnostic {}

type DeclarationKind = &'static str;

/// A frontend declaration whose signature need not denote a kernel type.
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct Declaration {
    pub module: Vec<String>,
    pub name: String,
    #[serde(deserialize_with = "declaration_kind")]
    pub kind: DeclarationKind,
    pub location: SourceLocation,
    pub ty: Option<String>,
}

/// A source occurrence whose lexical target is known before type inference.
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct Reference {
    pub module: Vec<String>,
    pub location: SourceLocation,
    pub target_module: Vec<String>,
    pub target_name: String,
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct Binding {
    pub module: ModuleId,
    pub name: String,
    pub parameter: Option<usize>,
}

/// Namespace correspondence for a syntactic module instantiation.
/// Elaboration fills in the corresponding typed instances after checking arguments.
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct Import {
    pub owner: ModuleId,
    pub name: String,
    pub target: ModuleId,
    pub remapping: ModuleMap,
}

/// Type-checking steps in lexical and import dependency order.
#[derive(serde::Serialize, serde::Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckStep {
    Parameters(ModuleId),
    Declaration { module: ModuleId, index: usize },
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
pub struct Project {
    pub declarations: Vec<Declaration>,
    pub modules: Vec<Module>,
    pub references: Vec<Reference>,
    pub bindings: HashMap<BindingId, Binding>,
    pub order: Vec<CheckStep>,
    pub imports: HashMap<BindingId, Import>,
}

#[derive(serde::Serialize, serde::Deserialize, Clone, Default)]
struct Scope {
    compiled: bool,
    closed: bool,
    parent: Option<ModuleId>,
    children: FxHashMap<String, ModuleId>,
    names: Arc<FxHashMap<String, BindingId>>,
    imports: FxHashMap<String, ModuleId>,
    import_ids: FxHashMap<String, BindingId>,
    macros: Vec<MacroBinding>,
    used: Vec<MacroBinding>,
    remapping: ModuleMap,
    substitutions: Arc<HashMap<BindingId, Arc<SExp>>>,
}

// A child needs the term environment at its declaration position until it is
// resolved. Macro environments and the namespace graph have their own owners.
#[derive(serde::Serialize, serde::Deserialize, Clone, Default)]
struct TermScope {
    names: Arc<FxHashMap<String, BindingId>>,
    imports: FxHashMap<String, ModuleId>,
    import_ids: FxHashMap<String, BindingId>,
}

impl Scope {
    fn terms(&self) -> TermScope {
        TermScope {
            names: self.names.clone(),
            imports: self.imports.clone(),
            import_ids: self.import_ids.clone(),
        }
    }
}

impl Scope {
    fn specialization(&self) -> Self {
        if !self.compiled {
            return self.clone();
        }
        Self {
            compiled: true,
            closed: self.closed,
            parent: self.parent,
            children: self.children.clone(),
            names: self.names.clone(),
            remapping: self.remapping.clone(),
            substitutions: self.substitutions.clone(),
            ..Self::default()
        }
    }
}

#[path = "macro_scopes.rs"]
mod macro_scopes;
use macro_scopes::{MacroWork, work_macro_names};

#[path = "structures.rs"]
mod structures;

#[derive(serde::Serialize, serde::Deserialize, Default)]
struct Resolver {
    declarations: Vec<Declaration>,
    structures: FxHashMap<BindingId, structures::Structure>,
    parameter_signatures: FxHashMap<BindingId, structures::ParameterSignature>,
    computation_bindings: HashSet<BindingId>,
    front_definitions: FxHashMap<BindingId, structures::Definition>,
    structure_values: FxHashMap<BindingId, structures::Value>,
    last_inputs: Vec<structures::Input>,
    last_parameter_checks: Vec<(SExp, SExp)>,
    module_inputs: FxHashMap<ModuleId, Vec<structures::Input>>,
    module_parameters: FxHashMap<ModuleId, Vec<RightBind>>,
    scopes: Vec<Scope>,
    input: FxHashMap<ModuleId, Module>,
    output: FxHashMap<ModuleId, Module>,
    origins: FxHashMap<ModuleId, ModuleId>,
    paths: FxHashMap<ModuleId, Vec<String>>,
    occurrences: FxHashMap<(ModuleId, String), usize>,
    states: FxHashMap<ModuleId, u8>,
    imports: HashMap<BindingId, Import>,
    module_selections: FxHashMap<ModuleId, ModuleInstantiatePath>,
    next_binding: u64,
    next_expression: u64,
    next_macro: u64,
    next_hygiene: Cell<u64>,
    location: Option<SourceLocation>,
    current: ModuleId,
    references: RefCell<Vec<Reference>>,
    // Source files stay alive throughout resolution; their Arc addresses identify
    // repeated probes of the same occurrence without copying paths or names.
    #[serde(skip)]
    reference_occurrences: RefCell<FxHashSet<(usize, ModuleId, usize, usize, BindingId)>>,
    reference_probes: Cell<u64>,
    global_bindings: HashMap<BindingId, Binding>,
    order: Vec<CheckStep>,
    declaration_scope: Option<u64>,
    public_declarations: HashSet<String>,
    next_declaration_scope: u64,
    work: FxHashMap<ModuleId, MacroWork>,
    dependency_stack: Vec<(ModuleId, usize)>,
    declaration_counts: FxHashMap<ModuleId, usize>,
    pending_macro_import: Option<ModuleItem>,
    child_term_scopes: FxHashMap<ModuleId, TermScope>,
}

pub fn resolve(modules: &[syntax::syntax::Module]) -> Result<Project, Diagnostic> {
    let _cost = timing::costs::Scope::enter("resolve.total");
    let mut resolver = Resolver::default();
    resolver.scopes.push(Scope::default());
    let mut roots: Vec<_> = {
        let _cost = timing::costs::Scope::enter("resolve.lower-syntax");
        modules.iter().cloned().map(lower::module).collect()
    };
    for module in &mut roots {
        resolver.reserve(ModuleId(0), module);
    }
    let mut ids: Vec<_> = resolver.input.keys().copied().collect();
    ids.sort_by_key(|id| id.0);
    for id in ids {
        resolver.module(id)?;
    }
    fn assemble(module: &mut Module, outputs: &mut FxHashMap<ModuleId, Module>) {
        let _cost = timing::costs::Scope::enter("resolve.assemble");
        *module = outputs.remove(&module.id).expect("resolved module");
        if let ModuleBody::Inline(items) = &mut module.body {
            for item in items {
                if let ModuleItem::ChildModule { module } = item {
                    assemble(module, outputs);
                }
            }
        }
    }
    for module in &mut roots {
        assemble(module, &mut resolver.output);
    }
    timing::costs::count("resolve.reference-probes", || {
        resolver.reference_probes.get()
    });
    timing::costs::count("resolve.references", || {
        resolver.references.borrow().len() as u64
    });
    timing::costs::count("resolve.declarations", || {
        resolver.declarations.len() as u64
    });
    timing::costs::count("resolve.scopes", || resolver.scopes.len() as u64);
    Ok(Project {
        declarations: resolver.declarations,
        order: resolver.order,
        modules: roots,
        imports: resolver.imports,
        references: resolver.references.into_inner(),
        bindings: resolver.global_bindings,
    })
}

/// Append dependency-ordered packages without reallocating earlier identities.
/// A session may only be reused after a successful append.
#[derive(Default, serde::Serialize, serde::Deserialize)]
pub struct Session {
    resolver: Resolver,
    roots: Vec<Module>,
}

impl Session {
    pub fn append(&mut self, module: &syntax::syntax::Module) -> Result<Project, Diagnostic> {
        let _cost = timing::costs::Scope::enter("resolve.package");
        let resolver = &mut self.resolver;
        if resolver.scopes.is_empty() {
            resolver.scopes.push(Scope::default());
        }
        let mut root = lower::module(module.clone());
        let first = resolver.scopes.len() as u32;
        resolver.reserve(ModuleId(0), &mut root);
        let mut ids: Vec<_> = resolver
            .input
            .keys()
            .copied()
            .filter(|id| id.0 >= first)
            .collect();
        ids.sort_by_key(|id| id.0);
        for id in ids {
            resolver.module(id)?;
        }
        fn assemble(module: &mut Module, outputs: &mut FxHashMap<ModuleId, Module>) {
            *module = outputs.remove(&module.id).expect("resolved package module");
            if let ModuleBody::Inline(items) = &mut module.body {
                for item in items {
                    if let ModuleItem::ChildModule { module } = item {
                        assemble(module, outputs);
                    }
                }
            }
        }
        assemble(&mut root, &mut resolver.output);
        self.roots.push(root);
        Ok(Project {
            declarations: resolver.declarations.clone(),
            modules: self.roots.clone(),
            references: resolver.references.borrow().clone(),
            bindings: resolver.global_bindings.clone(),
            order: resolver.order.clone(),
            imports: resolver.imports.clone(),
        })
    }

    /// Source text is omitted from checkpoints and reattached from the current snapshot.
    pub fn restore_sources(
        &mut self,
        source: impl Fn(&SourceId) -> Option<Arc<SourceFile>>,
    ) -> Option<()> {
        fn module(
            value: &mut Module,
            source: &impl Fn(&SourceId) -> Option<Arc<SourceFile>>,
        ) -> Option<()> {
            for file in [&mut value.source, &mut value.header_source]
                .into_iter()
                .flatten()
            {
                *file = source(&file.id)?;
            }
            if let ModuleBody::Inline(items) = &mut value.body {
                for item in items {
                    if let ModuleItem::ChildModule { module: child } = item {
                        module(child, source)?;
                    }
                }
            }
            Some(())
        }
        let location = |value: &mut SourceLocation| -> Option<()> {
            value.source = source(&value.source.id)?;
            Some(())
        };
        for root in &mut self.roots {
            module(root, &source)?;
        }
        let resolver = &mut self.resolver;
        for value in resolver
            .input
            .values_mut()
            .chain(resolver.output.values_mut())
        {
            module(value, &source)?;
        }
        for declaration in &mut resolver.declarations {
            location(&mut declaration.location)?;
        }
        for reference in resolver.references.get_mut() {
            location(&mut reference.location)?;
        }
        if let Some(value) = &mut resolver.location {
            location(value)?;
        }
        for scope in &mut resolver.scopes {
            for binding in scope.macros.iter_mut().chain(&mut scope.used) {
                if let Some(value) = &mut binding.introduction_location {
                    location(value)?;
                }
                if let Some(value) = &mut Arc::make_mut(&mut binding.definition).location {
                    location(value)?;
                }
            }
        }
        // No declaration is in flight at a successful package boundary.
        if !resolver.work.is_empty() || !resolver.dependency_stack.is_empty() {
            return None;
        }
        resolver.reference_occurrences.get_mut().clear();
        Some(())
    }
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
        let _cost = timing::costs::Scope::enter("resolve.reserve");
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
        let _time = timing::Scope::module(|| self.path(module.id));
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
        let body = std::mem::replace(&mut module.body, ModuleBody::External);
        self.input.insert(
            module.id,
            Module {
                body,
                ..module.clone()
            },
        );
    }
    fn path(&self, module: ModuleId) -> Vec<String> {
        let source = self.origins.get(&module).copied().unwrap_or(module);
        self.paths.get(&source).cloned().unwrap_or_default()
    }
    fn error(&self, error: impl Into<crate::error::Error>) -> Diagnostic {
        Diagnostic {
            error: error.into(),
            location: self.location.clone(),
            module: self.path(self.current),
        }
    }
    fn error_at(&self, error: impl Into<crate::error::Error>, span: SourceSpan) -> Diagnostic {
        let mut diagnostic = self.error(error);
        if let Some(location) = &mut diagnostic.location
            && location.span.start <= span.start
            && span.start < span.end
            && span.end <= location.span.end
        {
            location.span = span;
        }
        diagnostic
    }
    fn lexical(&mut self, exp: &mut SExp, scopes: &mut Vec<LocalScope>) {
        let _cost = timing::costs::Scope::enter("resolve.lexical");
        let order = self.next_expression;
        self.next_expression += 1;
        bindings::alpha_rename(exp, bindings::Mode::Resolved(order), &mut 0, scopes);
    }
    fn expression(
        &mut self,
        exp: &mut SExp,
        scopes: &mut Vec<LocalScope>,
    ) -> Result<(), Diagnostic> {
        self.expand(exp)?;
        self.expanded_expression(exp, scopes)
    }
    fn prepare_module_argument_bindings(&mut self, exp: &mut SExp, scopes: &mut Vec<LocalScope>) {
        let _cost = timing::costs::Scope::enter("resolve.module-argument-bindings");
        fn path(node: &mut SExp) -> Option<&mut Box<ModuleInstantiatePath>> {
            match node {
                SExp::ModuleInstance { path, .. } => Some(path),
                SExp::AccessPath { access, .. }
                | SExp::RecordTypeCtor { access, .. }
                | SExp::ProgramValueReference { access }
                | SExp::IndCase { path: access, .. }
                | SExp::ProgramCase { path: access, .. } => {
                    if let LocalAccess::Instantiated { path, .. } = access {
                        Some(path)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        let mut found = false;
        macros::walk_sexp_mut(exp, &mut |node| found |= path(node).is_some());
        if !found {
            return;
        }
        // Bind module arguments in their lexical scopes before normalization.
        // Other expressions retain their source form for structure expansion.
        let mut bound = exp.clone();
        self.lexical(&mut bound, scopes);
        let mut paths = Vec::new();
        macros::walk_sexp_mut(&mut bound, &mut |node| {
            if let Some(path) = path(node) {
                paths.push(path.clone());
            }
        });
        let mut paths = paths.into_iter();
        macros::walk_sexp_mut(exp, &mut |node| {
            if let Some(path) = path(node) {
                *path = paths.next().expect("matching expression traversal");
            }
        });
    }

    fn expanded_expression(
        &mut self,
        exp: &mut SExp,
        scopes: &mut Vec<LocalScope>,
    ) -> Result<(), Diagnostic> {
        self.prepare_module_argument_bindings(exp, scopes);
        self.normalize_structures(exp, scopes)?;
        self.lexical(exp, scopes);
        self.resolve_expressions(exp)
    }
    fn resolve_expressions(&self, exp: &mut SExp) -> Result<(), Diagnostic> {
        let _cost = timing::costs::Scope::enter("resolve.expressions");
        let mut result = Ok(());
        macros::walk_sexp_mut(exp, &mut |node| {
            if result.is_err() {
                return;
            }
            match node {
                SExp::ProgramValueReference { access }
                | SExp::AccessPath { access, .. }
                | SExp::RecordTypeCtor { access, .. }
                | SExp::IndCase { path: access, .. }
                | SExp::ProgramCase { path: access, .. } => {
                    result = self.access(self.current, access);
                }
                SExp::MacroParameter(_) | SExp::TokenMatch { .. } => {
                    result = Err(self.error(crate::error::Error::Invalid(
                        crate::error::Invalid::MacroTemplateSyntaxOutsideAMacroExpansion,
                    )));
                }
                _ => {}
            }
        });
        result
    }
    fn find_name(
        &self,
        mut module: ModuleId,
        name: &str,
        inherit: bool,
    ) -> Option<(ModuleId, BindingId)> {
        let spelling = name.trim_end_matches('^');
        loop {
            let scope = &self.scopes[module.0 as usize];
            if let Some(&id) = scope.names.get(spelling) {
                return Some((module, id));
            }
            if !inherit {
                return None;
            }
            module = scope.parent?;
        }
    }

    fn record_reference(&self, module: ModuleId, id: BindingId, name: &str, span: SourceSpan) {
        let Some(location) = &self.location else {
            return;
        };
        if span.end <= span.start {
            return;
        }
        self.reference_probes.set(self.reference_probes.get() + 1);
        let key = (
            Arc::as_ptr(&location.source) as usize,
            self.current,
            span.start,
            span.end,
            id,
        );
        if !self.reference_occurrences.borrow_mut().insert(key) {
            return;
        }
        self.references.borrow_mut().push(Reference {
            module: self.path(self.current),
            location: SourceLocation {
                source: location.source.clone(),
                span,
            },
            target_module: self.path(module),
            target_name: name.trim_end_matches('^').to_owned(),
        });
    }

    fn access(&self, from: ModuleId, access: &mut LocalAccess) -> Result<(), Diagnostic> {
        let _cost = timing::costs::Scope::enter("resolve.access");
        let (module, name, inherit, span) = match access {
            LocalAccess::Current { access, span } => {
                if access.1.is_some() {
                    return Ok(());
                }
                (from, &*access, true, *span)
            }
            LocalAccess::Named {
                access,
                child,
                span,
            } => (
                self.import(from, access.as_str()).ok_or_else(|| {
                    self.error_at(
                        crate::error::Error::UnknownImport {
                            name: (access.as_str()).to_owned(),
                        },
                        SourceSpan {
                            start: span.start,
                            end: span.start + access.as_str().len(),
                        },
                    )
                })?,
                &*child,
                false,
                *span,
            ),
            LocalAccess::Resolved { .. } => return Ok(()),
            LocalAccess::Instantiated { .. } => {
                return Err(self.error(crate::error::Error::Invalid(
                    crate::error::Invalid::UnresolvedModuleExpression,
                )));
            }
        };
        if let Some((module, id)) = self.find_name(module, name.as_str(), inherit) {
            self.record_reference(module, id, name.as_str(), span);
            let name = Name(name.0.clone(), Some(id));
            let display = access.to_string();
            *access = LocalAccess::Resolved {
                module,
                span,
                access: name,
                display,
            };
            return Ok(());
        }
        let name_span = SourceSpan {
            start: span.end.saturating_sub(name.as_str().len()),
            end: span.end,
        };
        Err(self.error_at(
            crate::error::Error::UnknownName {
                name: (name.as_str()).to_owned(),
            },
            name_span,
        ))
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
        let spelling = name.0.clone();
        let id = self.binding(name);
        Arc::make_mut(&mut self.scopes[self.current.0 as usize].names).insert(spelling.clone(), id);
        if let Some(scope) = self.declaration_scope
            && !self.public_declarations.contains(&spelling)
        {
            name.0 = format!("<declaration:{scope}:{spelling}>");
        }
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
        parameters: &mut Vec<RightBind>,
        locals: &mut Vec<LocalScope>,
        module: bool,
    ) -> Result<(), Diagnostic> {
        self.expand_structure_parameters(parameters, locals, module)?;
        Ok(())
    }
    fn module(&mut self, id: ModuleId) -> Result<(), Diagnostic> {
        let _cost = timing::costs::Scope::enter("resolve.module");
        let _time = timing::Scope::module(|| self.path(id));
        match self.states.get(&id) {
            Some(2) => return Ok(()),
            Some(1) => {
                if !self.dependency_stack.iter().any(|&(module, index)| {
                    self.work
                        .get(&module)
                        .and_then(|work| work.items.get(index))
                        .is_some_and(|item| matches!(item, ModuleItem::UseMacro { .. }))
                }) {
                    return Err(self.error(crate::error::Error::Invalid(
                        crate::error::Invalid::CyclicModuleImportDependency,
                    )));
                }
                let mut path = self.macro_dependency_path();
                path.push(format!("{}:module", self.path(id).join(".")));
                return Err(self.error(crate::error::Error::MacroDependencyCycle { path }));
            }
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
        let parent_terms = parent.and_then(|parent| {
            self.child_term_scopes.remove(&id).map(|snapshot| {
                let scope = &mut self.scopes[parent.0 as usize];
                let saved = (
                    scope.names.clone(),
                    scope.imports.clone(),
                    scope.import_ids.clone(),
                );
                scope.names = snapshot.names;
                scope.imports = snapshot.imports;
                scope.import_ids = snapshot.import_ids;
                (parent, saved)
            })
        });
        self.states.insert(id, 1);
        let previous = self.current;
        let declaration_scope = self.declaration_scope.take();
        let public_declarations = std::mem::take(&mut self.public_declarations);
        let location = self.location.clone();
        self.current = id;
        let input = self.input.get_mut(&id).expect("reserved module");
        let body = std::mem::replace(&mut input.body, ModuleBody::External);
        let mut module = Module {
            body,
            ..input.clone()
        };
        self.location = module
            .header_source
            .as_ref()
            .or(module.source.as_ref())
            .map(|source| SourceLocation {
                source: source.clone(),
                span: module.span,
            });
        self.parameters(&mut module.parameters, &mut Vec::new(), true)?;
        self.module_inputs.insert(id, self.last_inputs.clone());
        self.module_parameters.insert(id, module.parameters.clone());
        module.parameter_checks = self.last_parameter_checks.clone();
        self.order.push(CheckStep::Parameters(id));
        let ModuleBody::Inline(items) = &mut module.body else {
            return Err(self.error(crate::error::Error::Invalid(
                crate::error::Invalid::ExternalModuleWasNotLoaded,
            )));
        };
        self.collect_macro_scope(id, items, &module.declaration_spans, module.source.clone())?;
        for index in 0..items.len() {
            self.resolve_macro_item(id, index)?;
        }
        self.record_macro_template_references(id);
        let work = self.work.remove(&id).expect("module work");
        *items = work.output;
        module.declaration_spans = work.output_spans;
        self.output.insert(id, module);
        self.states.insert(id, 2);
        self.current = previous;
        self.declaration_scope = declaration_scope;
        self.public_declarations = public_declarations;
        self.location = location;
        if let Some((parent, (names, imports, import_ids))) = parent_terms {
            let scope = &mut self.scopes[parent.0 as usize];
            scope.names = names;
            scope.imports = imports;
            scope.import_ids = import_ids;
        }
        Ok(())
    }
    fn item(&mut self, item: &mut ModuleItem) -> Result<(), Diagnostic> {
        let mut locals = Vec::new();
        match item {
            ModuleItem::SetStructure {
                name,
                parameters,
                fields,
                ..
            } => {
                self.parameters(parameters, &mut locals, false)?;
                self.publish(name);
                self.register_parameter_signature(name, parameters);
                for (name, ty) in fields {
                    self.expression(ty, &mut locals)?;
                    self.binding(name);
                    locals.push(LocalScope::from_iter([(name.0.clone(), name.clone())]));
                }
            }
            ModuleItem::Structure { .. } => {
                unreachable!("structure signatures are expanded before ordinary declarations")
            }
            ModuleItem::Scoped { .. } => {
                unreachable!("declaration scopes are flattened before elaboration")
            }
            ModuleItem::Definition {
                owner,
                name,
                binders,
                ty,
                body,
            } => {
                if let Some(owner) = owner {
                    let mut access = LocalAccess::Current {
                        span: Default::default(),
                        access: owner.type_name.clone(),
                    };
                    self.access(self.current, &mut access)?;
                    if let LocalAccess::Resolved { access, .. } = access
                        && let Some(binding) = access.1.and_then(|id| self.global_bindings.get(&id))
                    {
                        owner.type_name.0 = binding.name.clone();
                    }
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
                let inputs = self.last_inputs.clone();
                let checks = self.last_parameter_checks.clone();
                self.parameters(indices, &mut locals.clone(), false)?;
                self.publish(type_name);
                self.last_inputs = inputs;
                self.last_parameter_checks = checks;
                self.register_parameter_signature(type_name, parameters);
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
                self.register_parameter_signature(type_name, parameters);
                for (name, ty) in fields {
                    self.expression(ty, &mut locals)?;
                    self.binding(name);
                    locals.push(LocalScope::from_iter([(name.0.clone(), name.clone())]));
                }
            }
            ModuleItem::ChildModule { module } => {
                self.child_term_scopes
                    .insert(module.id, self.scopes[self.current.0 as usize].terms());
            }
            ModuleItem::Import {
                path,
                import_name,
                checks,
            } => self.resolve_import(path, import_name, checks)?,
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
                path,
                macro_name,
                name,
            } => {
                let mut internal = Identifier(format!("<macro-use:{}>", self.next_binding));
                let mut checks = Vec::new();
                let alias = if let ModuleInstantiatePath::FromImport { import_name, calls } = path {
                    if calls.is_empty() {
                        self.import(self.current, import_name.as_str())
                    } else {
                        None
                    }
                } else {
                    None
                };
                let target = if let Some(target) = alias {
                    target
                } else {
                    self.resolve_import(path, &mut internal, &mut checks)?;
                    self.imports[&internal.1.unwrap()].target
                };
                let mut definition = self.scopes[target.0 as usize]
                    .macros
                    .iter()
                    .chain(&self.scopes[target.0 as usize].used)
                    .find(|d| d.name.as_str() == macro_name.as_str())
                    .cloned()
                    .ok_or_else(|| {
                        self.error(crate::error::Error::UnknownImportedMacro {
                            module: internal.0.clone(),
                            name: macro_name.0.clone(),
                        })
                    })?;
                definition.name = name.clone();
                definition.instance = target;
                definition.introduction_location = self.location.clone();
                definition.declaration_order = (
                    self.location.as_ref().map_or(0, |l| l.span.start),
                    self.dependency_stack
                        .iter()
                        .rev()
                        .find_map(|&(module, index)| (module == self.current).then_some(index))
                        .unwrap_or(0),
                );
                self.scopes[self.current.0 as usize].used.push(definition);
                // Elaboration checks and instantiates this private import normally.
                self.pending_macro_import = alias.is_none().then(|| ModuleItem::Import {
                    path: path.clone(),
                    import_name: internal,
                    checks,
                });
            }
            ModuleItem::Eval { exp }
            | ModuleItem::Normalize { exp }
            | ModuleItem::Infer { exp } => self.expression(exp, &mut locals)?,
            ModuleItem::Check { exp, ty } => {
                self.expression(exp, &mut locals)?;
                self.expression(ty, &mut locals)?;
            }
            ModuleItem::MemberCheck { value, ty } => {
                self.expression(value, &mut locals)?;
                self.expression(ty, &mut locals)?;
            }
            ModuleItem::ValueTypeCheck { ty } => self.value_type(ty, &mut locals)?,
        }
        Ok(())
    }
    fn visible(&self, mut module: ModuleId) -> Vec<&MacroBinding> {
        let mut result = Vec::new();
        let mut seen = HashSet::new();
        loop {
            let scope = &self.scopes[module.0 as usize];
            result.extend(
                scope
                    .macros
                    .iter()
                    .chain(&scope.used)
                    .filter(|d| seen.insert(d.name.0.clone())),
            );
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
        if name.as_str().contains("::[") {
            self.expand(template)?;
        }
        let mut expansion = Ok(());
        macros::walk_sexp_control(template, &mut |node| {
            if expansion.is_err() {
                return false;
            }
            if let SExp::AccessPath { access, parameters } = node
                && let Some(next) = self.expand_type_member(access, parameters)
            {
                match next {
                    Ok(ty) => *node = ty,
                    Err(error) => expansion = Err(error),
                }
            }
            true
        });
        expansion?;
        if self.scopes[self.current.0 as usize]
            .used
            .iter()
            .chain(
                self.scopes[self.current.0 as usize]
                    .macros
                    .iter()
                    .filter(|d| d.prepared),
            )
            .any(|d| d.name.as_str() == name.as_str())
        {
            return Err(self.error(crate::error::Error::DuplicateMacro {
                name: (name.as_str()).to_owned(),
            }));
        }
        let mut captures = HashMap::new();
        let mut fixed = 0;
        macros::pattern_captures(pattern, &mut captures, &mut fixed, kind)
            .map_err(|e| self.error(e))?;
        if kind == MacroKind::Math && fixed == 0 {
            return Err(self.error(crate::error::Error::MathMacroWithoutFixedToken {
                name: (name.as_str()).to_owned(),
            }));
        }
        let mut has_match = false;
        macros::walk_sexp_mut(template, &mut |node| {
            has_match |= matches!(node, SExp::TokenMatch { .. })
        });
        if kind == MacroKind::Math && has_match {
            return Err(self.error(crate::error::Error::Invalid(
                crate::error::Invalid::TokenMatchingIsOnlyValidInNamedMacros,
            )));
        }
        macros::validate_template(template, &captures).map_err(|e| self.error(e))?;
        macros::rename_template_binders(template, self.fresh_hygiene());
        let order = self.scopes[self.current.0 as usize]
            .macros
            .iter()
            .find(|d| d.name.as_str() == name.as_str())
            .map(|d| d.declaration_order)
            .unwrap_or((
                self.location.as_ref().map_or(0, |l| l.span.start),
                self.next_macro as usize,
            ));
        self.next_macro += 1;
        self.prepare_module_argument_bindings(template, &mut Vec::new());
        self.normalize_structures(template, &[])?;
        let mut result = Ok(());
        macros::walk_sexp_mut(template, &mut |node| {
            if result.is_err() {
                return;
            }
            match node {
                SExp::MathMacro { scope, .. } | SExp::NamedMacro { scope, .. } => {
                    *scope = Some(self.current);
                }
                SExp::ProgramValueReference { access }
                | SExp::AccessPath { access, .. }
                | SExp::RecordTypeCtor { access, .. }
                | SExp::IndCase { path: access, .. }
                | SExp::ProgramCase { path: access, .. }
                    if !matches!(&*access, LocalAccess::Current { access, .. } if access.as_str().starts_with("<macro:")) =>
                {
                    result = self.access(self.current, access);
                }
                _ => {}
            }
        });
        result?;
        let mut result = Ok(());
        let mut visible: HashSet<_> = self
            .visible(self.current)
            .iter()
            .filter(|d| d.kind == MacroKind::Named)
            .map(|d| d.name.0.clone())
            .collect();
        if let Some(work) = self.work.get(&self.current) {
            visible.extend(work_macro_names(work));
        }
        let definitions: HashMap<_, _> = self
            .visible(self.current)
            .into_iter()
            .filter(|d| d.kind == MacroKind::Named)
            .map(|d| (d.name.0.clone(), d.id))
            .collect();
        macros::walk_sexp_mut(template, &mut |node| {
            if let SExp::NamedMacro { name: nested, .. } = node {
                nested.1 = definitions.get(nested.as_str()).map(|id| BindingId(id.0));
            }
            if let SExp::NamedMacro { name: nested, .. } = node
                && !visible.contains(nested.as_str())
                && !(kind == MacroKind::Named && nested.as_str() == name.as_str())
            {
                result = Err(self.error(crate::error::Error::MacroUnavailableInTemplate {
                    name: (nested.as_str()).to_owned(),
                }));
            }
        });
        result?;
        let definition_id = self.scopes[self.current.0 as usize]
            .macros
            .iter()
            .find(|d| d.name.as_str() == name.as_str())
            .map_or(MacroDefinitionId(self.next_macro), |d| d.id);
        self.scopes[self.current.0 as usize]
            .macros
            .retain(|d| d.name.as_str() != name.as_str());
        self.scopes[self.current.0 as usize]
            .macros
            .push(MacroBinding {
                name: name.clone(),
                instance: self.current,
                declaration_order: order,
                introduction_location: self.location.clone(),
                definition: Arc::new(MacroDefinition {
                    id: definition_id,
                    kind,
                    pattern: pattern.to_vec(),
                    template: template.clone(),
                    definition_scope: self.current,
                    definition_name: name.0.clone(),
                    prepared: true,
                    location: self.location.clone(),
                }),
            });
        Ok(())
    }
    fn expand(&mut self, exp: &mut SExp) -> Result<(), Diagnostic> {
        let _cost = timing::costs::Scope::enter("resolve.macro-expansion");
        let mut result = Ok(());
        macros::walk_sexp_control(exp, &mut |node| {
            if result.is_err() {
                return false;
            }
            loop {
                let next = match node {
                    SExp::AccessPath { access, parameters } => {
                        let Some(next) = self.expand_type_member(access, parameters) else {
                            return true;
                        };
                        next
                    }
                    SExp::NamedMacro {
                        name,
                        tokens,
                        scope,
                        depth,
                    } => self.expand_one(scope.unwrap_or(self.current), Some(name), tokens, *depth),
                    SExp::MathMacro {
                        tokens,
                        scope,
                        depth,
                    } => self.expand_one(scope.unwrap_or(self.current), None, tokens, *depth),
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
        &mut self,
        scope: ModuleId,
        name: Option<&Identifier>,
        tokens: &[MacroExp],
        depth: u16,
    ) -> Result<SExp, Diagnostic> {
        if depth >= macros::MAX_MACRO_EXPANSION_DEPTH {
            let definition = self.visible(scope).into_iter().find(|d| {
                name.map_or(d.kind == MacroKind::Math, |name| {
                    d.name.as_str() == name.as_str()
                })
            });
            return Err(self.error(if let Some(definition) = definition {
                crate::error::Error::MacroExpansionLimit {
                    limit: macros::MAX_MACRO_EXPANSION_DEPTH as usize,
                    name: definition.definition_name.clone(),
                    module: self.path(definition.definition_scope).join("."),
                    definition: definition
                        .location
                        .as_ref()
                        .map_or(SourceSpan::default(), |l| l.span),
                }
            } else {
                crate::error::Error::MacroDepthExceeded {
                    limit: macros::MAX_MACRO_EXPANSION_DEPTH as usize,
                }
            }));
        }
        let tokens = if name.is_none() {
            tokens
                .iter()
                .map(|token| match token {
                    MacroExp::Seq(tokens) => self
                        .expand_one(scope, None, tokens, depth + 1)
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
        self.ensure_macro_bindings(scope, name)?;
        let mut candidates = self
            .visible(scope)
            .into_iter()
            .filter(|d| {
                if let Some(name) = name {
                    d.kind == MacroKind::Named
                        && d.name.as_str() == name.as_str()
                        && name.1.is_none_or(|id| d.id.0 == id.0)
                } else {
                    d.kind == MacroKind::Math
                }
            })
            .cloned()
            .collect::<Vec<_>>();
        if name.is_none() {
            candidates.sort_by_key(|d| {
                (
                    macros::first_fixed_position(&d.pattern),
                    self.macro_distance(scope, d),
                    d.declaration_order,
                )
            });
        }
        for mut definition in candidates {
            self.record_macro_reference(&definition, name);
            self.prepare_macro_definition(scope, &mut definition)?;
            let mut captures = HashMap::new();
            if macros::match_pattern(&definition.pattern, &tokens, &mut captures) {
                return macros::instantiate_template(
                    &definition,
                    &captures,
                    depth,
                    self.fresh_hygiene(),
                )
                .map_err(|e| self.error(e));
            }
            if name.is_some() {
                return Err(self.error(crate::error::Error::MacroPatternMismatch {
                    name: (definition.name.as_str()).to_owned(),
                }));
            }
        }
        if name.is_none()
            && let Some((module, index)) = self.active_macro_use(scope)
        {
            return Err(self.macro_cycle(module, index));
        }
        Err(self.error(name.map_or_else(
            || crate::error::Error::Invalid(crate::error::Invalid::NoVisibleMathMacro),
            |name| crate::error::Error::UnknownNamedMacro {
                name: (name.as_str()).to_owned(),
            },
        )))
    }
    fn resolve_import(
        &mut self,
        path: &mut ModuleInstantiatePath,
        name: &mut Identifier,
        checks: &mut Vec<(SExp, SExp)>,
    ) -> Result<(), Diagnostic> {
        self.resolve_import_in_scope(path, name, checks, &[])
    }

    fn resolve_import_in_scope(
        &mut self,
        path: &mut ModuleInstantiatePath,
        name: &mut Identifier,
        checks: &mut Vec<(SExp, SExp)>,
        locals: &[LocalScope],
    ) -> Result<(), Diagnostic> {
        let _cost = timing::costs::Scope::enter("resolve.import");
        let (mut target, calls) = match path {
            ModuleInstantiatePath::FromModule { module, calls } => (*module, calls),
            ModuleInstantiatePath::FromRoot { calls } => (ModuleId(0), calls),
            ModuleInstantiatePath::FromCurrent { back_parent, calls } => {
                let mut base = self.current;
                for _ in 0..*back_parent {
                    base = self.scopes[base.0 as usize].parent.ok_or_else(|| {
                        self.error(crate::error::Error::Invalid(
                            crate::error::Invalid::AlreadyAtRootModule,
                        ))
                    })?;
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
                            self.error(crate::error::Error::UnknownImport {
                                name: (import_name.as_str()).to_owned(),
                            })
                        })?,
                    calls,
                )
            }
        };
        let selection_source = target;
        let mut remapping = self.scopes[target.0 as usize].remapping.fork();
        let mut substitutions: HashMap<_, _> = self.scopes[target.0 as usize]
            .substitutions
            .iter()
            .map(|(&id, value)| (id, (**value).clone()))
            .collect();
        let mut route = Vec::new();
        for (child, arguments) in calls.iter_mut() {
            for (_, argument) in arguments.iter_mut() {
                self.expand(argument)?;
                // Check the supplied expression before expanding definitions:
                // their internal inference holes belong to their own bodies.
                let mut has_meta = false;
                macros::walk_sexp_control(argument, &mut |node| {
                    if matches!(node, SExp::Meta { .. }) {
                        has_meta = true;
                        false
                    } else {
                        true
                    }
                });
                if has_meta {
                    return Err(self.error(crate::error::Error::Invalid(
                        crate::error::Invalid::ModuleArgumentsDoNotAllowInferenceHolesOr,
                    )));
                }
                let mut template = false;
                macros::walk_sexp_mut(argument, &mut |node| {
                    template |= matches!(node, SExp::MacroParameter(_));
                });
                if !template {
                    self.expanded_expression(argument, &mut locals.to_vec())?;
                }
            }
            target = *self.scopes[target.0 as usize]
                .children
                .get(child.as_str())
                .ok_or_else(|| {
                    self.error(crate::error::Error::UnknownChildModule {
                        name: (child.as_str()).to_owned(),
                    })
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
            let inputs = self.module_inputs.get(&target).cloned().unwrap_or_default();
            let mut argument_substitutions = substitutions.clone();
            for (name, argument) in arguments.iter() {
                if let Some(id) = self.scopes[target.0 as usize].names.get(name.as_str()) {
                    argument_substitutions.insert(*id, argument.clone());
                }
            }
            let mut expanded = Vec::new();
            for (name, argument) in std::mem::take(arguments) {
                if let Some(input) = inputs.iter().find(|input| input.name == name.as_str()) {
                    if input.signature.is_some() {
                        let mut input = input.clone();
                        for expression in input.arguments.values_mut() {
                            *expression =
                                structures::substitute(expression, &argument_substitutions);
                        }
                        for bind in &mut input.callback_parameters {
                            *bind.ty = structures::substitute(&bind.ty, &argument_substitutions);
                        }
                        let (fields, guards) =
                            self.callback_arguments(&input, &argument, locals)?;
                        checks.extend(guards);
                        for (path, expression) in input.fields.iter().zip(fields) {
                            expanded.push((Identifier(format!("{}.{}", name.0, path)), expression));
                        }
                        continue;
                    }
                    if input.computation {
                        expanded.push((
                            name,
                            SExp::Thunk {
                                computation: Box::new(argument),
                            },
                        ));
                        continue;
                    }
                }
                expanded.push((name, argument));
            }
            // Flattening a structure argument can expose specialized module
            // references in field ascriptions that were absent from its surface.
            for (_, argument) in &mut expanded {
                let mut template = false;
                macros::walk_sexp_mut(argument, &mut |node| {
                    template |= matches!(node, SExp::MacroParameter(_));
                });
                if !template {
                    self.expanded_expression(argument, &mut locals.to_vec())?;
                }
            }
            *arguments = expanded;
            for (name, argument) in arguments {
                if let Some(id) = self.scopes[target.0 as usize].names.get(name.as_str()) {
                    name.1 = Some(*id);
                    substitutions.insert(*id, argument.clone());
                }
            }
            route.push(target);
        }
        for (value, ty) in checks.iter_mut() {
            for expression in [value, ty] {
                let mut template = false;
                macros::walk_sexp_mut(expression, &mut |node| {
                    template |= matches!(node, SExp::MacroParameter(_));
                });
                if !template {
                    self.expanded_expression(expression, &mut locals.to_vec())?;
                }
            }
        }
        let destination = route.last().copied();
        for source in route {
            // Parameterless ancestors contribute no argument environment.
            if Some(source) != destination
                && self
                    .module_parameters
                    .get(&source)
                    .is_none_or(Vec::is_empty)
            {
                continue;
            }
            target = self.instantiate(source, &mut remapping, &substitutions);
        }
        let mut selection = self
            .module_selections
            .get(&selection_source)
            .cloned()
            .unwrap_or_else(|| {
                if selection_source == ModuleId(0) {
                    ModuleInstantiatePath::FromRoot { calls: Vec::new() }
                } else {
                    ModuleInstantiatePath::FromModule {
                        module: selection_source,
                        calls: Vec::new(),
                    }
                }
            });
        let selected_calls = match &mut selection {
            ModuleInstantiatePath::FromModule { calls, .. }
            | ModuleInstantiatePath::FromCurrent { calls, .. }
            | ModuleInstantiatePath::FromRoot { calls }
            | ModuleInstantiatePath::FromImport { calls, .. } => calls,
        };
        selected_calls.extend(calls.clone());
        if selected_calls
            .iter()
            .any(|(_, arguments)| !arguments.is_empty())
        {
            self.module_selections.insert(target, selection);
        }
        let spelling = name.0.clone();
        if let Some(scope) = self.declaration_scope {
            name.0 = format!("<declaration:{scope}:{spelling}>");
        }
        let id = self.binding(name);
        self.scopes[self.current.0 as usize]
            .imports
            .insert(spelling.clone(), target);
        self.scopes[self.current.0 as usize]
            .import_ids
            .insert(spelling, id);
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
        remapping: &mut ModuleMap,
        substitutions: &HashMap<BindingId, SExp>,
    ) -> ModuleId {
        let _cost = timing::costs::Scope::enter("resolve.instantiate");
        if substitutions.is_empty() && remapping.is_empty() && self.states.get(&source) == Some(&2)
        {
            // A completed, unchanged namespace needs only a fresh alias.
            // Its descendants retain their original lexical environments.
            let id = ModuleId(self.scopes.len() as u32);
            let mut scope = self.scopes[source.0 as usize].specialization();
            let mut ancestor = Some(source);
            scope.closed = true;
            while let Some(module) = ancestor {
                let origin = self.origins.get(&module).copied().unwrap_or(module);
                if self
                    .module_parameters
                    .get(&origin)
                    .is_some_and(|p| !p.is_empty())
                {
                    scope.closed = false;
                    break;
                }
                ancestor = self.scopes[origin.0 as usize].parent;
            }
            remapping.insert(source, id);
            scope.remapping = remapping.clone();
            self.scopes.push(scope);
            self.origins
                .insert(id, self.origins.get(&source).copied().unwrap_or(source));
            if let Some(path) = self.module_selections.get(&source).cloned() {
                self.module_selections.insert(id, path);
            }
            return id;
        }
        fn allocate(
            resolver: &mut Resolver,
            source: ModuleId,
            map: &mut ModuleMap,
            pairs: &mut Vec<(ModuleId, ModuleId)>,
            allocated: &mut FxHashMap<ModuleId, ModuleId>,
        ) -> ModuleId {
            if let Some(id) = allocated.get(&source) {
                return *id;
            }
            let id = ModuleId(resolver.scopes.len() as u32);
            resolver.scopes.push(Scope::default());
            map.insert(source, id);
            allocated.insert(source, id);
            pairs.push((source, id));
            resolver
                .origins
                .insert(id, resolver.origins.get(&source).copied().unwrap_or(source));
            // Child selection starts from the child's original declaration and
            // applies this namespace's argument environment in resolve_import.
            // Reserve a specialized child only when that child is selected.
            id
        }
        *remapping = remapping.fork();
        let mut pairs = Vec::new();
        let mut allocated = FxHashMap::default();
        // Compiled definitions expose references, not their internal imports.
        // Typed namespace instantiation specializes their checked bodies.
        let scope = &self.scopes[source.0 as usize];
        let mut imports: Vec<_> = if scope.compiled {
            Vec::new()
        } else {
            scope.imports.values().copied().collect()
        };
        imports.sort_by_key(|id| id.0);
        for import in imports {
            // A namespace with no enclosing parameters cannot depend on this
            // specialization. Keep its imports and descendants shared too.
            if self.scopes[import.0 as usize].closed {
                continue;
            }
            allocate(self, import, remapping, &mut pairs, &mut allocated);
        }
        let result = allocate(self, source, remapping, &mut pairs, &mut allocated);
        if std::env::var_os("REF_TYPE_PROFILE_RESOLVE").is_some() {
            eprintln!(
                "resolve instantiate={} scopes={} total={} remapping={}",
                self.path(source).join("."),
                pairs.len(),
                self.scopes.len(),
                remapping.owned_len()
            );
        }
        // Every scope in this graph has the same completed correspondence.
        // Sharing immutable maps avoids copying the whole graph per scope.
        let shared_remapping = remapping.clone();
        let shared_arguments: HashMap<_, _> = substitutions
            .iter()
            .map(|(&id, value)| (id, Arc::new(value.clone())))
            .collect();
        let mut merged_substitutions: HashMap<usize, Arc<HashMap<BindingId, Arc<SExp>>>> =
            HashMap::new();
        for (source, id) in pairs {
            let mut scope = self.scopes[source.0 as usize].specialization();
            scope.parent = scope
                .parent
                .map(|id| remapping.get(&id).copied().unwrap_or(id));
            for import in scope.imports.values_mut() {
                *import = remapping.get(import).copied().unwrap_or(*import);
            }
            for definition in scope.macros.iter_mut().chain(&mut scope.used) {
                definition.instance = remapping
                    .get(&definition.instance)
                    .copied()
                    .unwrap_or(definition.instance);
                definition.definition_scope = remapping
                    .get(&definition.definition_scope)
                    .copied()
                    .unwrap_or(definition.definition_scope);
                macros::walk_sexp_control(&mut definition.template, &mut |node| {
                    if let SExp::ProgramValueReference {
                        access:
                            LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. },
                    } = node
                        && let Some(argument) = access.1.and_then(|id| substitutions.get(&id))
                    {
                        *node = argument.clone();
                        return false;
                    }
                    if let SExp::AccessPath {
                        access:
                            LocalAccess::Current { access, .. } | LocalAccess::Resolved { access, .. },
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
                    SExp::ModuleInstance { path, import_name } => {
                        if let ModuleInstantiatePath::FromModule { module, .. } = path.as_mut() {
                            *module = remapping.get(module).copied().unwrap_or(*module);
                        }
                        if let Some(mut import) =
                            import_name.1.and_then(|id| self.imports.get(&id)).cloned()
                        {
                            import.target = remapping
                                .get(&import.target)
                                .copied()
                                .unwrap_or(import.target);
                            for target in import.remapping.values_mut() {
                                *target = remapping.get(target).copied().unwrap_or(*target);
                            }
                            import_name.1 = None;
                            let binding = self.binding(import_name);
                            self.imports.insert(binding, import);
                        }
                    }
                    SExp::AccessPath {
                        access: LocalAccess::Resolved { module, .. },
                        ..
                    }
                    | SExp::RecordTypeCtor {
                        access: LocalAccess::Resolved { module, .. },
                        ..
                    }
                    | SExp::ProgramValueReference {
                        access: LocalAccess::Resolved { module, .. },
                    }
                    | SExp::IndCase {
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
            scope.remapping = shared_remapping.clone();
            let key = if scope.substitutions.is_empty() {
                0
            } else {
                Arc::as_ptr(&scope.substitutions) as usize
            };
            let merged = merged_substitutions.entry(key).or_insert_with(|| {
                // Imported expressions can already contain arguments from an
                // enclosing specialization. Compose that environment before
                // adding the new arguments; insertion alone leaves those
                // expressions referring to the original enclosing parameters.
                let mut merged: HashMap<_, _> = scope
                    .substitutions
                    .iter()
                    .map(|(id, expression)| {
                        (
                            *id,
                            structures::substitute_shared(expression, substitutions),
                        )
                    })
                    .collect();
                merged.extend(shared_arguments.clone());
                Arc::new(merged)
            });
            scope.substitutions = merged.clone();
            if let Some(path) = self.module_selections.get(&source) {
                let expression = SExp::ModuleInstance {
                    path: Box::new(path.clone()),
                    import_name: Identifier("<selection>".into()),
                };
                let mut expression = structures::substitute(&expression, substitutions);
                structures::remap_modules(&mut expression, remapping);
                let SExp::ModuleInstance { path, .. } = expression else {
                    unreachable!()
                };
                self.module_selections.insert(id, *path);
            }
            self.scopes[id.0 as usize] = scope;
        }
        result
    }
}

impl Resolver {
    fn value_type(
        &mut self,
        value: &mut ValueTypeExp,
        locals: &mut Vec<LocalScope>,
    ) -> Result<(), Diagnostic> {
        let mut expression: SExp = value.clone().into();
        self.expression(&mut expression, locals)?;
        *value = expression.try_into().map_err(|e| self.error(e))?;
        Ok(())
    }
}

fn declaration_kind<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<&'static str, D::Error> {
    let value = <String as serde::Deserialize>::deserialize(deserializer)?;
    match value.as_str() {
        "definition" => Ok("definition"),
        "inductive" => Ok("inductive"),
        "structure" => Ok("structure"),
        "macro" => Ok("macro"),
        "import" => Ok("import"),
        "constructor" => Ok("constructor"),
        "field" => Ok("field"),
        "parameter" => Ok("parameter"),
        _ => Err(serde::de::Error::custom("unknown declaration kind")),
    }
}

impl diagnostics::DiagnosticError for Diagnostic {
    fn diagnostic_data(&self) -> diagnostics::DiagnosticData {
        let mut data = self.error.diagnostic_data().with(
            "module",
            diagnostics::Value::List(self.module.iter().cloned().map(Into::into).collect()),
        );
        if let Some(location) = &self.location {
            data = data
                .with("file", location.source.id.0.to_string_lossy().into_owned())
                .with("start", location.span.start)
                .with("end", location.span.end);
        }
        data
    }
}
