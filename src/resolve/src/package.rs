//! Resolver package boundaries, owned tables, and transactional relocation.
use super::*;
use artifact::{Identity, Relocate, Relocation};

const SPACES: [&str; 5] = [
    "resolve.module",
    "resolve.binding",
    "resolve.macro",
    "resolve.expression",
    "resolve.hygiene",
];

#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub struct PackageBoundary {
    counters: [u64; 5],
    declarations: usize,
    references: usize,
    order: usize,
    roots: usize,
}

#[derive(serde::Serialize, serde::Deserialize)]
struct Allocations([Vec<u64>; 5]);
impl Relocate for Allocations {
    fn relocate(&mut self, r: &mut Relocation) -> artifact::Result<()> {
        for (space, values) in SPACES.into_iter().zip(&mut self.0) {
            for value in values {
                *value = r.id(space, *value)?;
            }
        }
        Ok(())
    }
}

#[derive(Relocate, serde::Serialize, serde::Deserialize)]
struct StoredMacro {
    name: Identifier,
    definition: MacroDefinitionId,
    instance: ModuleId,
    declaration_order: (usize, usize),
    introduction_location: Option<SourceLocation>,
}
impl StoredMacro {
    fn capture(value: &MacroBinding) -> Self {
        Self {
            name: value.name.clone(),
            definition: value.definition.id,
            instance: value.instance,
            declaration_order: value.declaration_order,
            introduction_location: value.introduction_location.clone(),
        }
    }
    fn restore(
        self,
        definitions: &HashMap<MacroDefinitionId, Arc<MacroDefinition>>,
    ) -> artifact::Result<MacroBinding> {
        Ok(MacroBinding {
            name: self.name,
            definition: definitions
                .get(&self.definition)
                .cloned()
                .ok_or_else(|| artifact::Error("missing imported macro definition".into()))?,
            instance: self.instance,
            declaration_order: self.declaration_order,
            introduction_location: self.introduction_location,
        })
    }
}

/// A package owns each table entry exactly once. Macro imports contain only
/// definition identities, so dependency templates are never copied into a user.
#[derive(Relocate, serde::Serialize, serde::Deserialize)]
pub struct PackageExport {
    allocations: Allocations,
    data: Resolver,
    scopes: Vec<(ModuleId, Scope)>,
    scope_macros: Vec<(ModuleId, Vec<StoredMacro>, Vec<StoredMacro>)>,
    definitions: Vec<Arc<MacroDefinition>>,
    root_children: FxHashMap<String, ModuleId>,
    roots: Vec<Module>,
}
impl PackageExport {
    pub fn owned_ids(&self) -> Vec<Identity> {
        SPACES
            .into_iter()
            .zip(&self.allocations.0)
            .flat_map(|(space, values)| {
                values.iter().map(move |&value| Identity::Scalar {
                    space: space.into(),
                    value,
                })
            })
            .collect()
    }
    pub fn module_count(&self) -> usize {
        self.scopes.len()
    }
    pub fn order(&self) -> &[CheckStep] {
        &self.data.order
    }

    pub fn owns_binding(&self, binding: BindingId) -> bool {
        let (space, value) = if binding.0 & (1 << 63) == 0 {
            (1, binding.0)
        } else {
            (3, (binding.0 >> 32) & 0x7fff_ffff)
        };
        self.allocations.0[space].binary_search(&value).is_ok()
    }
}

impl Session {
    pub fn contains_package(&self, name: &str) -> bool {
        self.roots.iter().any(|module| module.name.as_str() == name)
    }

    pub fn order(&self) -> &[CheckStep] {
        &self.resolver.order
    }

    pub fn references(&self) -> std::cell::Ref<'_, Vec<Reference>> {
        self.resolver.references.borrow()
    }

    fn counters(&self) -> [u64; 5] {
        let r = &self.resolver;
        [
            r.scopes.len().max(1) as u64,
            r.next_binding,
            r.next_macro,
            r.next_expression,
            r.next_hygiene.get(),
        ]
    }
    pub fn boundary(&self) -> PackageBoundary {
        PackageBoundary {
            counters: self.counters(),
            declarations: self.resolver.declarations.len(),
            references: self.resolver.references.borrow().len(),
            order: self.resolver.order.len(),
            roots: self.roots.len(),
        }
    }
    pub fn export_package(&self, boundary: &PackageBoundary) -> artifact::Result<PackageExport> {
        let r = &self.resolver;
        let ends = self.counters();
        if boundary
            .counters
            .iter()
            .zip(ends)
            .any(|(start, end)| *start > end)
            || boundary.declarations > r.declarations.len()
            || boundary.references > r.references.borrow().len()
            || boundary.order > r.order.len()
            || boundary.roots > self.roots.len()
            || !r.work.is_empty()
            || !r.dependency_stack.is_empty()
        {
            return Err(artifact::Error("invalid resolver package boundary".into()));
        }
        let own_module = |id: &ModuleId| (boundary.counters[0]..ends[0]).contains(&(id.0 as u64));
        let own_binding = |id: &BindingId| (boundary.counters[1]..ends[1]).contains(&id.0);
        let mut data = Resolver {
            declarations: r.declarations[boundary.declarations..].to_vec(),
            references: RefCell::new(r.references.borrow()[boundary.references..].to_vec()),
            order: r.order[boundary.order..].to_vec(),
            module_inputs: r
                .module_inputs
                .iter()
                .filter(|(id, _)| own_module(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            module_parameters: r
                .module_parameters
                .iter()
                .filter(|(id, _)| own_module(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            input: r
                .input
                .iter()
                .filter(|(id, _)| own_module(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            output: r
                .output
                .iter()
                .filter(|(id, _)| own_module(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            origins: r
                .origins
                .iter()
                .filter(|(id, _)| own_module(id))
                .map(|(&id, value)| (id, *value))
                .collect(),
            paths: r
                .paths
                .iter()
                .filter(|(id, _)| own_module(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            states: r
                .states
                .iter()
                .filter(|(id, _)| own_module(id))
                .map(|(&id, value)| (id, *value))
                .collect(),
            module_selections: r
                .module_selections
                .iter()
                .filter(|(id, _)| own_module(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            declaration_counts: r
                .declaration_counts
                .iter()
                .filter(|(id, _)| own_module(id))
                .map(|(&id, value)| (id, *value))
                .collect(),
            child_term_scopes: r
                .child_term_scopes
                .iter()
                .filter(|(id, _)| own_module(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            structures: r
                .structures
                .iter()
                .filter(|(id, _)| own_binding(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            parameter_signatures: r
                .parameter_signatures
                .iter()
                .filter(|(id, _)| own_binding(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            front_definitions: r
                .front_definitions
                .iter()
                .filter(|(id, _)| own_binding(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            structure_values: r
                .structure_values
                .iter()
                .filter(|(id, _)| own_binding(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            imports: r
                .imports
                .iter()
                .filter(|(id, _)| own_binding(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            global_bindings: r
                .global_bindings
                .iter()
                .filter(|(id, _)| own_binding(id))
                .map(|(&id, value)| (id, value.clone()))
                .collect(),
            computation_bindings: r
                .computation_bindings
                .iter()
                .copied()
                .filter(&own_binding)
                .collect(),
            ..Resolver::default()
        };
        let root_children: FxHashMap<_, _> = r
            .scopes
            .first()
            .into_iter()
            .flat_map(|scope| &scope.children)
            .filter(|(_, id)| own_module(id))
            .map(|(name, &id)| (name.clone(), id))
            .collect();
        data.occurrences = r
            .occurrences
            .iter()
            .filter(|((module, name), _)| {
                own_module(module) || (*module == ModuleId(0) && root_children.contains_key(name))
            })
            .map(|(key, &value)| (key.clone(), value))
            .collect();
        let mut scopes = Vec::new();
        let mut scope_macros = Vec::new();
        let mut definitions = HashMap::new();
        for index in boundary.counters[0] as usize..r.scopes.len() {
            let id = ModuleId(index as u32);
            let mut scope = r.scopes[index].clone();
            let macros = std::mem::take(&mut scope.macros);
            let used = std::mem::take(&mut scope.used);
            for binding in macros.iter().chain(&used) {
                if (boundary.counters[2]..ends[2]).contains(&binding.definition.id.0) {
                    definitions
                        .entry(binding.definition.id)
                        .or_insert_with(|| binding.definition.clone());
                }
            }
            scope_macros.push((
                id,
                macros.iter().map(StoredMacro::capture).collect(),
                used.iter().map(StoredMacro::capture).collect(),
            ));
            scopes.push((id, scope));
        }
        let mut definitions: Vec<_> = definitions.into_values().collect();
        definitions.sort_by_key(|definition| definition.id.0);
        Ok(PackageExport {
            allocations: Allocations(std::array::from_fn(|i| {
                (boundary.counters[i]..ends[i]).collect()
            })),
            data,
            scopes,
            scope_macros,
            definitions,
            root_children,
            roots: self.roots[boundary.roots..].to_vec(),
        })
    }

    /// Reserve all package identities before relocating any forward references.
    /// Reservation only updates the caller's map; a rejected import leaves this
    /// session unchanged.
    pub fn reserve_import(
        &self,
        package: &PackageExport,
        relocation: &mut Relocation,
    ) -> artifact::Result<()> {
        relocation.insert("resolve.module", 0, 0)?;
        for ((space, values), first) in SPACES
            .into_iter()
            .zip(&package.allocations.0)
            .zip(self.counters())
        {
            let mut next = first;
            for &old in values {
                if relocation.get(space, old).is_some() {
                    continue;
                }
                relocation.insert(space, old, next)?;
                next = next
                    .checked_add(1)
                    .ok_or_else(|| artifact::Error("resolver identity overflow".into()))?;
            }
        }
        Ok(())
    }

    pub fn import_package(
        &mut self,
        mut package: PackageExport,
        relocation: &mut Relocation,
    ) -> artifact::Result<()> {
        package.relocate(relocation)?;
        let counters = self.counters();
        if !package.scopes.is_empty()
            && package
                .scopes
                .iter()
                .all(|(id, _)| (id.0 as u64) < counters[0])
        {
            if package
                .allocations
                .0
                .iter()
                .zip(counters)
                .any(|(values, end)| values.iter().any(|value| *value >= end))
                || package.root_children.iter().any(|(name, id)| {
                    self.resolver
                        .scopes
                        .first()
                        .and_then(|scope| scope.children.get(name))
                        != Some(id)
                })
                || package
                    .data
                    .paths
                    .iter()
                    .any(|(id, path)| self.resolver.paths.get(id) != Some(path))
            {
                return Err(artifact::Error(
                    "overlapping resolver package differs".into(),
                ));
            }
            return Ok(());
        }
        for (values, first) in package.allocations.0.iter().zip(counters) {
            if values
                .iter()
                .enumerate()
                .any(|(offset, value)| *value != first + offset as u64)
            {
                return Err(artifact::Error(
                    "noncontiguous resolver import allocation".into(),
                ));
            }
        }
        if package.scopes.len() != package.allocations.0[0].len()
            || package
                .scopes
                .iter()
                .enumerate()
                .any(|(offset, (id, _))| id.0 as u64 != counters[0] + offset as u64)
            || package.scope_macros.len() != package.scopes.len()
        {
            return Err(artifact::Error("invalid resolver scope table".into()));
        }
        let ends: [u64; 5] =
            std::array::from_fn(|i| counters[i] + package.allocations.0[i].len() as u64);
        if ends[0] > u32::MAX as u64 || ends[1] >= (1 << 63) || ends[3] >= (1 << 31) {
            return Err(artifact::Error(
                "resolver identity capacity exceeded".into(),
            ));
        }
        let mut references = Relocation::collecting();
        package.relocate(&mut references)?;
        for identity in references.identities() {
            if let Identity::Scalar { space, value } = identity
                && let Some(index) = SPACES.iter().position(|candidate| *candidate == space)
                && *value >= ends[index]
            {
                return Err(artifact::Error(format!(
                    "out-of-range imported {space} identity {value}"
                )));
            }
        }
        let own_module = |id: &ModuleId| (counters[0]..ends[0]).contains(&(id.0 as u64));
        let own_binding = |id: &BindingId| (counters[1]..ends[1]).contains(&id.0);
        if package.data.module_inputs.keys().any(|id| !own_module(id)) {
            return Err(artifact::Error("foreign module table entry".into()));
        }
        if package
            .data
            .module_parameters
            .keys()
            .any(|id| !own_module(id))
        {
            return Err(artifact::Error("foreign module table entry".into()));
        }
        if package.data.input.keys().any(|id| !own_module(id)) {
            return Err(artifact::Error("foreign module table entry".into()));
        }
        if package.data.output.keys().any(|id| !own_module(id)) {
            return Err(artifact::Error("foreign module table entry".into()));
        }
        if package.data.origins.keys().any(|id| !own_module(id)) {
            return Err(artifact::Error("foreign module table entry".into()));
        }
        if package.data.paths.keys().any(|id| !own_module(id)) {
            return Err(artifact::Error("foreign module table entry".into()));
        }
        if package.data.states.keys().any(|id| !own_module(id)) {
            return Err(artifact::Error("foreign module table entry".into()));
        }
        if package
            .data
            .module_selections
            .keys()
            .any(|id| !own_module(id))
        {
            return Err(artifact::Error("foreign module table entry".into()));
        }
        if package
            .data
            .declaration_counts
            .keys()
            .any(|id| !own_module(id))
        {
            return Err(artifact::Error("foreign module table entry".into()));
        }
        if package
            .data
            .child_term_scopes
            .keys()
            .any(|id| !own_module(id))
        {
            return Err(artifact::Error("foreign module table entry".into()));
        }
        if package.data.structures.keys().any(|id| !own_binding(id)) {
            return Err(artifact::Error("foreign binding table entry".into()));
        }
        if package
            .data
            .parameter_signatures
            .keys()
            .any(|id| !own_binding(id))
        {
            return Err(artifact::Error("foreign binding table entry".into()));
        }
        if package
            .data
            .front_definitions
            .keys()
            .any(|id| !own_binding(id))
        {
            return Err(artifact::Error("foreign binding table entry".into()));
        }
        if package
            .data
            .structure_values
            .keys()
            .any(|id| !own_binding(id))
        {
            return Err(artifact::Error("foreign binding table entry".into()));
        }
        if package.data.imports.keys().any(|id| !own_binding(id)) {
            return Err(artifact::Error("foreign binding table entry".into()));
        }
        if package
            .data
            .global_bindings
            .keys()
            .any(|id| !own_binding(id))
        {
            return Err(artifact::Error("foreign binding table entry".into()));
        }
        let r = &mut self.resolver;
        if r.scopes.first().is_some_and(|scope| {
            package
                .root_children
                .keys()
                .any(|name| scope.children.contains_key(name))
        }) {
            return Err(artifact::Error("duplicate package root".into()));
        }
        let mut definitions = HashMap::new();
        for scope in &r.scopes {
            for binding in scope.macros.iter().chain(&scope.used) {
                definitions
                    .entry(binding.definition.id)
                    .or_insert_with(|| binding.definition.clone());
            }
        }
        for definition in package.definitions {
            if definitions.insert(definition.id, definition).is_some() {
                return Err(artifact::Error("duplicate macro definition".into()));
            }
        }
        for ((id, scope), (macro_id, macros, used)) in
            package.scopes.iter_mut().zip(package.scope_macros)
        {
            if *id != macro_id {
                return Err(artifact::Error("invalid macro scope identity".into()));
            }
            scope.macros = macros
                .into_iter()
                .map(|value| value.restore(&definitions))
                .collect::<artifact::Result<_>>()?;
            scope.used = used
                .into_iter()
                .map(|value| value.restore(&definitions))
                .collect::<artifact::Result<_>>()?;
        }
        // All fallible relocation and external-reference validation precedes publication.
        if r.scopes.is_empty() {
            r.scopes.push(Scope::default());
        }
        r.scopes[0].children.extend(package.root_children);
        r.scopes
            .extend(package.scopes.into_iter().map(|(_, scope)| scope));
        let data = package.data;
        r.declarations.extend(data.declarations);
        r.references.get_mut().extend(data.references.into_inner());
        r.order.extend(data.order);
        r.module_inputs.extend(data.module_inputs);
        r.module_parameters.extend(data.module_parameters);
        r.input.extend(data.input);
        r.output.extend(data.output);
        r.origins.extend(data.origins);
        r.paths.extend(data.paths);
        r.states.extend(data.states);
        r.module_selections.extend(data.module_selections);
        r.declaration_counts.extend(data.declaration_counts);
        r.child_term_scopes.extend(data.child_term_scopes);
        r.structures.extend(data.structures);
        r.parameter_signatures.extend(data.parameter_signatures);
        r.front_definitions.extend(data.front_definitions);
        r.structure_values.extend(data.structure_values);
        r.imports.extend(data.imports);
        r.global_bindings.extend(data.global_bindings);
        r.computation_bindings.extend(data.computation_bindings);
        r.occurrences.extend(data.occurrences);
        r.next_binding = ends[1];
        r.next_macro = ends[2];
        r.next_expression = ends[3];
        r.next_hygiene.set(ends[4]);
        r.reference_occurrences.get_mut().clear();
        self.roots.extend(package.roots);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn append(session: &mut Session, source: &str) -> PackageExport {
        let boundary = session.boundary();
        let module = syntax::parse::str_parse_modules(source).unwrap().remove(0);
        session.append(&module).unwrap();
        session.export_package(&boundary).unwrap()
    }
    fn import(session: &mut Session, package: PackageExport, r: &mut Relocation) {
        session.reserve_import(&package, r).unwrap();
        session.import_package(package, r).unwrap();
    }
    fn remap_dependencies(source: &Relocation, target: &Relocation) -> Relocation {
        let mut result = Relocation::default();
        for (canonical, source_runtime) in source.mappings() {
            let target_runtime = target.lookup(&canonical).unwrap();
            result
                .insert_identity(source_runtime, target_runtime)
                .unwrap();
        }
        result
    }
    const A: &str = r"\module A {
        \definition T: \Set := \Set;
        \macro identity($value) := (\fun (x: T) => $value);
    }";
    const B: &str = r"\module B {
        \import \root.A[] \as A;
        \use A.identity \as identity;
        \definition b: _ := identity!{A.T};
    }";
    const C: &str = r"\module C {
        \import \root.A[] \as A;
        \definition c: _ := A.T;
    }";
    const NOISE: &str = r"\module Noise {
        \definition unrelated[x: \Set]: \Set := x;
        \macro m($x) := (\fun (z: \Set) => $x);
    }";

    #[test]
    fn independent_packages_import_after_unrelated_allocations() {
        let mut a = Session::default();
        let package_a = append(&mut a, A);
        let mut b = Session::default();
        let package_b = append(&mut b, NOISE);
        let mut combined = Session::default();
        import(&mut combined, package_b, &mut Relocation::default());
        import(&mut combined, package_a, &mut Relocation::default());
        append(&mut combined, B);
        assert_eq!(
            combined
                .project()
                .modules
                .iter()
                .map(|m| m.name.as_str())
                .collect::<Vec<_>>(),
            ["Noise", "A", "B"]
        );
        let b = combined.project().modules.pop().unwrap();
        let ModuleBody::Inline(items) = b.body else {
            panic!()
        };
        assert!(items.iter().any(|item| matches!(
            item,
            ModuleItem::Definition {
                body: SExp::Lam { .. },
                ..
            }
        )));
    }

    #[test]
    fn diamond_shares_dependency_identity_across_different_export_orders() {
        let mut origin = Session::default();
        let origin_a = append(&mut origin, A);
        let mut left = Session::default();
        let mut left_a = Relocation::default();
        import(&mut left, origin_a, &mut left_a);
        let package_b = append(&mut left, B);
        let mut right = Session::default();
        append(&mut right, NOISE);
        let mut right_a = Relocation::default();
        import(
            &mut right,
            origin
                .export_package(&Session::default().boundary())
                .unwrap(),
            &mut right_a,
        );
        let package_c = append(&mut right, C);
        let mut combined = Session::default();
        let mut target_a = Relocation::default();
        import(
            &mut combined,
            origin
                .export_package(&Session::default().boundary())
                .unwrap(),
            &mut target_a,
        );
        import(
            &mut combined,
            package_c,
            &mut remap_dependencies(&right_a, &target_a),
        );
        assert!(
            package_b.definitions.is_empty(),
            "B references A's macro template without storing its body"
        );
        import(
            &mut combined,
            package_b,
            &mut remap_dependencies(&left_a, &target_a),
        );
        append(
            &mut combined,
            r"\module D {
            \import \root.B[] \as B;
            \import \root.C[] \as C;
            \use B.identity \as identity;
            \definition d: _ := identity!{C.c};
        }",
        );
        let roots: Vec<_> = combined.roots.iter().map(|m| m.name.as_str()).collect();
        assert_eq!(roots, ["A", "C", "B", "D"]);
        let a_id = combined.roots[0].id;
        for name in ["B", "C"] {
            let owner = combined
                .roots
                .iter()
                .find(|m| m.name.as_str() == name)
                .unwrap()
                .id;
            assert!(combined.resolver.imports.values().any(|import| {
                import.owner == owner
                    && combined
                        .resolver
                        .origins
                        .get(&import.target)
                        .copied()
                        .unwrap_or(import.target)
                        == a_id
            }));
        }
    }

    #[test]
    fn failed_import_does_not_publish_partial_tables() {
        let mut source = Session::default();
        append(&mut source, A);
        let package_b = append(&mut source, B);
        let mut target = Session::default();
        append(&mut target, NOISE);
        let before = target.counters();
        let mut relocation = Relocation::default();
        target.reserve_import(&package_b, &mut relocation).unwrap();
        assert!(target.import_package(package_b, &mut relocation).is_err());
        assert_eq!(target.counters(), before);
        assert_eq!(target.roots.len(), 1);
    }
}
