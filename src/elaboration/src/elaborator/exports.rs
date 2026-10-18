//! Explicit package deltas; dependency environments are supplied by the importer.
use super::*;
use artifact::{Identity, Relocate, Relocation, Result};
use kernel::exports::ExpressionGraph;

pub(crate) struct Boundary {
    raw: crate::raw::environment::exports::Boundary,
    aliases: std::collections::HashSet<resolve::hir::BindingId>,
    references: usize,
    resolved_declarations: usize,
}

#[derive(serde::Serialize, serde::Deserialize, Relocate)]
pub(crate) struct Export {
    pub raw: crate::raw::environment::exports::Export,
    pub graph: ExpressionGraph,
    pub modules: HashMap<resolve::hir::ModuleId, crate::raw::ids::ModuleId>,
    bindings: HashMap<resolve::hir::BindingId, crate::raw::ids::ModuleId>,
    aliases: HashMap<resolve::hir::BindingId, crate::raw::ids::ModuleId>,
    references: Vec<crate::analysis::Reference>,
    declarations: Vec<crate::analysis::Declaration>,
    outputs: Vec<crate::analysis::Output>,
    resolved_declarations: usize,
}

impl Export {
    pub(crate) fn canonicalize(
        &mut self,
        source_modules: &[crate::raw::ids::ModuleId],
    ) -> Result<()> {
        self.raw.canonicalize(source_modules)?;
        // Postcard varints are not numerically ordered. Keep module declaration
        // order and numeric source offsets, with semantic keys for tied locations.
        let modules: HashMap<_, _> = self
            .raw
            .modules
            .iter()
            .map(|(id, module)| (*id, module))
            .collect();
        let module_order: rustc_hash::FxHashMap<_, _> = source_modules
            .iter()
            .enumerate()
            .map(|(index, id)| {
                let mut path = Vec::new();
                let mut current = Some(*id);
                while let Some(module) = current.and_then(|id| modules.get(&id)) {
                    path.push(module.name().to_owned());
                    current = module.parent();
                }
                path.reverse();
                (path, index)
            })
            .collect();
        source_order(&mut self.outputs, &module_order, |v| {
            (&v.module, &v.location)
        });
        source_order(&mut self.references, &module_order, |v| {
            (&v.module, &v.location)
        });
        deduplicate_references(&mut self.references);
        if self.resolved_declarations > self.declarations.len() {
            return Err(artifact::Error(
                "invalid exported declaration boundary".into(),
            ));
        }
        let mut checked = self.declarations.split_off(self.resolved_declarations);
        source_order(&mut self.declarations, &module_order, |v| {
            (&v.module, &v.location)
        });
        source_order(&mut checked, &module_order, |v| (&v.module, &v.location));
        self.declarations.extend(checked);
        Ok(())
    }
}

trait AnalysisOrder {
    fn semantic_order(&self, other: &Self) -> std::cmp::Ordering;
}
impl AnalysisOrder for crate::analysis::Declaration {
    fn semantic_order(&self, other: &Self) -> std::cmp::Ordering {
        (&self.name, self.kind, &self.ty).cmp(&(&other.name, other.kind, &other.ty))
    }
}
impl AnalysisOrder for crate::analysis::Reference {
    fn semantic_order(&self, other: &Self) -> std::cmp::Ordering {
        (&self.target_module, &self.target_name).cmp(&(&other.target_module, &other.target_name))
    }
}
impl AnalysisOrder for crate::analysis::Output {
    fn semantic_order(&self, _other: &Self) -> std::cmp::Ordering {
        // Expansion can emit several outputs at one source location. Stable
        // sorting preserves their evaluation order within that occurrence.
        std::cmp::Ordering::Equal
    }
}

fn deduplicate_references(references: &mut Vec<crate::analysis::Reference>) {
    references.dedup_by(|left, right| {
        left.module == right.module
            && left.location.source.id == right.location.source.id
            && left.location.span == right.location.span
            && left.target_module == right.target_module
            && left.target_name == right.target_name
    });
}

fn source_order<T: AnalysisOrder>(
    values: &mut [T],
    modules: &rustc_hash::FxHashMap<Vec<String>, usize>,
    location: impl for<'a> Fn(&'a T) -> (&'a Vec<String>, &'a syntax::syntax::SourceLocation),
) {
    values.sort_by(|left, right| {
        let (lm, ll) = location(left);
        let (rm, rl) = location(right);
        (
            modules.get(lm).copied().unwrap_or(usize::MAX),
            lm,
            &ll.source.id.0,
            ll.span.start,
            ll.span.end,
        )
            .cmp(&(
                modules.get(rm).copied().unwrap_or(usize::MAX),
                rm,
                &rl.source.id.0,
                rl.span.start,
                rl.span.end,
            ))
            .then_with(|| left.semantic_order(right))
    });
}

impl GlobalEnvironment {
    pub(crate) fn order_analysis(&mut self) {
        let mut modules: Vec<_> = self.module_manager.hir_modules.iter().collect();
        modules.sort_by_key(|(hir, _)| hir.0);
        let order = modules
            .into_iter()
            .enumerate()
            .map(|(index, (_, raw))| {
                (
                    crate::elaborator::analysis::module_path(&self.crate_env, *raw),
                    index,
                )
            })
            .collect();
        let (resolved, checked) = self
            .analysis
            .declarations
            .split_at_mut(self.resolved_declarations);
        source_order(resolved, &order, |v| (&v.module, &v.location));
        source_order(checked, &order, |v| (&v.module, &v.location));
        source_order(&mut self.analysis.references, &order, |v| {
            (&v.module, &v.location)
        });
        deduplicate_references(&mut self.analysis.references);
        source_order(&mut self.analysis.outputs, &order, |v| {
            (&v.module, &v.location)
        });
    }

    pub(crate) fn restore_artifact_analysis(&mut self, project: &resolve::Project) {
        self.analysis.references = project.references.clone();
        self.collect_references();
    }

    pub(crate) fn artifact_boundary(&self) -> Boundary {
        Boundary {
            raw: self.crate_env.boundary(),
            aliases: self.module_manager.hir_aliases.keys().copied().collect(),
            references: self.module_manager.references.borrow().len(),
            resolved_declarations: self.resolved_declarations,
        }
    }

    pub(crate) fn export_artifact(
        &self,
        base: &Boundary,
        mut external: impl FnMut(kernel::syntax::Expression) -> bool,
        pending: bool,
        external_snapshot: impl Fn(crate::raw::environment::RemappingSnapshotId) -> bool,
    ) -> Result<Export> {
        let modules: HashMap<_, _> = self
            .module_manager
            .hir_modules
            .iter()
            .filter(|(_, id)| id.index() >= base.raw.modules)
            .map(|(k, v)| (*k, *v))
            .collect();
        let roots: Vec<_> = modules
            .values()
            .copied()
            .chain(
                self.module_manager
                    .hir_module_bindings
                    .values()
                    .copied()
                    .filter(|id| id.index() >= base.raw.modules),
            )
            .chain(
                self.module_manager
                    .hir_aliases
                    .iter()
                    .filter(|(binding, _)| !base.aliases.contains(binding))
                    .map(|(_, id)| *id),
            )
            .collect();
        let raw = self.crate_env.export_since_with_snapshots(
            &base.raw,
            external_snapshot,
            (!pending).then_some(roots.as_slice()),
            &mut external,
        )?;
        let package_names: std::collections::HashSet<_> = modules
            .values()
            .filter(|id| self.crate_env.module(**id).parent() == Some(crate::raw::ids::ModuleId(0)))
            .map(|id| self.crate_env.module(*id).name().to_owned())
            .collect();
        let own = |path: &Vec<String>| {
            path.first()
                .is_some_and(|name| package_names.contains(name))
        };
        let declarations = self
            .analysis
            .declarations
            .iter()
            .filter(|v| own(&v.module))
            .cloned()
            .collect();
        let mut export = Export {
            raw,
            graph: ExpressionGraph { nodes: Vec::new() },
            modules,
            bindings: self
                .module_manager
                .hir_module_bindings
                .iter()
                .filter(|(_, id)| id.index() >= base.raw.modules)
                .map(|(k, v)| (*k, *v))
                .collect(),
            aliases: self
                .module_manager
                .hir_aliases
                .iter()
                .filter(|(k, _)| !base.aliases.contains(k))
                .map(|(k, v)| (*k, *v))
                .collect(),
            references: self
                .module_manager
                .references
                .borrow()
                .iter()
                .skip(base.references)
                .cloned()
                .collect(),
            declarations,
            outputs: self
                .analysis
                .outputs
                .iter()
                .filter(|v| own(&v.module))
                .cloned()
                .collect(),
            resolved_declarations: self.resolved_declarations - base.resolved_declarations,
        };
        let mut roots = Relocation::collecting();
        export.relocate(&mut roots)?;
        let expressions = roots
            .into_identities()
            .into_iter()
            .filter_map(|id| match id {
                Identity::Scalar { space, value } if space == "expression" => {
                    Some(kernel::syntax::Expression::from_index(value as u32))
                }
                _ => None,
            });
        export.graph = self
            .crate_env
            .arena()
            .core
            .export_graph(expressions, external)?;
        let mut graph_ids = Relocation::collecting();
        export.graph.relocate(&mut graph_ids)?;
        export
            .raw
            .arena
            .retain_reachable_atoms(&graph_ids.into_identities())?;
        Ok(export)
    }

    pub(crate) fn reserve_artifact(&self, export: &mut Export, r: &mut Relocation) -> Result<()> {
        self.crate_env.reserve_export(&export.raw, r)?;
        export.raw.nominal_mappings(r)?;
        // Nominal IDs in expressions need the same module-based translation as metadata.
        let mut ids = Relocation::collecting();
        export.relocate(&mut ids)?;
        for id in ids.identities() {
            if let Identity::Scalar { space, value } = id
                && matches!(space.as_str(), "inductive" | "datatype" | "parameter")
                && r.get(space, *value).is_none()
            {
                let module = r.id("raw.module", value >> 32)?;
                r.insert(space, *value, (module << 32) | (value & 0xffff_ffff))?;
            }
        }
        kernel::exports::reserve_metas(r, ids.identities().cloned())?;
        export
            .raw
            .kernel
            .reserve_nominals(&self.crate_env.kernel.borrow(), r)?;
        Ok(())
    }

    pub(crate) fn import_artifact(&mut self, mut export: Export, r: &mut Relocation) -> Result<()> {
        let graph = std::mem::replace(&mut export.graph, ExpressionGraph { nodes: Vec::new() });
        let mut atoms: Vec<_> = graph
            .nodes
            .iter()
            .filter_map(|(_, node)| match node {
                kernel::syntax::Node::Meta { id, .. } => Some(*id),
                _ => None,
            })
            .collect();
        atoms.relocate(r)?;
        self.crate_env.arena().core.import_graph(graph, r)?;
        export.relocate(r)?;
        self.crate_env.import_export(export.raw)?;
        self.crate_env.arena().validate_atoms(&atoms)?;
        self.module_manager.hir_modules.extend(export.modules);
        self.module_manager
            .hir_module_bindings
            .extend(export.bindings);
        self.module_manager.hir_aliases.extend(export.aliases);
        extend_unique(self.module_manager.references.get_mut(), export.references)?;
        if export.resolved_declarations > export.declarations.len() {
            return Err(artifact::Error(
                "invalid exported declaration boundary".into(),
            ));
        }
        let existing_checked = self
            .analysis
            .declarations
            .split_off(self.resolved_declarations);
        let mut declarations = export.declarations;
        let checked = declarations.split_off(export.resolved_declarations);
        extend_unique(&mut self.analysis.declarations, declarations)?;
        self.resolved_declarations = self.analysis.declarations.len();
        self.analysis.declarations.extend(existing_checked);
        extend_unique(&mut self.analysis.declarations, checked)?;
        extend_unique(&mut self.analysis.outputs, export.outputs)?;
        Ok(())
    }
}

fn extend_unique<T: serde::Serialize>(target: &mut Vec<T>, incoming: Vec<T>) -> Result<()> {
    let encode = |value: &T| {
        artifact::canonical::to_vec(value, crate::MAX_PACKAGE_BYTES)
            .map_err(|error| artifact::Error(error.to_string()))
    };
    let mut seen = target
        .iter()
        .map(&encode)
        .collect::<Result<std::collections::BTreeSet<_>>>()?;
    for value in incoming {
        if seen.insert(encode(&value)?) {
            target.push(value);
        }
    }
    Ok(())
}
