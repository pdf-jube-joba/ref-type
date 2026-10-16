//! Source identities and structural expression labels survive coverage changes.
use super::*;
use sha2::{Digest, Sha256};

pub(super) fn identity<T: Relocate + Clone>(value: &T) -> Identity {
    let mut r = Relocation::collecting();
    value.clone().relocate(&mut r).expect("collect identity");
    r.identities()
        .next()
        .expect("identity-bearing value")
        .clone()
}
fn hash<T: serde::Serialize>(value: &T) -> artifact::Result<Label> {
    Ok(Label::Digest(
        Sha256::digest(
            artifact::canonical::to_vec_detailed(value, MAX_PACKAGE_BYTES)
                .map_err(|error| Error(format!("artifact identity hash serialization: {error}")))?,
        )
        .into(),
    ))
}

/// Encode just this value's references with small local numbers and include
/// their semantic labels in the hash. Ambient table sizes cannot affect it.
fn structural<T: serde::Serialize + Relocate + Clone>(
    value: &T,
    labels: &BTreeMap<Identity, Label>,
) -> artifact::Result<Label> {
    let mut value = value.clone();
    let mut inventory = Relocation::collecting();
    value.relocate(&mut inventory)?;
    let mut ids: Vec<_> = inventory
        .into_identities()
        .into_iter()
        .map(|id| {
            let label = labels
                .get(&id)
                .cloned()
                .ok_or_else(|| Error(format!("semantic label missing for {id:?}")))?;
            Ok((id, label))
        })
        .collect::<artifact::Result<_>>()?;
    ids.sort_by(|(a, al), (b, bl)| a.space().cmp(b.space()).then_with(|| al.cmp(bl)));
    let mut r = Relocation::default();
    let mut names = Vec::new();
    for (index, (id, label)) in ids.into_iter().enumerate() {
        let normalized = match &id {
            Identity::Scalar { space, .. } => Identity::scalar(space, index as u64),
            Identity::Pair { space, .. } => Identity::pair(space, (0, index as u32)),
        };
        names.push((id.space().to_string(), label));
        r.insert_identity(id, normalized)?;
    }
    value.relocate(&mut r)?;
    drop(r);
    hash(&(value, names))
}

pub(super) fn labels(
    workspace: &mut crate::elaborator::exports::Export,
    environment: &GlobalEnvironment,
    resolver: &resolve::PackageExport,
    identities: &BTreeSet<Identity>,
    catalog: &ArtifactCatalog,
    dependencies: &BTreeSet<ArtifactOwner>,
    input: ArtifactOwner,
    artifact: ArtifactOwner,
) -> artifact::Result<BTreeMap<Identity, Reference>> {
    let mut references: BTreeMap<_, _> = identities
        .iter()
        .filter_map(|id| {
            catalog
                .reference(id, dependencies)
                .filter(|reference| reference.owner != input)
                .map(|reference| (id.clone(), *reference))
        })
        .collect();
    let mut labels = BTreeMap::new();
    for (id, reference) in &references {
        labels.insert(id.clone(), hash(reference)?);
    }
    for id in identities.iter().filter(|id| builtin(id)) {
        labels.insert(id.clone(), hash(id)?);
    }
    macro_rules! put {
        ($id:expr, $local:expr, $labels:expr) => {{
            let id = $id;
            let reference = Reference {
                owner: input,
                local: $local,
            };
            $labels.insert(id.clone(), hash(&reference)?);
            references.insert(id, reference);
            Ok::<(), Error>(())
        }};
    }
    let mut ordinal: BTreeMap<String, u64> = BTreeMap::new();
    for id in resolver.owned_ids() {
        let next = ordinal.entry(id.space().into()).or_default();
        let space = [
            "resolve.module",
            "resolve.binding",
            "resolve.macro",
            "resolve.expression",
            "resolve.hygiene",
        ]
        .iter()
        .position(|space| *space == id.space())
        .expect("resolver identity space") as u8;
        put!(
            id.clone(),
            Label::Resolver {
                space,
                ordinal: *next
            },
            &mut labels
        )?;
        *next += 1;
    }
    let mut sources: Vec<_> = workspace.modules.iter().collect();
    sources.sort_by_key(|(hir, _)| hir.0);
    for (hir, raw) in sources {
        put!(
            identity(raw),
            structural(&("source-module".to_string(), *hir), &labels)?,
            &mut labels
        )?;
    }
    let mut generated: BTreeMap<Label, u64> = BTreeMap::new();
    for (id, module) in &workspace.raw.modules {
        if labels.contains_key(&identity(id)) {
            continue;
        }
        let owner = workspace
            .raw
            .checking_scopes
            .get(id)
            .copied()
            .or(module.parent())
            .ok_or_else(|| Error("generated namespace has no owning scope".into()))?;
        let owner_label = *labels
            .get(&identity(&owner))
            .ok_or_else(|| Error("generated namespace owner missing".into()))?;
        let ordinal = generated.entry(owner_label).or_default();
        put!(
            identity(id),
            hash(&("generated-module", owner_label, *ordinal))?,
            &mut labels
        )?;
        *ordinal += 1;
    }
    for id in identities {
        if references.contains_key(id) || builtin(id) {
            continue;
        }
        if let Identity::Scalar { space, value } = id
            && matches!(space.as_str(), "inductive" | "datatype" | "parameter")
        {
            let module = labels
                .get(&Identity::scalar("raw.module", value >> 32))
                .ok_or_else(|| Error("nominal owning module missing".into()))?;
            put!(
                id.clone(),
                hash(&(space, module, value & 0xffff_ffff))?,
                &mut labels
            )?;
        }
    }
    // Index symbol metadata once: looking through both tables for each symbol
    // made package publication quadratic in the number of binders.
    let mut symbol_bindings = rustc_hash::FxHashMap::default();
    for (&binding, &symbol) in &workspace.raw.hir_symbols {
        symbol_bindings.entry(symbol).or_insert(binding);
    }
    let mut exported_symbols: rustc_hash::FxHashSet<_> = workspace
        .raw
        .symbols
        .iter()
        .map(|(symbol, _, _)| *symbol)
        .collect();
    for id in identities {
        if references.contains_key(id) || builtin(id) {
            continue;
        }
        if let Identity::Scalar { space, value } = id
            && space == "symbol"
        {
            let symbol = kernel::ids::SymbolId(*value as u32);
            let (name, interned) = environment.crate_env.exported_symbol(symbol);
            let binding = symbol_bindings.get(&symbol).copied();
            let label = match binding {
                Some(binding) => match references.get(&identity(&binding)) {
                    Some(Reference {
                        owner,
                        local: Label::Resolver { space, ordinal },
                    }) if *owner == input => Label::BindingSymbol {
                        space: *space,
                        ordinal: *ordinal,
                        index: if binding.0 & (1 << 63) != 0 {
                            binding.0 as u32
                        } else {
                            0
                        },
                    },
                    _ => structural(&("binding-symbol".to_string(), binding), &labels)?,
                },
                None => structural(&name, &labels)?,
            };
            put!(id.clone(), label, &mut labels)?;
            if exported_symbols.insert(symbol) {
                workspace.raw.symbols.push((symbol, name, interned));
            }
        }
    }
    for (raw, kernel) in &workspace.raw.kernel_definitions {
        let id = identity(kernel);
        if !references.contains_key(&id) {
            put!(
                id,
                structural(&("definition".to_string(), *raw), &labels)?,
                &mut labels
            )?;
        }
    }
    for (source, reflected) in &workspace.raw.kernel.reflected {
        let id = identity(reflected);
        if !references.contains_key(&id) && labels.contains_key(&identity(source)) {
            put!(
                id,
                structural(&("reflected-definition".to_string(), *source), &labels)?,
                &mut labels
            )?;
        }
    }
    for (meta, atom) in &workspace.raw.arena.atoms {
        let id = identity(meta);
        if !references.contains_key(&id) {
            put!(id, structural(atom, &labels)?, &mut labels)?;
        }
    }
    // A remapping names an immutable creation site or composition. Its current
    // attachment set and incrementally populated contents are not its identity.
    let mut visiting = BTreeSet::new();
    for root in workspace.raw.remapping_origins.keys() {
        let mut pending = vec![(*root, false)];
        while let Some((id, expanded)) = pending.pop() {
            let runtime = identity(&id);
            if labels.contains_key(&runtime) {
                continue;
            }
            let origin = workspace
                .raw
                .remapping_origins
                .get(&id)
                .ok_or_else(|| Error("remapping creation origin missing".into()))?;
            if expanded {
                put!(
                    runtime,
                    structural(&("remapping-origin".to_string(), origin.clone()), &labels)?,
                    &mut labels
                )?;
                visiting.remove(&id.0);
                continue;
            }
            if !visiting.insert(id.0) {
                return Err(Error("cyclic remapping origin".into()));
            }
            pending.push((id, true));
            if let crate::raw::environment::RemappingOrigin::Composition { next, previous } = origin
            {
                for parent in [previous, next] {
                    if !labels.contains_key(&identity(parent)) {
                        pending.push((*parent, false));
                    }
                }
            }
        }
    }
    for (remapping, snapshot) in workspace
        .raw
        .remappings
        .ids
        .iter()
        .zip(&workspace.raw.remappings.snapshots)
    {
        put!(
            identity(snapshot),
            structural(
                &("remapping-snapshot".to_string(), artifact, *remapping),
                &labels
            )?,
            &mut labels
        )?;
    }
    // Non-nominal implementation tables may be separate for distinct coverage
    // artifacts. Their references still have explicit ownership and relocation.
    let mut ordinal: BTreeMap<String, u64> = BTreeMap::new();
    let own_input = BTreeSet::from([input]);
    for id in identities {
        if references.contains_key(id) || builtin(id) || id.space() == "expression" {
            continue;
        }
        if let Some(reference) = catalog.reference(id, &own_input) {
            labels.insert(id.clone(), hash(reference)?);
            references.insert(id.clone(), *reference);
            continue;
        }
        let next = ordinal.entry(id.space().into()).or_default();
        put!(
            id.clone(),
            hash(&(artifact, id.space(), *next))?,
            &mut labels
        )?;
        *next += 1;
    }
    for (expression, node) in &workspace.graph.nodes {
        let id = identity_of_expression(*expression);
        if !references.contains_key(&id) {
            put!(id, structural(node, &labels)?, &mut labels)?;
        }
    }
    Ok(references)
}

/// Restore only labels omitted from the resolver header. References to external
/// expressions stay explicit, so dependency ownership and overlap checks remain
/// identical to the export path.
pub(super) fn restore_expression_references(
    graph: &kernel::exports::ExpressionGraph,
    input: ArtifactOwner,
    references: &mut Vec<(Identity, Reference)>,
) -> artifact::Result<()> {
    let mut labels = BTreeMap::new();
    for (id, reference) in references.iter() {
        if labels.insert(id.clone(), hash(reference)?).is_some() {
            return Err(Error("duplicate portable identity".into()));
        }
    }
    for (space, value) in [
        ("resolve.module", 0),
        ("raw.module", 0),
        ("raw.remapping", 0),
        ("raw.remapping.snapshot", 0),
        ("symbol", 0),
        ("symbol", 1),
    ] {
        let id = Identity::scalar(space, value);
        labels.insert(id.clone(), hash(&id)?);
    }
    for (expression, node) in &graph.nodes {
        let id = identity_of_expression(*expression);
        let reference = Reference {
            owner: input,
            local: structural(node, &labels)?,
        };
        if labels.insert(id.clone(), hash(&reference)?).is_some() {
            return Err(Error("duplicate owned expression identity".into()));
        }
        references.push((id, reference));
    }
    Ok(())
}
