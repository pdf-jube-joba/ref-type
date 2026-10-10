//! Package boundaries preserve both resolver and checker identities across callers.
use super::*;
use elaboration::{PackageChecker, PackageProgress};

pub(crate) const MAX_RECORD_BYTES: usize = elaboration::MAX_PACKAGE_BYTES + 64 * 1024 * 1024;

fn encode(
    checker: &PackageChecker,
    results: &BTreeMap<usize, ModuleResult>,
) -> Option<(Vec<u8>, bool)> {
    let _cost = timing::costs::Scope::enter("query.package-serialize");
    let environment = checker
        .checkpoint()
        .map_err(|error| {
            if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
                eprintln!("package checkpoint skipped: {error}");
            }
        })
        .ok();
    let has_environment = environment.is_some();
    let environment = environment.unwrap_or_default();
    let metadata = serde_json::to_vec(&results.values().collect::<Vec<_>>()).ok()?;
    if 8 + metadata.len() + environment.len() > MAX_RECORD_BYTES {
        return None;
    }
    let mut bytes = (metadata.len() as u64).to_le_bytes().to_vec();
    bytes.extend(metadata);
    bytes.extend(environment);
    Some((bytes, has_environment))
}

fn decode(bytes: &[u8]) -> Option<(&[u8], Vec<ModuleResult>)> {
    let _cost = timing::costs::Scope::enter("query.package-restore");
    if bytes.len() > MAX_RECORD_BYTES {
        return None;
    }
    let length = usize::try_from(u64::from_le_bytes(bytes.get(..8)?.try_into().ok()?)).ok()?;
    let end = 8_usize.checked_add(length)?;
    let results: Vec<ModuleResult> = serde_json::from_slice(bytes.get(8..end)?).ok()?;
    if results
        .iter()
        .any(|result| result.status != ModuleStatus::Verified)
    {
        return None;
    }
    Some((bytes.get(end..)?, results))
}

impl Database {
    pub(super) fn check_packages(
        &mut self,
        snapshot: &SourceSnapshot,
        options: &CheckOptions,
        graph: &ModuleGraph<'_>,
        requested: &BTreeSet<usize>,
        packages: &[PathBuf],
        module_keys: &[Fingerprint],
        progress: &mut crate::progress::Reporter,
    ) -> Option<Arc<SemanticResult>> {
        let _cost = timing::costs::Scope::enter("query.packages");
        let modules = graph.selected(requested);
        let mut prefix = fingerprint(
            format!(
                "package-v1:{}:{}",
                env!("REF_SEMA_REVISION"),
                options.configuration
            )
            .as_bytes(),
        );
        let mut boundaries = Vec::new();
        for module in &modules {
            let root = graph
                .roots
                .iter()
                .position(|root| root.name == module.name)?;
            let mut bytes = prefix.to_vec();
            bytes.extend(crate::cache::source_key(snapshot, &packages[root]));
            // Partial queries never masquerade as a fully checked package.
            let indices: BTreeSet<_> = requested
                .iter()
                .copied()
                .filter(|&index| graph.units[index].path[0] == module.name.0)
                .collect();
            for &index in &indices {
                bytes.extend(serde_json::to_vec(&graph.units[index].path).ok()?);
            }
            prefix = fingerprint(&bytes);
            boundaries.push((prefix, indices));
        }
        let mut checker = PackageChecker::default();
        let mut results = BTreeMap::new();
        let mut start = 0;
        let first_forced = if options.force {
            0
        } else if options.force_local {
            modules
                .iter()
                .position(|module| module.name == graph.roots.last().expect("entry package").name)
                .unwrap_or(modules.len())
        } else {
            modules.len()
        };
        progress.phase(ProgressPhase::Restoring);
        for index in (0..first_forced).rev() {
            let key = &boundaries[index].0;
            let mut disk_hit = false;
            let bytes = self.package_environments.get(key).or_else(|| {
                let bytes: Arc<[u8]> = self.disk.as_ref()?.read_package(key)?.into();
                disk_hit = true;
                self.package_environments.insert(*key, bytes.clone());
                Some(bytes)
            });
            let Some((environment, saved)) = bytes.as_deref().and_then(decode) else {
                continue;
            };
            let expected: BTreeSet<_> = boundaries[..=index]
                .iter()
                .flat_map(|(_, indices)| indices.iter().copied())
                .collect();
            let mapped: Option<BTreeMap<_, _>> = saved
                .into_iter()
                .map(|result| Some((*graph.indices.get(&result.path)?, result)))
                .collect();
            let Some(saved) =
                mapped.filter(|saved| saved.keys().copied().collect::<BTreeSet<_>>() == expected)
            else {
                continue;
            };
            if index + 1 < modules.len() {
                let restored =
                    PackageChecker::restore(environment, |id| snapshot.source(&id.0).cloned());
                let Some(restored) = restored else {
                    continue;
                };
                checker = restored;
                self.stats.environment_hits += 1;
                self.stats.restored_modules += saved.len();
            }
            results = saved;
            for (&index, result) in &mut results {
                result.dependencies = graph.units[index]
                    .dependencies
                    .iter()
                    .map(|&dependency| graph.units[dependency].path.clone())
                    .collect();
            }
            start = index + 1;
            self.stats.package_hits += start;
            if disk_hit {
                self.stats.disk_hits += results.len();
            }
            self.stats.reused_modules += results.len();
            for &index in results.keys() {
                progress.reused(index, std::time::Duration::ZERO);
            }
            progress.skip_cached();
            break;
        }
        // Retain finer module invalidation for edits inside a standalone package.
        if modules.len() == 1
            && start == 0
            && !options.force
            && requested.iter().any(|&index| {
                self.checked.contains_key(&module_keys[index])
                    || self
                        .disk
                        .as_ref()
                        .is_some_and(|disk| disk.read(&module_keys[index]).is_some())
            })
        {
            return None;
        }
        for (index, module) in modules.iter().enumerate().skip(start) {
            progress.phase(ProgressPhase::Resolving);
            let checked = checker.append(module, |event| match event {
                PackageProgress::Prepared { paths, start } => {
                    let steps: Vec<_> = paths
                        .iter()
                        .map(|path| {
                            (1..=path.len())
                                .rev()
                                .find_map(|length| graph.indices.get(&path[..length]))
                                .copied()
                                .expect("package source scope")
                        })
                        .collect();
                    progress.begin_batch(
                        &steps,
                        start,
                        steps.len(),
                        &(start..steps.len()).collect(),
                    );
                    progress.phase(ProgressPhase::Checking);
                }
                PackageProgress::Step(elaboration::CheckStepProgress::Started(position)) => {
                    progress.start_step(position)
                }
                PackageProgress::Step(elaboration::CheckStepProgress::Finished {
                    position,
                    elapsed,
                    success,
                }) => progress.step(position, elapsed, success),
            });
            progress.finish_batch();
            // The ordinary path retains detailed independent-scope error recovery.
            // Successfully checked dependency artifacts remain valid on failure.
            if checked.is_err() {
                return None;
            }
            let (key, indices) = &boundaries[index];
            self.stats.checked_modules += indices.len();
            progress.verified(indices);
            let mut fresh: BTreeMap<_, _> = indices
                .iter()
                .map(|&index| {
                    (
                        index,
                        ModuleResult {
                            path: graph.units[index].path.clone(),
                            status: ModuleStatus::Verified,
                            dependencies: graph.units[index]
                                .dependencies
                                .iter()
                                .map(|&dependency| graph.units[dependency].path.clone())
                                .collect(),
                            ..ModuleResult::default()
                        },
                    )
                })
                .collect();
            collect_analysis(checker.analysis(), graph, &mut fresh);
            for (&index, result) in &fresh {
                self.checked
                    .insert(module_keys[index], Arc::new(result.clone()));
                if let Some(disk) = &self.disk {
                    match disk.write(&module_keys[index], result) {
                        Ok(()) => self.stats.disk_writes += 1,
                        Err(_) => self.stats.cache_write_failures += 1,
                    }
                }
            }
            results.extend(fresh);
            progress.phase(ProgressPhase::Saving);
            if !(options.force && self.disk.is_none()) {
                if let Some((bytes, has_environment)) = encode(&checker, &results) {
                    if !has_environment {
                        self.stats.package_skips += 1;
                    }
                    if std::env::var_os("REF_TYPE_PROFILE_ENVIRONMENTS").is_some() {
                        eprintln!(
                            "package checkpoint {}: {} bytes",
                            module.name.0,
                            bytes.len()
                        );
                    }
                    if let Some(disk) = &self.disk {
                        match disk.write_package(key, &bytes) {
                            Ok(()) => self.stats.package_writes += 1,
                            Err(_) => self.stats.cache_write_failures += 1,
                        }
                    }
                    self.package_environments.insert(*key, bytes.into());
                } else {
                    self.stats.package_skips += 1;
                }
            }
        }
        self.stats.environment_bytes =
            self.environments.bytes() + self.package_environments.bytes();
        Some(Arc::new(SemanticResult {
            modules: results.into_values().collect(),
            diagnostics: Vec::new(),
        }))
    }
}
