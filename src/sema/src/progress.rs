use crate::graph::ModuleGraph;
use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgressAction {
    Check,
    Skip,
}

#[derive(Clone, Debug)]
pub struct ModuleProgress {
    pub path: Vec<String>,
    pub action: ProgressAction,
    /// Exclusive time across loading, resolution, checking and result storage.
    pub elapsed: Duration,
}

struct State {
    path: Vec<String>,
    cached: bool,
    checked: bool,
}

/// Report after all module work, including analysis and cache writes, has finished.
/// Synthetic modules are charged to their enclosing source module by timing scopes.
pub(crate) struct Reporter {
    callback: Option<fn(&ModuleProgress)>,
    modules: BTreeMap<usize, State>,
    steps: BTreeMap<usize, usize>,
    last: BTreeMap<usize, usize>,
    order: Vec<usize>,
}

impl Reporter {
    pub fn new(
        graph: &ModuleGraph<'_>,
        requested: &BTreeSet<usize>,
        package: bool,
        callback: Option<fn(&ModuleProgress)>,
    ) -> Self {
        let modules = requested
            .iter()
            .filter(|&&index| callback.is_some() && (!package || graph.units[index].path.len() > 1))
            .map(|&index| {
                (
                    index,
                    State {
                        path: graph.units[index].path.clone(),
                        cached: false,
                        checked: false,
                    },
                )
            })
            .collect();
        Self {
            callback,
            modules,
            steps: BTreeMap::new(),
            last: BTreeMap::new(),
            order: Vec::new(),
        }
    }

    pub fn reused(&mut self, index: usize, _: Duration) {
        if let Some(state) = self.modules.get_mut(&index) {
            state.cached = true;
        }
    }

    pub fn skip_all(&mut self) {
        for state in self.modules.values_mut() {
            state.cached = true;
        }
        self.skip_cached();
    }

    pub fn skip_cached(&mut self) {
        for (&index, state) in &self.modules {
            if state.cached && !self.last.contains_key(&index) && !self.order.contains(&index) {
                self.order.push(index);
            }
        }
    }

    pub fn begin_batch(
        &mut self,
        steps: &[usize],
        start: usize,
        end: usize,
        selected: &BTreeSet<usize>,
    ) {
        if self.callback.is_none() {
            return;
        }
        self.steps.clear();
        self.last.clear();
        for &index in &steps[..start] {
            self.reused(index, Duration::ZERO);
        }
        for &position in selected.range(start..end) {
            let index = steps[position];
            self.steps.insert(position, index);
            self.last.insert(index, position);
        }
        self.skip_cached();
    }

    pub fn step(&mut self, position: usize, _: Duration) {
        let Some(&index) = self.steps.get(&position) else {
            return;
        };
        let Some(state) = self.modules.get_mut(&index) else {
            return;
        };
        state.checked = true;
        if self.last.get(&index) == Some(&position) && !self.order.contains(&index) {
            self.order.push(index);
        }
    }

    pub fn finish_batch(&mut self) {
        for (&index, state) in &self.modules {
            if state.checked && !self.order.contains(&index) {
                self.order.push(index);
            }
        }
        self.last.clear();
    }
}

impl Drop for Reporter {
    fn drop(&mut self) {
        self.skip_cached();
        let Some(callback) = self.callback else {
            return;
        };
        for (&index, state) in &self.modules {
            if !self.order.contains(&index) && timing::elapsed(&state.path) > Duration::ZERO {
                self.order.push(index);
            }
        }
        for &index in &self.order {
            let state = &self.modules[&index];
            callback(&ModuleProgress {
                path: state.path.clone(),
                action: if state.cached && !state.checked {
                    ProgressAction::Skip
                } else {
                    ProgressAction::Check
                },
                elapsed: timing::elapsed(&state.path),
            });
        }
    }
}
