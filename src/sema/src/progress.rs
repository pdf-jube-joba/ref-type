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
    pub elapsed: Duration,
}

struct State {
    path: Vec<String>,
    elapsed: Duration,
    cached: bool,
    checked: bool,
    reported: bool,
}

/// Track source modules; synthetic modules share their enclosing source unit.
pub(crate) struct Reporter {
    callback: Option<fn(&ModuleProgress)>,
    modules: BTreeMap<usize, State>,
    steps: BTreeMap<usize, usize>,
    last: BTreeMap<usize, usize>,
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
                let unit = &graph.units[index];
                (
                    index,
                    State {
                        path: unit.path.clone(),
                        elapsed: Duration::ZERO,
                        cached: false,
                        checked: false,
                        reported: false,
                    },
                )
            })
            .collect();
        Self {
            callback,
            modules,
            steps: BTreeMap::new(),
            last: BTreeMap::new(),
        }
    }

    pub fn reused(&mut self, index: usize, elapsed: Duration) {
        if let Some(state) = self.modules.get_mut(&index) {
            state.cached = true;
            state.elapsed += elapsed;
        }
    }

    pub fn skip_all(&mut self) {
        for state in self.modules.values_mut() {
            state.cached = true;
        }
        self.skip_cached();
    }

    pub fn skip_cached(&mut self) {
        for (&index, state) in &mut self.modules {
            if state.cached && !self.last.contains_key(&index) {
                Self::report(self.callback, state, ProgressAction::Skip);
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

    pub fn step(&mut self, position: usize, elapsed: Duration) {
        let Some(index) = self.steps.get(&position) else {
            return;
        };
        let Some(state) = self.modules.get_mut(index) else {
            return;
        };
        if !state.checked {
            state.elapsed = Duration::ZERO;
            state.checked = true;
        }
        state.elapsed += elapsed;
        if self.last.get(index) == Some(&position) {
            Self::report(self.callback, state, ProgressAction::Check);
        }
    }

    pub fn finish_batch(&mut self) {
        for state in self.modules.values_mut().filter(|state| state.checked) {
            Self::report(self.callback, state, ProgressAction::Check);
        }
        self.last.clear();
    }

    fn report(callback: Option<fn(&ModuleProgress)>, state: &mut State, action: ProgressAction) {
        if state.reported {
            return;
        }
        state.reported = true;
        if let Some(callback) = callback {
            callback(&ModuleProgress {
                path: state.path.clone(),
                action,
                elapsed: state.elapsed,
            });
        }
    }
}
