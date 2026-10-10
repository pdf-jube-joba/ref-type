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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgressPhase {
    Loading,
    Planning,
    Cache,
    Resolving,
    Restoring,
    Checking,
    Saving,
}

/// Source modules in the selected dependency closure, before elaboration.
#[derive(Clone, Debug)]
pub struct ProgressModule {
    pub path: Vec<String>,
    pub dependencies: Vec<Vec<String>>,
}

#[derive(Clone, Debug)]
pub struct ProgressPlan {
    /// Empty for standalone files, which may contain several root modules.
    pub packages: Vec<String>,
    pub modules: Vec<ProgressModule>,
}

#[derive(Clone, Debug)]
pub enum ProgressEvent {
    Phase(ProgressPhase),
    Planned(ProgressPlan),
    ModuleStarted(Vec<String>),
    /// Checking is complete; analysis and cache storage may still follow.
    ModuleFinished {
        path: Vec<String>,
        action: ProgressAction,
    },
    Finished {
        success: bool,
    },
}

struct State {
    path: Vec<String>,
    cached: bool,
    checked: bool,
    report_timing: bool,
    completed: Option<ProgressAction>,
}

/// Report after all module work, including analysis and cache writes, has finished.
/// Synthetic modules are charged to their enclosing source module by timing scopes.
pub(crate) struct Reporter {
    callback: Option<fn(&ModuleProgress)>,
    events: Option<fn(&ProgressEvent)>,
    modules: BTreeMap<usize, State>,
    steps: BTreeMap<usize, usize>,
    last: BTreeMap<usize, usize>,
    order: Vec<usize>,
    queued: BTreeSet<usize>,
    succeeded: bool,
    active: Option<usize>,
}

impl Reporter {
    pub fn new(
        graph: &ModuleGraph<'_>,
        requested: &BTreeSet<usize>,
        package: bool,
        callback: Option<fn(&ModuleProgress)>,
        events: Option<fn(&ProgressEvent)>,
    ) -> Self {
        if let Some(receive) = events {
            receive(&ProgressEvent::Planned(ProgressPlan {
                packages: if package {
                    requested
                        .iter()
                        .map(|&index| graph.units[index].path[0].clone())
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect()
                } else {
                    Vec::new()
                },
                modules: requested
                    .iter()
                    .map(|&index| ProgressModule {
                        path: graph.units[index].path.clone(),
                        dependencies: graph.units[index]
                            .dependencies
                            .iter()
                            .map(|&dependency| graph.units[dependency].path.clone())
                            .collect(),
                    })
                    .collect(),
            }));
        }
        let modules = requested
            .iter()
            .filter(|&&index| {
                events.is_some()
                    || (callback.is_some() && (!package || graph.units[index].path.len() > 1))
            })
            .map(|&index| {
                (
                    index,
                    State {
                        path: graph.units[index].path.clone(),
                        cached: false,
                        checked: false,
                        report_timing: callback.is_some()
                            && (!package || graph.units[index].path.len() > 1),
                        completed: None,
                    },
                )
            })
            .collect();
        Self {
            callback,
            events,
            modules,
            steps: BTreeMap::new(),
            last: BTreeMap::new(),
            order: Vec::new(),
            queued: BTreeSet::new(),
            succeeded: false,
            active: None,
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
        for (&index, state) in &mut self.modules {
            if state.cached && !self.last.contains_key(&index) && self.queued.insert(index) {
                self.order.push(index);
                Self::complete(self.events, state, ProgressAction::Skip);
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
        if self.callback.is_none() && self.events.is_none() {
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

    pub fn phase(&mut self, phase: ProgressPhase) {
        self.active = None;
        if let Some(receive) = self.events {
            receive(&ProgressEvent::Phase(phase));
        }
    }

    pub fn start_step(&mut self, position: usize) {
        let Some(&index) = self.steps.get(&position) else {
            return;
        };
        if self.active != Some(index) {
            self.active = Some(index);
            if let Some(receive) = self.events {
                receive(&ProgressEvent::ModuleStarted(
                    self.modules[&index].path.clone(),
                ));
            }
        }
    }

    pub fn step(&mut self, position: usize, _: Duration, success: bool) {
        let Some(&index) = self.steps.get(&position) else {
            return;
        };
        let Some(state) = self.modules.get_mut(&index) else {
            return;
        };
        state.checked = true;
        if self.last.get(&index) == Some(&position) {
            if self.queued.insert(index) {
                self.order.push(index);
            }
            if success {
                Self::complete(self.events, state, ProgressAction::Check);
            }
        }
    }

    pub fn finish_batch(&mut self) {
        for (&index, state) in &self.modules {
            if state.checked && self.queued.insert(index) {
                self.order.push(index);
            }
        }
        self.last.clear();
    }

    pub fn verified(&mut self, selected: &BTreeSet<usize>) {
        for &index in selected {
            if let Some(state) = self.modules.get_mut(&index) {
                let action = if state.cached && !state.checked {
                    ProgressAction::Skip
                } else {
                    ProgressAction::Check
                };
                Self::complete(self.events, state, action);
            }
        }
    }

    fn complete(events: Option<fn(&ProgressEvent)>, state: &mut State, action: ProgressAction) {
        if state.completed != Some(action) {
            state.completed = Some(action);
            if let Some(receive) = events {
                receive(&ProgressEvent::ModuleFinished {
                    path: state.path.clone(),
                    action,
                });
            }
        }
    }

    pub fn finish(&mut self, success: bool) {
        self.succeeded = success;
    }
}

impl Drop for Reporter {
    fn drop(&mut self) {
        self.skip_cached();
        if let Some(receive) = self.events {
            receive(&ProgressEvent::Finished {
                success: self.succeeded,
            });
        }
        let Some(callback) = self.callback else {
            return;
        };
        for (&index, state) in &self.modules {
            if timing::elapsed(&state.path) > Duration::ZERO && self.queued.insert(index) {
                self.order.push(index);
            }
        }
        for &index in &self.order {
            let state = &self.modules[&index];
            if !state.report_timing {
                continue;
            }
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
