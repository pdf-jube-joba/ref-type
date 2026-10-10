use sema::{ProgressAction, ProgressEvent, ProgressPhase, ProgressPlan};
use std::{
    cell::RefCell,
    collections::BTreeMap,
    io::{self, Write},
    sync::{Arc, Mutex, mpsc},
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};

thread_local! {
    static ACTIVE: RefCell<Option<Active>> = const { RefCell::new(None) };
}

enum Update {
    Refresh,
    Stop,
}

struct Active {
    state: Arc<Mutex<State>>,
    wake: mpsc::SyncSender<Update>,
}

struct State {
    phase: ProgressPhase,
    plan: Option<ProgressPlan>,
    completed: BTreeMap<Vec<String>, ProgressAction>,
    current: Option<Vec<String>>,
    started: Instant,
    success: Option<bool>,
}

impl State {
    fn new() -> Self {
        Self {
            phase: ProgressPhase::Loading,
            plan: None,
            completed: BTreeMap::new(),
            current: None,
            started: Instant::now(),
            success: None,
        }
    }

    fn update(&mut self, event: &ProgressEvent) {
        match event {
            ProgressEvent::Phase(phase) => {
                self.phase = *phase;
                self.current = None;
            }
            ProgressEvent::Planned(plan) => self.plan = Some(plan.clone()),
            ProgressEvent::ModuleStarted(path) => self.current = Some(path.clone()),
            ProgressEvent::ModuleFinished { path, action } => {
                self.completed.insert(path.clone(), *action);
            }
            ProgressEvent::Finished { success } => self.success = Some(*success),
        }
    }

    fn render(&self, tick: usize, width: usize) -> String {
        let phase = match self.success {
            Some(false) => "Failed",
            Some(true) => "Finishing",
            None => match self.phase {
                ProgressPhase::Loading => "Loading",
                ProgressPhase::Planning => "Planning",
                ProgressPhase::Cache => "Cache",
                ProgressPhase::Resolving => "Resolving",
                ProgressPhase::Restoring => "Restoring",
                ProgressPhase::Checking => "Checking",
                ProgressPhase::Saving => "Saving",
            },
        };
        let spinner = ['|', '/', '-', '\\'][tick % 4];
        let elapsed = self.started.elapsed().as_secs_f64();
        let Some(plan) = &self.plan else {
            return truncate(&format!("{spinner} {phase} ({elapsed:.1}s)"), width);
        };
        let total = plan.modules.len();
        let complete = self.completed.len();
        let filled = complete.saturating_mul(16).checked_div(total).unwrap_or(0);
        let bar = format!("{}{}", "=".repeat(filled), " ".repeat(16 - filled));
        let target = self.current.as_ref().map_or_else(
            || match plan.packages.len() {
                0 => String::new(),
                count => format!("{count} packages"),
            },
            |path| {
                let package = &path[0];
                if plan.packages.contains(package) {
                    let total = plan
                        .modules
                        .iter()
                        .filter(|m| m.path[0] == *package)
                        .count();
                    let done = self.completed.keys().filter(|p| p[0] == *package).count();
                    format!("({package} {done}/{total}) {}", path.join("."))
                } else {
                    path.join(".")
                }
            },
        );
        // Keep elapsed time visible even when the module path is long.
        let prefix = format!("{spinner} {phase} [{bar}] {complete}/{total} ({elapsed:.1}s)");
        truncate(&format!("{prefix} {target}"), width)
    }
}

fn truncate(line: &str, width: usize) -> String {
    if line.chars().count() <= width {
        line.to_owned()
    } else {
        line.chars()
            .take(width.saturating_sub(1))
            .chain(['…'])
            .collect()
    }
}

pub fn receive(event: &ProgressEvent) {
    ACTIVE.with_borrow(|active| {
        if let Some(active) = active {
            active.state.lock().unwrap().update(event);
            let _ = active.wake.try_send(Update::Refresh);
        }
    });
}

/// Own the transient stderr line and stop its worker before diagnostics are printed.
pub struct Display {
    enabled: bool,
    state: Arc<Mutex<State>>,
    wake: mpsc::SyncSender<Update>,
    worker: Option<JoinHandle<()>>,
}

impl Display {
    pub fn new(enabled: bool) -> Self {
        let state = Arc::new(Mutex::new(State::new()));
        let (wake, updates) = mpsc::sync_channel(1);
        let worker = enabled.then(|| {
            ACTIVE.with_borrow_mut(|active| {
                *active = Some(Active {
                    state: state.clone(),
                    wake: wake.clone(),
                });
            });
            let state = state.clone();
            let width = std::env::var("COLUMNS")
                .ok()
                .and_then(|value| value.parse::<usize>().ok())
                .unwrap_or(80)
                .clamp(20, 240)
                .saturating_sub(1);
            thread::spawn(move || {
                let mut tick = 0;
                loop {
                    let line = state.lock().unwrap().render(tick, width);
                    let mut stderr = io::stderr().lock();
                    let _ = write!(stderr, "\r\x1b[2K{line}");
                    let _ = stderr.flush();
                    drop(stderr);
                    tick += 1;
                    match updates.recv_timeout(Duration::from_millis(100)) {
                        Ok(Update::Stop) | Err(mpsc::RecvTimeoutError::Disconnected) => break,
                        Ok(Update::Refresh) | Err(mpsc::RecvTimeoutError::Timeout) => {}
                    }
                }
            })
        });
        Self {
            enabled,
            state,
            wake,
            worker,
        }
    }

    pub fn enabled(&self) -> bool {
        self.enabled
    }

    fn stop(&mut self) -> bool {
        let Some(worker) = self.worker.take() else {
            return false;
        };
        ACTIVE.with_borrow_mut(|active| *active = None);
        let _ = self.wake.send(Update::Stop);
        let _ = worker.join();
        let _ = write!(io::stderr().lock(), "\r\x1b[2K");
        true
    }

    pub fn finish(&mut self, success: bool) {
        if !self.stop() {
            return;
        }
        let state = self.state.lock().unwrap();
        let status = if success { "Finished" } else { "Failed" };
        let skipped = state
            .completed
            .values()
            .filter(|&&a| a == ProgressAction::Skip)
            .count();
        let count = state.plan.as_ref().map_or(String::new(), |plan| {
            format!(
                " {}/{} modules, {skipped} cached",
                state.completed.len(),
                plan.modules.len()
            )
        });
        eprintln!(
            "{status}{count} ({:.3}s)",
            state.started.elapsed().as_secs_f64()
        );
    }
}

impl Drop for Display {
    fn drop(&mut self) {
        self.stop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retries_change_cached_action_without_counting_a_module_twice() {
        let mut state = State::new();
        let path = vec!["lib".into(), "Module".into()];
        state.update(&ProgressEvent::Planned(ProgressPlan {
            packages: vec!["lib".into()],
            modules: vec![sema::ProgressModule {
                path: path.clone(),
                dependencies: vec![],
            }],
        }));
        state.update(&ProgressEvent::ModuleStarted(path.clone()));
        state.update(&ProgressEvent::ModuleFinished {
            path: path.clone(),
            action: ProgressAction::Skip,
        });
        state.update(&ProgressEvent::ModuleFinished {
            path,
            action: ProgressAction::Check,
        });
        assert_eq!(state.completed.len(), 1);
        assert!(state.render(0, 200).contains("(lib 1/1) lib.Module"));
        assert_eq!(
            state.completed.values().next(),
            Some(&ProgressAction::Check)
        );
        let line = state.render(0, 40);
        assert_eq!(line.chars().count(), 40);
        assert!(line.ends_with('…'));
    }
}
