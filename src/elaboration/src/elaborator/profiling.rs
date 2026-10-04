use std::time::Instant;

pub(crate) struct ProfileTimer {
    label: String,
    started: Instant,
    checkpoint: Instant,
    diagnostics: std::time::Duration,
}

impl ProfileTimer {
    pub(crate) fn start(variable: &str, label: impl FnOnce() -> String) -> Option<Self> {
        let filter = std::env::var(variable).ok()?;
        let label = label();
        if filter != "1" && !label.contains(&filter) {
            return None;
        }
        let started = Instant::now();
        Some(Self {
            label,
            started,
            checkpoint: started,
            diagnostics: crate::diagnostics::diagnostic_time(),
        })
    }

    pub(crate) fn checkpoint(&mut self, phase: &str) {
        let now = Instant::now();
        eprintln!(
            "{:>10.3?}    {}",
            now.duration_since(self.checkpoint),
            phase
        );
        self.checkpoint = now;
    }
}

impl Drop for ProfileTimer {
    fn drop(&mut self) {
        eprintln!(
            "{:>10.3?}  {} (excluding diagnostics)",
            self.started.elapsed().saturating_sub(
                crate::diagnostics::diagnostic_time().saturating_sub(self.diagnostics)
            ),
            self.label
        );
    }
}
