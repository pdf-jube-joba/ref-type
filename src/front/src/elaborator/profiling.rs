use std::time::Instant;

pub(super) struct ProfileTimer {
    label: String,
    started: Instant,
    checkpoint: Instant,
}

impl ProfileTimer {
    pub(super) fn start(variable: &str, label: impl FnOnce() -> String) -> Option<Self> {
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
        })
    }

    pub(super) fn checkpoint(&mut self, phase: &str) {
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
        eprintln!("{:>10.3?}  {}", self.started.elapsed(), self.label);
    }
}
