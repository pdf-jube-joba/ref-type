//! Optional wall-time and resident-memory measurements for checking phases.
use std::{borrow::Cow, time::Instant};

pub struct Phase {
    label: Cow<'static, str>,
    started: Option<Instant>,
    rss: Option<i64>,
}
impl Phase {
    pub fn start(label: impl Into<Cow<'static, str>>) -> Self {
        let enabled = std::env::var_os("REF_TYPE_PROFILE_PHASES").is_some();
        Self {
            label: label.into(),
            started: enabled.then(Instant::now),
            rss: enabled.then(rss_kib).flatten(),
        }
    }
}
fn rss_kib() -> Option<i64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    status
        .lines()
        .find(|line| line.starts_with("VmRSS:"))?
        .split_whitespace()
        .nth(1)?
        .parse()
        .ok()
}
impl Drop for Phase {
    fn drop(&mut self) {
        if let Some(started) = self.started {
            let rss = rss_kib();
            eprintln!(
                "phase={} elapsed_us={} rss_kib={rss:?} rss_delta_kib={:?}",
                self.label,
                started.elapsed().as_micros(),
                rss.zip(self.rss).map(|(after, before)| after - before)
            );
        }
    }
}
