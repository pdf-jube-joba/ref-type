//! Per-query diagnostic policy and bounded rendering support.
use std::{
    cell::Cell,
    time::{Duration, Instant},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticMode {
    Compact,
    Detailed,
}
impl Default for DiagnosticMode {
    fn default() -> Self {
        if std::env::var("REF_TYPE_COMPACT_DIAGNOSTICS").as_deref() == Ok("1") {
            Self::Compact
        } else {
            Self::Detailed
        }
    }
}
thread_local! {
    static MODE: Cell<Option<DiagnosticMode>> = const { Cell::new(None) };
    static DIAGNOSTIC_TIME: Cell<Duration> = const { Cell::new(Duration::ZERO) };
}
pub fn with_diagnostic_mode<T>(mode: DiagnosticMode, run: impl FnOnce() -> T) -> T {
    struct Reset(Option<DiagnosticMode>);
    impl Drop for Reset {
        fn drop(&mut self) {
            MODE.set(self.0);
        }
    }
    let _reset = Reset(MODE.replace(Some(mode)));
    run()
}
pub(crate) fn compact() -> bool {
    MODE.get().unwrap_or_default() == DiagnosticMode::Compact
}
pub(crate) const CONSTRAINTS: usize = 32;
pub(crate) const SEARCH: usize = 2048;
pub(crate) const GOALS: usize = 64;
pub(crate) const EXPRESSION_BYTES: usize = 4096;
pub(crate) const MESSAGE_BYTES: usize = 64 * 1024;

/// Preserve UTF-8 boundaries and report the exact number of omitted bytes.
pub(crate) fn bounded(mut text: String, limit: usize) -> String {
    if text.len() > limit {
        let mut end = limit.saturating_sub(64);
        while !text.is_char_boundary(end) {
            end -= 1;
        }
        let omitted = text.len() - end;
        text.truncate(end);
        text.push_str(&format!("… ({omitted} bytes omitted)"));
    }
    text
}

pub(crate) fn format_context(count: usize, entries: impl Iterator<Item = String>) -> String {
    let mut text = entries.take(128).collect::<Vec<_>>().join(", ");
    if count > 128 {
        text.push_str(&format!("; … {} context entries omitted", count - 128));
    }
    bounded(text, 8192)
}

pub fn diagnostic_time() -> Duration {
    DIAGNOSTIC_TIME.get()
}

/// RSS is a process measurement, not a count of allocations owned by this phase.
pub struct DiagnosticProfile {
    label: &'static str,
    start: Instant,
    rss: Option<i64>,
    nested: Duration,
    enabled: bool,
}
impl DiagnosticProfile {
    pub fn start(label: &'static str) -> Self {
        let enabled = std::env::var_os("REF_TYPE_PROFILE_DIAGNOSTICS").is_some();
        Self {
            label,
            start: Instant::now(),
            rss: enabled.then(rss_kib).flatten(),
            nested: diagnostic_time(),
            enabled,
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
impl Drop for DiagnosticProfile {
    fn drop(&mut self) {
        let elapsed = self.start.elapsed();
        let nested = diagnostic_time().saturating_sub(self.nested);
        DIAGNOSTIC_TIME.set(diagnostic_time() + elapsed.saturating_sub(nested));
        if self.enabled {
            let rss = rss_kib();
            eprintln!(
                "diagnostics phase={} elapsed_us={} rss_kib={rss:?} rss_delta_kib={:?}",
                self.label,
                elapsed.as_micros(),
                rss.zip(self.rss).map(|(after, before)| after - before)
            );
        }
    }
}
