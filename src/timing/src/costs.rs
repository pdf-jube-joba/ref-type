//! Opt-in, nested wall-time accounting independent of module progress clocks.
use std::{
    cell::RefCell,
    collections::BTreeMap,
    time::{Duration, Instant},
};

#[derive(Default, Debug)]
pub struct Measurement {
    pub calls: u64,
    pub inclusive: Duration,
    pub exclusive: Duration,
    pub max: Duration,
}

struct Frame {
    label: &'static str,
    started: Instant,
    children: Duration,
}

#[derive(Default)]
struct Ledger {
    stack: Vec<Frame>,
    measurements: BTreeMap<&'static str, Measurement>,
    counters: BTreeMap<&'static str, u64>,
    filters: Vec<String>,
}

impl Ledger {
    fn accepts(&self, label: &str) -> bool {
        self.filters.is_empty() || self.filters.iter().any(|prefix| label.starts_with(prefix))
    }

    fn exit(&mut self, now: Instant) {
        let frame = self.stack.pop().expect("cost scopes exit in nesting order");
        let inclusive = now.duration_since(frame.started);
        let measurement = self.measurements.entry(frame.label).or_default();
        measurement.calls += 1;
        measurement.inclusive += inclusive;
        measurement.exclusive += inclusive.saturating_sub(frame.children);
        measurement.max = measurement.max.max(inclusive);
        if let Some(parent) = self.stack.last_mut() {
            parent.children += inclusive;
        }
    }
}

thread_local! {
    static LEDGER: RefCell<Option<Ledger>> = const { RefCell::new(None) };
}

/// Set REF_TYPE_PROFILE_COSTS=1 to print aggregate logs when the owner exits.
/// A comma-separated list of label prefixes measures only those scopes.
/// Nested sessions reuse the existing ledger, including on error returns.
pub struct Session {
    started: Option<Instant>,
}

impl Session {
    pub fn start() -> Self {
        let filter = std::env::var("REF_TYPE_PROFILE_COSTS").ok();
        let owned = filter.is_some()
            && LEDGER.with_borrow_mut(|ledger| {
                if ledger.is_some() {
                    return false;
                }
                let filter = filter.unwrap();
                *ledger = Some(Ledger {
                    filters: if filter == "1" {
                        Vec::new()
                    } else {
                        filter
                            .split(',')
                            .map(str::trim)
                            .map(str::to_owned)
                            .collect()
                    },
                    ..Ledger::default()
                });
                true
            });
        Self {
            started: owned.then(Instant::now),
        }
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        let Some(started) = self.started else { return };
        let elapsed = started.elapsed();
        let ledger = LEDGER
            .with_borrow_mut(Option::take)
            .expect("cost session owns ledger");
        debug_assert!(ledger.stack.is_empty());
        let mut accounted = Duration::ZERO;
        let mut groups: BTreeMap<&str, Duration> = BTreeMap::new();
        for (label, measurement) in ledger.measurements {
            accounted += measurement.exclusive;
            *groups.entry(label.split('.').next().unwrap()).or_default() += measurement.exclusive;
            eprintln!(
                "cost={label} calls={} inclusive_us={} exclusive_us={} max_us={}",
                measurement.calls,
                measurement.inclusive.as_micros(),
                measurement.exclusive.as_micros(),
                measurement.max.as_micros()
            );
        }
        for (group, duration) in groups {
            eprintln!("cost_group={group} exclusive_us={}", duration.as_micros());
        }
        for (label, value) in ledger.counters {
            eprintln!("cost_count={label} value={value}");
        }
        eprintln!(
            "cost_total elapsed_us={} accounted_us={} unaccounted_us={}",
            elapsed.as_micros(),
            accounted.as_micros(),
            elapsed.saturating_sub(accounted).as_micros()
        );
    }
}

/// The closure is evaluated only during a profiling session.
pub fn count(label: &'static str, value: impl FnOnce() -> u64) {
    LEDGER.with_borrow_mut(|ledger| {
        if let Some(ledger) = ledger {
            *ledger.counters.entry(label).or_default() += value();
        }
    });
}

/// Inclusive time includes child scopes; exclusive time subtracts them once.
/// Recursive calls with the same label therefore have additive exclusive time.
pub struct Scope {
    active: bool,
}

impl Scope {
    #[inline]
    pub fn enter(label: &'static str) -> Self {
        let active = LEDGER.with_borrow_mut(|ledger| {
            let Some(ledger) = ledger else { return false };
            if !ledger.accepts(label) {
                return false;
            }
            ledger.stack.push(Frame {
                label,
                started: Instant::now(),
                children: Duration::ZERO,
            });
            true
        });
        Self { active }
    }
}

impl Drop for Scope {
    #[inline]
    fn drop(&mut self) {
        if self.active {
            let now = Instant::now();
            LEDGER.with_borrow_mut(|ledger| {
                if let Some(ledger) = ledger {
                    ledger.exit(now);
                }
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recursive_and_cross_group_calls_have_additive_exclusive_time() {
        let start = Instant::now();
        let at = |ms| start + Duration::from_millis(ms);
        let mut ledger = Ledger::default();
        ledger.stack.push(Frame {
            label: "resolve.import",
            started: at(0),
            children: Duration::ZERO,
        });
        ledger.stack.push(Frame {
            label: "resolve.import",
            started: at(2),
            children: Duration::ZERO,
        });
        ledger.stack.push(Frame {
            label: "kernel.check",
            started: at(3),
            children: Duration::ZERO,
        });
        ledger.exit(at(6));
        ledger.exit(at(8));
        ledger.exit(at(10));
        let imports = &ledger.measurements["resolve.import"];
        assert_eq!(imports.calls, 2);
        assert_eq!(imports.inclusive, Duration::from_millis(16));
        assert_eq!(imports.exclusive, Duration::from_millis(7));
        assert_eq!(imports.max, Duration::from_millis(10));
        assert_eq!(
            ledger.measurements["kernel.check"].exclusive,
            Duration::from_millis(3)
        );
        assert_eq!(
            ledger
                .measurements
                .values()
                .map(|m| m.exclusive)
                .sum::<Duration>(),
            Duration::from_millis(10)
        );
    }

    #[test]
    fn scopes_are_inert_without_a_session() {
        let _scope = Scope::enter("kernel.check");
        LEDGER.with_borrow(|ledger| assert!(ledger.is_none()));
    }

    #[test]
    fn filters_select_boundaries_and_counters_are_lazy_when_disabled() {
        let ledger = Ledger {
            filters: vec!["resolve.total".into(), "kernel.".into()],
            ..Ledger::default()
        };
        assert!(ledger.accepts("resolve.total"));
        assert!(ledger.accepts("kernel.check"));
        assert!(!ledger.accepts("resolve.access"));
        assert!(!ledger.accepts("names.get-item"));
        count("unused", || panic!("disabled counter evaluated"));
    }
}
