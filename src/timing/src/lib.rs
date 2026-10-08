//! Exclusive wall-time accounting for source modules on the current thread.
use std::{
    cell::RefCell,
    collections::BTreeMap,
    time::{Duration, Instant},
};

#[derive(Default, Debug)]
pub struct Measurements {
    pub total: Duration,
    pub modules: BTreeMap<Vec<String>, Duration>,
}

struct Ledger {
    start: Instant,
    since: Instant,
    owner: Option<Vec<String>>,
    modules: BTreeMap<Vec<String>, Duration>,
}

impl Ledger {
    fn switch(&mut self, now: Instant, owner: Option<Vec<String>>) -> Option<Vec<String>> {
        if let Some(path) = &self.owner {
            *self.modules.entry(path.clone()).or_default() += now.duration_since(self.since);
        }
        self.since = now;
        std::mem::replace(&mut self.owner, owner)
    }

    fn measurements(&mut self, now: Instant) -> Measurements {
        let owner = self.owner.clone();
        self.switch(now, owner);
        Measurements {
            total: now.duration_since(self.start),
            modules: self.modules.clone(),
        }
    }
}

thread_local! {
    static LEDGER: RefCell<Option<Ledger>> = const { RefCell::new(None) };
}

/// Nested clients reuse the caller's session. Only its owner finishes it.
pub struct Session {
    owned: bool,
}

impl Session {
    pub fn start(enabled: bool) -> Self {
        let owned = enabled
            && LEDGER.with_borrow_mut(|ledger| {
                if ledger.is_some() {
                    return false;
                }
                let now = Instant::now();
                *ledger = Some(Ledger {
                    start: now,
                    since: now,
                    owner: None,
                    modules: BTreeMap::new(),
                });
                true
            });
        Self { owned }
    }

    pub fn finish(mut self) -> Option<Measurements> {
        if !self.owned {
            return None;
        }
        self.owned = false;
        LEDGER.with_borrow_mut(|ledger| {
            ledger
                .take()
                .map(|mut ledger| ledger.measurements(Instant::now()))
        })
    }

    pub fn measurements(&self) -> Option<Measurements> {
        LEDGER.with_borrow_mut(|ledger| {
            ledger
                .as_mut()
                .map(|ledger| ledger.measurements(Instant::now()))
        })
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        if self.owned {
            LEDGER.with_borrow_mut(|ledger| *ledger = None);
        }
    }
}

pub fn elapsed(path: &[String]) -> Duration {
    LEDGER.with_borrow_mut(|ledger| {
        let Some(ledger) = ledger else {
            return Duration::ZERO;
        };
        let owner = ledger.owner.clone();
        ledger.switch(Instant::now(), owner);
        ledger.modules.get(path).copied().unwrap_or_default()
    })
}

/// Child scopes suspend their parent's clock; generated scopes use the source owner.
pub struct Scope {
    previous: Option<Option<Vec<String>>>,
}

impl Scope {
    pub fn module(path: impl FnOnce() -> Vec<String>) -> Self {
        Self::enter(|| {
            let mut path = path();
            if let Some(index) = path.iter().position(|component| component.starts_with('<')) {
                path.truncate(index);
            }
            (!path.is_empty()).then_some(path)
        })
    }

    pub fn shared() -> Self {
        Self::enter(|| None)
    }

    fn enter(owner: impl FnOnce() -> Option<Vec<String>>) -> Self {
        let previous = LEDGER.with_borrow_mut(|ledger| {
            ledger.as_mut().map(|ledger| {
                let owner = owner();
                ledger.switch(Instant::now(), owner)
            })
        });
        Self { previous }
    }
}

impl Drop for Scope {
    fn drop(&mut self) {
        if let Some(previous) = self.previous.take() {
            LEDGER.with_borrow_mut(|ledger| {
                if let Some(ledger) = ledger {
                    ledger.switch(Instant::now(), previous);
                }
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_modules_are_exclusive_and_return_to_shared_time() {
        let start = Instant::now();
        let a = vec!["A".into()];
        let b = vec!["B".into()];
        let mut ledger = Ledger {
            start,
            since: start,
            owner: None,
            modules: BTreeMap::new(),
        };
        let at = |ms| start + Duration::from_millis(ms);
        let shared = ledger.switch(at(2), Some(a.clone()));
        let parent = ledger.switch(at(5), Some(b.clone()));
        ledger.switch(at(12), parent);
        ledger.switch(at(16), shared);
        let measurements = ledger.measurements(at(20));
        assert_eq!(measurements.modules[&a], Duration::from_millis(7));
        assert_eq!(measurements.modules[&b], Duration::from_millis(7));
        assert_eq!(
            measurements.total - measurements.modules.values().sum::<Duration>(),
            Duration::from_millis(6)
        );
    }

    #[test]
    fn nested_sessions_and_generated_modules_share_the_source_clock() {
        let session = Session::start(true);
        {
            let _source = Scope::module(|| vec!["A".into()]);
            let nested = Session::start(true);
            {
                let _generated = Scope::module(|| vec!["A".into(), "<definition:f>".into()]);
            }
            assert!(nested.finish().is_none());
        }
        let measurements = session.finish().unwrap();
        assert_eq!(measurements.modules.len(), 1);
        assert!(measurements.modules.values().sum::<Duration>() <= measurements.total);
        assert!(Session::start(true).finish().is_some());
    }
}
