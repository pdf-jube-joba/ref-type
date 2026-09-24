//! Cooperative cancellation and deterministic resource limits for checking.
use std::{
    cell::RefCell,
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

#[derive(Debug, Clone, Default)]
pub struct CancellationToken(Arc<AtomicBool>);

impl CancellationToken {
    pub fn cancel(&self) {
        self.0.store(true, Ordering::Relaxed);
    }
    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Interrupted {
    Cancelled,
    ResourceLimit,
}

struct Control {
    cancellation: CancellationToken,
    remaining: Option<u64>,
}
thread_local! { static CURRENT: RefCell<Option<Control>> = const { RefCell::new(None) }; }

struct Scope(Option<Control>);
impl Drop for Scope {
    fn drop(&mut self) {
        CURRENT.with(|current| *current.borrow_mut() = self.0.take());
    }
}

/// Unwinding discards the caller's uncommitted working environment. Expected
/// interruptions bypass the panic hook; unexpected panics retain their payload.
pub fn run<T>(
    cancellation: CancellationToken,
    steps: Option<u64>,
    operation: impl FnOnce() -> T,
) -> Result<T, Interrupted> {
    let previous = CURRENT.with(|current| {
        current.replace(Some(Control {
            cancellation,
            remaining: steps,
        }))
    });
    let _scope = Scope(previous);
    match catch_unwind(AssertUnwindSafe(|| {
        checkpoint();
        operation()
    })) {
        Ok(result) => Ok(result),
        Err(payload) => match payload.downcast::<Interrupted>() {
            Ok(interrupted) => Err(*interrupted),
            Err(payload) => resume_unwind(payload),
        },
    }
}

pub fn checkpoint() {
    let interrupted = CURRENT.with(|current| {
        let mut current = current.borrow_mut();
        let control = current.as_mut()?;
        if control.cancellation.is_cancelled() {
            return Some(Interrupted::Cancelled);
        }
        if let Some(remaining) = &mut control.remaining {
            if *remaining == 0 {
                return Some(Interrupted::ResourceLimit);
            }
            *remaining -= 1;
        }
        None
    });
    if let Some(interrupted) = interrupted {
        resume_unwind(Box::new(interrupted));
    }
}
