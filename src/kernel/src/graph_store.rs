//! Immutable graph pages supplied by the session's content-addressed store.
use std::{cell::RefCell, io, rc::Rc};

pub trait GraphStore: std::fmt::Debug {
    fn identity(&self) -> String;
    fn write(&self, bytes: &[u8]) -> io::Result<Vec<u8>>;
    fn read(&self, reference: &[u8]) -> io::Result<Vec<u8>>;
    fn retain(&self, reference: &[u8]) -> io::Result<()>;
}

thread_local! {
    static CURRENT: RefCell<Option<Rc<dyn GraphStore>>> = const { RefCell::new(None) };
}
pub fn current() -> Option<Rc<dyn GraphStore>> {
    CURRENT.with_borrow(Clone::clone)
}

/// The caller publishes all retained page references with the checkpoint's
/// manifest. The guard restores nested contexts even when serialization fails.
pub fn with_graph_store<T>(store: Rc<dyn GraphStore>, f: impl FnOnce() -> T) -> T {
    struct Guard(Option<Rc<dyn GraphStore>>);
    impl Drop for Guard {
        fn drop(&mut self) {
            CURRENT.with_borrow_mut(|slot| *slot = self.0.take());
        }
    }
    let _guard = Guard(CURRENT.with_borrow_mut(|slot| slot.replace(store)));
    f()
}
