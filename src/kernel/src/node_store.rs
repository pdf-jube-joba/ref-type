//! Stable expression handles over bounded resident pages. Reads pin an Rc<Node>;
//! the graph's edges are indices, so pages can be reloaded without relocation.
use crate::syntax::{Expression, Node};
use rustc_hash::FxHashMap;
use std::{
    io,
    rc::{Rc, Weak},
};

const PAGE_NODES: usize = 2048;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct StoreStats {
    pub allocated_slots: usize,
    pub live_nodes: usize,
    pub hash_collisions: usize,
    pub pinned_nodes: usize,
    pub index_capacity_bytes: usize,
    pub resident_bytes: usize,
    pub peak_resident_bytes: usize,
    pub stored_bytes: u64,
    pub loaded_bytes: u64,
    pub evicted_bytes: u64,
    pub loads: u64,
    pub evictions: u64,
}

#[derive(Debug, Default)]
struct Page {
    nodes: Option<Vec<Option<Node>>>,
    external: Option<(Rc<dyn crate::graph_store::GraphStore>, Vec<u8>)>,
    bytes: usize,
    recent: bool,
}

#[derive(Debug)]
pub(crate) struct NodeStore {
    pages: Vec<Page>,
    live: Vec<bool>,
    pins: FxHashMap<Expression, Weak<Node>>,
    hot: crate::sharing::Cache<usize, Rc<Node>, { 1 << 15 }>,
    store: Option<Rc<dyn crate::graph_store::GraphStore>>,
    budget: usize,
    clock: usize,
    stats: StoreStats,
}

impl Default for NodeStore {
    fn default() -> Self {
        Self {
            pages: Vec::new(),
            live: Vec::new(),
            pins: FxHashMap::default(),
            hot: Default::default(),
            store: crate::graph_store::current(),
            budget: if cfg!(target_arch = "wasm32") {
                usize::MAX
            } else {
                std::env::var("REF_TYPE_GRAPH_RESIDENT_MIB")
                    .ok()
                    .and_then(|value| value.parse::<usize>().ok())
                    .and_then(|value| value.checked_mul(1024 * 1024))
                    .filter(|value| *value >= 1024 * 1024)
                    .unwrap_or(128 * 1024 * 1024)
            },
            clock: 0,
            stats: StoreStats::default(),
        }
    }
}

fn payload_bytes(node: &Node) -> usize {
    let mut bytes = 0;
    let _: Result<(), std::convert::Infallible> = node.try_for_each_child(|_, _| {
        bytes += 4 * std::mem::size_of::<usize>();
        Ok(())
    });
    bytes
}

impl NodeStore {
    pub fn len(&self) -> usize {
        self.live.len()
    }
    pub fn is_live(&self, index: usize) -> bool {
        self.live.get(index).copied().unwrap_or(false)
    }
    pub fn stats(&self) -> StoreStats {
        StoreStats {
            allocated_slots: self.live.len(),
            pinned_nodes: self
                .pins
                .values()
                .filter(|pin| pin.strong_count() != 0)
                .count(),
            index_capacity_bytes: self.live.capacity()
                + self.pages.capacity() * std::mem::size_of::<Page>()
                + self.pins.capacity() * std::mem::size_of::<(Expression, Weak<Node>)>(),
            ..self.stats
        }
    }
    pub fn set_budget(&mut self, bytes: usize) {
        self.budget = bytes.max(1024 * 1024);
    }

    fn load(&mut self, page: usize) -> io::Result<()> {
        if self.pages[page].nodes.is_some() {
            self.pages[page].recent = true;
            return Ok(());
        }
        let (store, reference) = self.pages[page]
            .external
            .as_ref()
            .ok_or_else(|| io::Error::other("missing expression page"))?;
        let bytes = store.read(reference)?;
        let length = bytes.len() as u64;
        let mut nodes: Vec<Option<Node>> =
            postcard::from_bytes(&bytes).map_err(io::Error::other)?;
        if nodes.len() > PAGE_NODES {
            return Err(io::Error::other("invalid expression page length"));
        }
        nodes.reserve_exact(PAGE_NODES - nodes.len());
        for (slot, node) in nodes.iter_mut().enumerate() {
            let index = page * PAGE_NODES + slot;
            if !self.is_live(index) {
                *node = None;
            }
        }
        let bytes = nodes.capacity() * std::mem::size_of::<Option<Node>>()
            + nodes.iter().flatten().map(payload_bytes).sum::<usize>();
        self.pages[page].nodes = Some(nodes);
        self.pages[page].bytes = bytes;
        self.pages[page].recent = true;
        self.stats.resident_bytes += bytes;
        self.stats.loaded_bytes += length;
        self.stats.loads += 1;
        self.peak();
        self.trim(Some(page))
    }

    fn peak(&mut self) {
        self.stats.peak_resident_bytes = self
            .stats
            .peak_resident_bytes
            .max(self.stats.resident_bytes);
    }

    pub fn trim(&mut self, protected: Option<usize>) -> io::Result<()> {
        if let Some(store) = crate::graph_store::current() {
            self.store = Some(store);
        }
        if protected.is_none() {
            self.pins.retain(|_, node| node.strong_count() > 0);
        }
        let Some(store) = self.store.clone() else {
            return Ok(());
        };
        let mut attempts = 0;
        while self.stats.resident_bytes > self.budget && attempts < self.pages.len() * 2 {
            let index = self.clock % self.pages.len();
            self.clock = (index + 1) % self.pages.len();
            attempts += 1;
            // The append page remains writable until its index range is full.
            if Some(index) == protected
                || (index + 1) * PAGE_NODES > self.len()
                || self.pages[index].nodes.is_none()
            {
                continue;
            }
            if self.pages[index].recent {
                self.pages[index].recent = false;
                continue;
            }
            if self.pages[index].external.is_none() {
                let bytes = postcard::to_stdvec(self.pages[index].nodes.as_ref().unwrap())
                    .map_err(io::Error::other)?;
                let reference = store.write(&bytes)?;
                self.pages[index].external = Some((store.clone(), reference));
                self.stats.stored_bytes += bytes.len() as u64;
            }
            let page = &mut self.pages[index];
            page.nodes = None;
            self.stats.resident_bytes -= page.bytes;
            self.stats.evicted_bytes += page.bytes as u64;
            self.stats.evictions += 1;
        }
        Ok(())
    }

    pub fn push(&mut self, node: Option<Node>) -> io::Result<()> {
        let page = self.len() / PAGE_NODES;
        if self.len().is_multiple_of(PAGE_NODES) {
            let bytes = PAGE_NODES * std::mem::size_of::<Option<Node>>();
            self.pages.push(Page {
                nodes: Some(Vec::with_capacity(PAGE_NODES)),
                bytes,
                ..Page::default()
            });
            self.stats.resident_bytes += bytes;
        }
        self.load(page)?;
        let size = node.as_ref().map_or(0, payload_bytes);
        self.live.push(node.is_some());
        let page = &mut self.pages[page];
        page.nodes.as_mut().unwrap().push(node);
        page.external = None;
        page.bytes += size;
        self.stats.resident_bytes += size;
        self.peak();
        if self.len().is_multiple_of(PAGE_NODES) {
            self.trim(None)?;
        }
        Ok(())
    }

    pub fn get(&mut self, index: usize) -> io::Result<Option<Rc<Node>>> {
        if !self.is_live(index) {
            return Ok(None);
        }
        if let Some(node) = self.hot.get(&index) {
            return Ok(Some(node.clone()));
        }
        if let Some(node) = self
            .pins
            .get(&Expression::from_index(index as u32))
            .and_then(Weak::upgrade)
        {
            return Ok(Some(node));
        }
        let page = index / PAGE_NODES;
        self.load(page)?;
        let node = self.pages[page].nodes.as_ref().unwrap()[index % PAGE_NODES]
            .clone()
            .map(Rc::new);
        if let Some(node) = &node {
            if self.pins.len() >= 131_072 {
                self.pins.retain(|_, node| node.strong_count() > 0);
            }
            self.pins
                .insert(Expression::from_index(index as u32), Rc::downgrade(node));
            self.hot.insert(index, node.clone());
        }
        Ok(node)
    }

    pub fn take(&mut self, index: usize) -> io::Result<Option<Rc<Node>>> {
        let node = self.get(index)?;
        if let Some(node) = &node {
            self.live[index] = false;
            let page = &mut self.pages[index / PAGE_NODES];
            if let Some(nodes) = &mut page.nodes {
                nodes[index % PAGE_NODES] = None;
                let size = payload_bytes(node);
                page.bytes -= size;
                self.stats.resident_bytes -= size;
            }
            self.pins.remove(&Expression::from_index(index as u32));
        }
        Ok(node)
    }

    pub fn truncate(&mut self, length: usize) -> io::Result<()> {
        self.hot.clear();
        for index in length..self.len() {
            if self.is_live(index) {
                self.take(index)?;
            }
        }
        // `take` can populate the read cache. Truncation permits these indices
        // to be allocated again, so their previous values must leave the cache.
        self.hot.clear();
        let pages = length.div_ceil(PAGE_NODES);
        for page in &self.pages[pages..] {
            if page.nodes.is_some() {
                self.stats.resident_bytes -= page.bytes;
            }
        }
        self.pages.truncate(pages);
        self.live.truncate(length);
        self.pins
            .retain(|index, node| index.index() < length && node.strong_count() > 0);
        if !length.is_multiple_of(PAGE_NODES) {
            let page = pages - 1;
            self.load(page)?;
            self.pages[page]
                .nodes
                .as_mut()
                .unwrap()
                .truncate(length % PAGE_NODES);
            self.pages[page].external = None;
        }
        Ok(())
    }

    pub fn pinned(&mut self, mark: usize) -> Vec<Expression> {
        self.hot.clear();
        self.pins.retain(|_, node| node.strong_count() > 0);
        self.pins
            .keys()
            .filter(|e| e.index() >= mark)
            .copied()
            .collect()
    }
}

#[derive(serde::Serialize, serde::Deserialize)]
pub(crate) struct StoredNodes {
    pages: Vec<Vec<u8>>,
    live: Vec<bool>,
}
impl NodeStore {
    pub(crate) fn snapshot(
        &mut self,
        store: Rc<dyn crate::graph_store::GraphStore>,
    ) -> io::Result<StoredNodes> {
        self.store = Some(store.clone());
        let identity = store.identity();
        let mut references = Vec::with_capacity(self.pages.len());
        for index in 0..self.pages.len() {
            let existing = self.pages[index]
                .external
                .as_ref()
                .filter(|(old, _)| old.identity() == identity)
                .map(|(_, reference)| reference.clone());
            let reference = if let Some(reference) = existing {
                store.retain(&reference)?;
                reference
            } else {
                self.load(index)?;
                let bytes = postcard::to_stdvec(self.pages[index].nodes.as_ref().unwrap())
                    .map_err(io::Error::other)?;
                let reference = store.write(&bytes)?;
                self.pages[index].external = Some((store.clone(), reference.clone()));
                reference
            };
            references.push(reference);
        }
        Ok(StoredNodes {
            pages: references,
            live: self.live.clone(),
        })
    }

    pub(crate) fn restore(
        saved: StoredNodes,
        store: Rc<dyn crate::graph_store::GraphStore>,
    ) -> io::Result<Self> {
        if saved.pages.len() != saved.live.len().div_ceil(PAGE_NODES) {
            return Err(io::Error::other("invalid graph page index"));
        }
        for reference in &saved.pages {
            store.retain(reference)?;
        }
        Ok(Self {
            pages: saved
                .pages
                .into_iter()
                .map(|reference| Page {
                    external: Some((store.clone(), reference)),
                    ..Page::default()
                })
                .collect(),
            live: saved.live,
            store: Some(store),
            ..Self::default()
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    #[derive(Debug, Default)]
    struct MemoryPages(RefCell<Vec<Vec<u8>>>);
    impl crate::graph_store::GraphStore for MemoryPages {
        fn identity(&self) -> String {
            "test-pages".into()
        }
        fn write(&self, bytes: &[u8]) -> io::Result<Vec<u8>> {
            let mut pages = self.0.borrow_mut();
            let reference = (pages.len() as u64).to_le_bytes().to_vec();
            pages.push(bytes.to_vec());
            Ok(reference)
        }
        fn read(&self, reference: &[u8]) -> io::Result<Vec<u8>> {
            Ok(self.0.borrow()[u64::from_le_bytes(reference.try_into().unwrap()) as usize].clone())
        }
        fn retain(&self, _: &[u8]) -> io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn without_a_store_nodes_remain_in_memory() {
        let mut nodes = NodeStore::default();
        nodes.set_budget(1024 * 1024);
        for index in 0..PAGE_NODES * 16 {
            nodes.push(Some(Node::Bound(index))).unwrap();
        }
        assert_eq!(nodes.stats().evictions, 0);
        assert_eq!(*nodes.get(7).unwrap().unwrap(), Node::Bound(7));
    }

    #[test]
    fn eviction_and_incremental_snapshots_preserve_live_handles_and_pins() {
        let store = Rc::new(MemoryPages::default());
        let mut nodes = crate::graph_store::with_graph_store(store.clone(), NodeStore::default);
        nodes.set_budget(1024 * 1024);
        for index in 0..PAGE_NODES * 16 {
            nodes.push(Some(Node::Bound(index))).unwrap();
        }
        let pinned = nodes.get(7).unwrap().unwrap();
        assert_eq!(*pinned, Node::Bound(7));
        assert!(nodes.stats().evictions > 0);
        assert!(nodes.stats().resident_bytes < 2 * 1024 * 1024);
        let first = nodes.snapshot(store.clone()).unwrap();
        let writes = store.0.borrow().len();
        nodes.snapshot(store.clone()).unwrap();
        assert_eq!(store.0.borrow().len(), writes);
        nodes.take(9).unwrap();
        for index in PAGE_NODES * 16..PAGE_NODES * 17 {
            nodes.push(Some(Node::Bound(index))).unwrap();
        }
        let second = nodes.snapshot(store.clone()).unwrap();
        assert_eq!(store.0.borrow().len(), writes + 1);
        let mut restored = NodeStore::restore(second, store.clone()).unwrap();
        assert!(restored.get(9).unwrap().is_none());
        assert_eq!(*restored.get(7).unwrap().unwrap(), *pinned);
        let mut earlier = NodeStore::restore(first, store).unwrap();
        assert_eq!(*earlier.get(9).unwrap().unwrap(), Node::Bound(9));
        assert_eq!(*pinned, Node::Bound(7));
        nodes.truncate(PAGE_NODES * 16).unwrap();
        nodes.push(Some(Node::Bound(123))).unwrap();
        assert_eq!(
            *nodes.get(PAGE_NODES * 16).unwrap().unwrap(),
            Node::Bound(123)
        );
        assert_eq!(
            *restored.get(PAGE_NODES * 16).unwrap().unwrap(),
            Node::Bound(PAGE_NODES * 16)
        );
    }
}
