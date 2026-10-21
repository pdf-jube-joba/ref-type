//! Stable, append-only declaration ordinals with storage only for touched slots.
use std::{
    cell::{OnceCell, RefCell},
    collections::BTreeMap,
};

type Cells<T> = BTreeMap<usize, Box<OnceCell<T>>>;

#[derive(Debug, Clone, artifact::Relocate)]
pub(super) struct Slots<T> {
    length: usize,
    cells: OnceCell<Box<RefCell<Cells<T>>>>,
    empty: OnceCell<T>,
}
impl<T> Default for Slots<T> {
    fn default() -> Self {
        Self::reserved(0)
    }
}
impl<T> Slots<T> {
    pub fn reserved(length: usize) -> Self {
        Self {
            length,
            cells: OnceCell::new(),
            empty: OnceCell::new(),
        }
    }
    pub fn len(&self) -> usize {
        self.length
    }
    pub fn touched(&self) -> usize {
        self.cells.get().map_or(0, |cells| cells.borrow().len())
    }
    pub fn get(&self, index: usize) -> Option<&OnceCell<T>> {
        let pointer = self
            .cells
            .get()?
            .borrow()
            .get(&index)
            .map(|cell| cell.as_ref() as *const OnceCell<T>)?;
        // SAFETY: cells are boxed and never removed through a shared reference.
        // Map rebalancing moves boxes, not their allocations. Removal and drop
        // require exclusive access, so the returned reference stays valid.
        Some(unsafe { &*pointer })
    }
    pub fn push(&mut self, cell: OnceCell<T>) {
        if cell.get().is_some() {
            self.cells
                .get_or_init(Default::default)
                .borrow_mut()
                .insert(self.length, Box::new(cell));
        }
        self.length += 1;
    }
    pub fn resize_with(&mut self, length: usize, _: impl FnMut() -> OnceCell<T>) {
        if length < self.length
            && let Some(cells) = self.cells.get_mut()
        {
            cells.get_mut().retain(|index, _| *index < length);
        }
        self.length = length;
    }
    pub fn iter(&self) -> impl Iterator<Item = &OnceCell<T>> {
        (0..self.length).map(|index| self.get(index).unwrap_or(&self.empty))
    }
    pub fn entries(&self) -> Vec<(usize, &OnceCell<T>)> {
        let Some(cells) = self.cells.get() else {
            return Vec::new();
        };
        cells
            .borrow()
            .keys()
            .map(|&index| (index, self.get(index).unwrap()))
            .collect()
    }
    pub fn into_entries(self) -> impl Iterator<Item = (usize, OnceCell<T>)> {
        self.cells
            .into_inner()
            .map(|cells| cells.into_inner())
            .unwrap_or_default()
            .into_iter()
            .map(|(index, cell)| (index, *cell))
    }
}
impl<T> std::ops::Index<usize> for Slots<T> {
    type Output = OnceCell<T>;
    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.length, "declaration slot out of range");
        self.cells
            .get_or_init(Default::default)
            .borrow_mut()
            .entry(index)
            .or_default();
        self.get(index).unwrap()
    }
}
