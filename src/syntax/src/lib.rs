pub mod module_loader;
pub mod package_loader;
pub mod parse;
pub mod sort;
pub mod syntax;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(pub u32);
impl ModuleId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
