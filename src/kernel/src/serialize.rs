use crate::exp::Var;
use serde::ser::{Serialize, SerializeStruct, Serializer};
use std::fmt::Debug;

impl Debug for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ptr_val = self.ptr() as usize;
        write!(f, "{}[{:016x}]", self.as_str(), ptr_val)
    }
}

impl Serialize for Var {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let ptr_val = self.ptr() as usize;
        let ptr_str = format!("{ptr_val:016x}");

        let mut st = serializer.serialize_struct("Var", 2)?;
        st.serialize_field("name", self.as_str())?;
        st.serialize_field("ptr", &ptr_str)?;
        st.end()
    }
}
