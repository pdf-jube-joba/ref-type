use crate::exp::Var;
use serde::ser::{Serialize, SerializeStruct, Serializer};
use std::rc::Rc;

impl Serialize for Var {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // ポインタを 16進文字列にする（今の print_ptr と同じノリでOK）
        let ptr_val = self.ptr() as usize;
        let ptr_str = format!("{ptr_val:016x}");

        let mut st = serializer.serialize_struct("Var", 2)?;
        st.serialize_field("name", self.as_str())?;
        st.serialize_field("ptr", &ptr_str)?;
        st.end()
    }
}

/// serialize Rc<T> as pointer string
pub fn serialize_rc_ptr<S, T>(rc: &Rc<T>, s: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let ptr = Rc::as_ptr(rc) as usize;
    let s_repr = format!("{ptr:016x}");
    s.serialize_str(&s_repr)
}

/// same idea, but for Option<Rc<T>>
pub fn serialize_opt_rc_ptr<S, T>(opt: &Option<Rc<T>>, s: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match opt {
        Some(rc) => serialize_rc_ptr(rc, s),
        None => s.serialize_none(),
    }
}
