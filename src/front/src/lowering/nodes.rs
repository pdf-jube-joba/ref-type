//! Allocate logical syntax after lowering has established its family.
//! Keep the allowed families explicit at each call site. Field conversions are
//! type-checked separately for every family; there is no dynamic dispatch.
macro_rules! logical_node {
    ($this:expr, $sort:expr, $family:expr; $($allowed:ident)|+ => $variant:ident $fields:tt) => {
        logical_node!($this, $sort, $family; $($allowed)|+ => $variant $fields;
            "constructor cannot inhabit this syntax family")
    };
    ($this:expr, $sort:expr, $family:expr; $($allowed:ident)|+ => $variant:ident $fields:tt; $error:literal) => {
        match $family {
            $(s::Family::$allowed => logical_node!(@alloc $this, $sort, $allowed, $variant $fields),)+
            _ => return Err($error.into()),
        }
    };
    (@alloc $this:expr, $sort:expr, SetTerm, $variant:ident $fields:tt) => {
        $this.kernel.arena().alloc(s::SetTermNode {
            level: $sort.level().ok_or("expected Set level")?,
            form: s::SetTermForm::$variant $fields,
        }).into()
    };
    (@alloc $this:expr, $sort:expr, SetType, $variant:ident $fields:tt) => {
        $this.kernel.arena().alloc(s::SetTypeNode {
            level: $sort.level().ok_or("expected Set level")?,
            form: s::SetTypeForm::$variant $fields,
        }).into()
    };
    (@alloc $this:expr, $sort:expr, SetKind, $variant:ident $fields:tt) => {
        $this.kernel.arena().alloc(s::SetKindNode {
            level: $sort.level().ok_or("expected Set level")?,
            form: s::SetKindForm::$variant $fields,
        }).into()
    };
    (@alloc $this:expr, $sort:expr, PropTerm, $variant:ident $fields:tt) => {
        $this.kernel.arena().alloc(s::PropTermNode {
            form: s::PropTermForm::$variant $fields,
        }).into()
    };
    (@alloc $this:expr, $sort:expr, PropType, $variant:ident $fields:tt) => {
        $this.kernel.arena().alloc(s::PropTypeNode {
            form: s::PropTypeForm::$variant $fields,
        }).into()
    };
    (@alloc $this:expr, $sort:expr, PropKind, $variant:ident $fields:tt) => {
        $this.kernel.arena().alloc(s::PropKindNode {
            form: s::PropKindForm::$variant $fields,
        }).into()
    };
}

pub(super) use logical_node;
