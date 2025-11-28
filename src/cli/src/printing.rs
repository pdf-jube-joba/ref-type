use crate::{Log, StringTree, TreeNode};
use front::logger::{LogLevel, LogPayload, LogRecord};

mod for_front;
mod for_kernel;

// Convert the whole 64 bit pointer to a fixed-length base62 string.
// 62^12 = 3.22 * 10^21 > 2^64 = 1.84 * 10^19
fn ptr_64bit_base62_fixed(ptr: *const ()) -> String {
    const BASE62: &[u8; 62] = b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

    let mut n = ptr as u64;
    let mut buf = [0u8; 12];

    for i in (0..12).rev() {
        buf[i] = BASE62[(n % 62) as usize];
        n /= 62;
    }

    String::from_utf8(buf.to_vec()).unwrap()
}

// Convert the lower 32 bit of pointer to a fixed-length base62 string.
// 62^6 = 3.52 * 10^12 > 2^
fn ptr_lower32bit_base62_fixed(ptr: *const ()) -> String {
    const BASE62: &[u8; 62] = b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

    let mut n = (ptr as u64) & 0xffffffff;
    let mut buf = [0u8; 6];

    for i in (0..6).rev() {
        buf[i] = BASE62[(n % 62) as usize];
        n /= 62;
    }

    String::from_utf8(buf.to_vec()).unwrap()
}

fn print_rc_ptr<T>(rc: &std::rc::Rc<T>) -> String {
    ptr_64bit_base62_fixed(std::rc::Rc::as_ptr(rc) as *const ())
}

pub fn log_record_to_log(record: &front::logger::LogRecord) -> Log {
    match &record.payload {
        LogPayload::DerivationSuccess(derivation) => Log::Derivation(annotate_tree(
            for_kernel::derivation_success_tree(derivation),
            record,
        )),
        LogPayload::DerivationFail(derivation) => Log::Derivation(annotate_tree(
            for_kernel::derivation_fail_tree(derivation),
            record,
        )),
        LogPayload::Exp(exp) => Log::Message(format_record(
            record,
            Some(format!("exp = {}", for_kernel::format_exp(exp))),
        )),
        LogPayload::Ctx(ctx) => Log::Message(format_record(
            record,
            Some(format!("ctx = [{}]", for_kernel::format_ctx(ctx))),
        )),
        LogPayload::Message => Log::Message(format_record(record, None)),
    }
}

fn annotate_tree(tree: StringTree, record: &LogRecord) -> StringTree {
    let prefix = record_prefix(&record.level, &record.tags);
    let base = format!("{prefix} {}", record.message);
    StringTree {
        head: match tree.head {
            TreeNode::Success(s) => TreeNode::Success(format!("{base} :: {s}")),
            TreeNode::ErrorPropagate(s) => TreeNode::ErrorPropagate(format!("{base} :: {s}")),
            TreeNode::ErrorCause(s) => TreeNode::ErrorCause(format!("{base} :: {s}")),
            TreeNode::Pending(s) => TreeNode::Pending(format!("{base} :: {s}")),
        },
        children: tree.children,
    }
}

fn format_record(record: &LogRecord, extra: Option<String>) -> String {
    let mut base = format!(
        "{} {}",
        record_prefix(&record.level, &record.tags),
        record.message
    );
    if let Some(extra) = extra {
        if !extra.is_empty() {
            base.push_str(" | ");
            base.push_str(&extra);
        }
    }
    base
}

fn record_prefix(level: &LogLevel, tags: &[String]) -> String {
    let mut prefix = format!("[{:?}]", level);
    if !tags.is_empty() {
        prefix.push(' ');
        prefix.push('[');
        prefix.push_str(&tags.join(", "));
        prefix.push(']');
    }
    prefix
}
