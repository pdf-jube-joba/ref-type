use crate::Log;
use front::logger::{LogLevel, LogPayload, LogRecord};

mod for_kernel;

// Convert the whole 64 bit pointer to a fixed-length base62 string.
// 62^12 = 3.22 * 10^21 > 2^64 = 1.84 * 10^19
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

pub fn log_record_to_log(
    env: &kernel::environment::CrateEnv,
    record: &front::logger::LogRecord,
) -> Log {
    match &record.payload {
        LogPayload::Exp(exp) => Log::Message(format_record(
            record,
            Some(format!("exp = {}", for_kernel::format_exp(env, *exp))),
        )),
        LogPayload::Ctx(ctx) => Log::Message(format_record(
            record,
            Some(format!("ctx = [{}]", for_kernel::format_ctx(env, ctx))),
        )),
        LogPayload::Message => Log::Message(format_record(record, None)),
    }
}

fn format_record(record: &LogRecord, extra: Option<String>) -> String {
    let mut base = format!(
        "{} {}",
        record_prefix(&record.level, &record.tags),
        record.message
    );
    if let Some(extra) = extra
        && !extra.is_empty()
    {
        base.push_str(" | ");
        base.push_str(&extra);
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
