use crate::Log;

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

fn print_ptr<T>(ptr: *const T) -> String {
    ptr_64bit_base62_fixed(ptr as *const ())
}

fn print_rc_ptr<T>(rc: &std::rc::Rc<T>) -> String {
    ptr_64bit_base62_fixed(std::rc::Rc::as_ptr(rc) as *const ())
}

pub fn log_record_to_log(record: &front::logger::LogRecord) -> Log {
    todo!()
}