#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    use chrono::Local;
    use std::env;

    if !data.iter().any(|d| *d == 0) {
        if let Ok(data) = std::str::from_utf8(data) {
            dbg!(data);
            env::set_var("TZ", data);
            let _ = Local::now();
        }
    }
});
