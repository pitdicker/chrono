#[cfg(test)]
use core::fmt::{self, Write};

/// Sink that will return an error when bytes are written to it that do not match `expected`.
#[cfg(test)]
#[allow(dead_code)]
pub(crate) struct WriteCompare<'a> {
    expected: &'a str,
    remainder: &'a str,
}

#[cfg(test)]
impl<'a> WriteCompare<'a> {
    pub(crate) fn new(expected: &'a str) -> Self {
        Self { expected, remainder: expected }
    }
}

#[cfg(test)]
impl<'a> Write for WriteCompare<'a> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if let Some(remainder) = self.remainder.strip_prefix(s) {
            self.remainder = remainder;
            Ok(())
        } else {
            #[cfg(feature = "std")]
            eprintln!(
                "formatting difference: `(left == right)`\n  left: `\"{}{}(...)\"`\n right: `\"{}\"`",
                &self.expected[..(self.expected.len() - self.remainder.len())],
                s,
                self.expected
            );
            Err(fmt::Error)
        }
    }
}

#[cfg(test)]
#[track_caller]
pub(crate) fn assert_display_eq<D>(value: D, expected: &str)
where
    D: fmt::Display,
{
    write!(&mut WriteCompare::new(expected), "{}", value).unwrap();
}

#[cfg(test)]
#[track_caller]
pub(crate) fn assert_debug_eq<D>(value: D, expected: &str)
where
    D: fmt::Debug,
{
    write!(&mut WriteCompare::new(expected), "{:?}", value).unwrap();
}
