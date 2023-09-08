//! Macro's for easy initialization of date and time values.

/// Create a `NaiveDate` with a statically known value.
///
/// Supported formats are 'year-month-day' and 'year-ordinal'.
///
/// Note: rustfmt wants to add spaces around `-` in this macro.
/// For nice formatting use `#[rustfmt::skip::macros(date)]`, or use as `date! {2023-09-08}`
///
/// # Examples
/// ```
/// use chrono::date;
///
/// assert_eq!(date!(2023-09-08), date!(2023-251));
/// ```
#[macro_export]
macro_rules! date {
    ($y:literal-$m:literal-$d:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        match $crate::NaiveDate::from_ymd_opt($y, $m, $d) {
            Some(d) => d,
            None => panic!("invalid calendar date"),
        }
    }};
    ($y:literal-$o:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        match $crate::NaiveDate::from_yo_opt($y, $o) {
            Some(d) => d,
            None => panic!("invalid ordinal date"),
        }
    }};
}

/// Create a `NaiveTime` with a statically known value.
///
/// Supported formats are 'hour:minute' and 'hour:minute:second'.
///
/// # Examples
/// ```
/// use chrono::time;
/// # use chrono::Timelike;
///
/// assert_eq!(time!(7:03), time!(7:03:00));
/// let leap_second = time!(23:59:60);
/// # assert!(leap_second.second() == 59 && leap_second.nanosecond() == 1_000_000_000);
/// ```
#[macro_export]
macro_rules! time {
    ($h:literal:$m:literal:$s:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            let (s, nanos) = match $s {
                60u32 => (59, 1_000_000_000),
                s => (s, 0),
            };
            match $crate::NaiveTime::from_hms_nano_opt($h, $m, s, nanos) {
                Some(t) => t,
                None => panic!("invalid time"),
            }
        }
    }};
    ($h:literal:$m:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        match $crate::NaiveTime::from_hms_opt($h, $m, 0) {
            Some(t) => t,
            None => panic!("invalid time"),
        }
    }};
}

/// Create a `NaiveDateTime` or `DateTime<FixedOffset>` with a statically known value.
///
/// # Examples
/// ```
/// use chrono::datetime;
///
/// // NaiveDateTime
/// let _ = datetime!(2023-09-08 7:03);
/// let _ = datetime!(2023-09-08 7:03:25);
/// // DateTime<FixedOffset>
/// let _ = datetime!(2023-09-08 7:03:25+02:00);
/// let _ = datetime!(2023-09-08 7:03:25-02:00);
/// ```
#[macro_export]
macro_rules! datetime {
    ($y:literal-$m:literal-$d:literal $h:literal:$min:literal:$s:literal+$hh:literal:$mm:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            let date = match $crate::NaiveDate::from_ymd_opt($y, $m, $d) {
                Some(d) => d,
                None => panic!("invalid calendar date"),
            };
            let (s, nanos) = match $s {
                60u32 => (59, 1_000_000_000),
                s => (s, 0),
            };
            let time = match $crate::NaiveTime::from_hms_nano_opt($h, $min, s, nanos) {
                Some(t) => t,
                None => panic!("invalid time"),
            };
            assert!($hh < 24u32 || $mm < 60, "invalid offset");
            let offset = match $crate::FixedOffset::east_opt(($hh * 3600 + $mm * 60) as i32) {
                Some(o) => o,
                None => panic!("invalid offset"),
            };
            let dt = match date.and_time(time).checked_sub_offset(offset) {
                Some(o) => o,
                None => panic!("datetime out of range"),
            };
            $crate::DateTime::<$crate::FixedOffset>::from_naive_utc_and_offset(dt, offset)
        }
    }};
    ($y:literal-$m:literal-$d:literal $h:literal:$min:literal:$s:literal-$hh:literal:$mm:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            let date = match $crate::NaiveDate::from_ymd_opt($y, $m, $d) {
                Some(d) => d,
                None => panic!("invalid calendar date"),
            };
            let (s, nanos) = match $s {
                60u32 => (59, 1_000_000_000),
                s => (s, 0),
            };
            let time = match $crate::NaiveTime::from_hms_nano_opt($h, $min, s, nanos) {
                Some(t) => t,
                None => panic!("invalid time"),
            };
            assert!($hh < 24u32 || $mm < 60, "invalid offset");
            let offset = match $crate::FixedOffset::west_opt(($hh * 3600 + $mm * 60) as i32) {
                Some(o) => o,
                None => panic!("invalid offset"),
            };
            let dt = match date.and_time(time).checked_sub_offset(offset) {
                Some(o) => o,
                None => panic!("datetime out of range"),
            };
            $crate::DateTime::<$crate::FixedOffset>::from_naive_utc_and_offset(dt, offset)
        }
    }};
    ($y:literal-$m:literal-$d:literal $h:literal:$min:literal:$s:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            let date = match $crate::NaiveDate::from_ymd_opt($y, $m, $d) {
                Some(d) => d,
                None => panic!("invalid calendar date"),
            };
            let (s, nanos) = match $s {
                60u32 => (59, 1_000_000_000),
                s => (s, 0),
            };
            let time = match $crate::NaiveTime::from_hms_nano_opt($h, $min, s, nanos) {
                Some(t) => t,
                None => panic!("invalid time"),
            };
            date.and_time(time)
        }
    }};
    ($y:literal-$m:literal-$d:literal $h:literal:$min:literal) => {{
        #[allow(clippy::zero_prefixed_literal)]
        {
            let date = match $crate::NaiveDate::from_ymd_opt($y, $m, $d) {
                Some(d) => d,
                None => panic!("invalid calendar date"),
            };
            let time = match $crate::NaiveTime::from_hms_opt($h, $min, 0) {
                Some(t) => t,
                None => panic!("invalid time"),
            };
            date.and_time(time)
        }
    }};
}

#[cfg(test)]
#[rustfmt::skip::macros(date)]
mod tests {
    use crate::{FixedOffset, NaiveDate, NaiveTime, TimeZone};

    #[test]
    fn init_macros() {
        assert_eq!(date!(2023-09-08), NaiveDate::from_ymd_opt(2023, 9, 8).unwrap());
        assert_eq!(date!(2023-253), NaiveDate::from_yo_opt(2023, 253).unwrap());
        assert_eq!(time!(7:03), NaiveTime::from_hms_opt(7, 3, 0).unwrap());
        assert_eq!(time!(7:03:25), NaiveTime::from_hms_opt(7, 3, 25).unwrap());
        assert_eq!(
            time!(23:59:60),
            NaiveTime::from_hms_nano_opt(23, 59, 59, 1_000_000_000).unwrap()
        );
        assert_eq!(
            datetime!(2023-09-08 7:03),
            NaiveDate::from_ymd_opt(2023, 9, 8).unwrap().and_hms_opt(7, 3, 0).unwrap(),
        );
        assert_eq!(
            datetime!(2023-09-08 7:03:25),
            NaiveDate::from_ymd_opt(2023, 9, 8).unwrap().and_hms_opt(7, 3, 25).unwrap(),
        );
        assert_eq!(
            datetime!(2023-09-08 7:03:25+02:00),
            FixedOffset::east_opt(7200).unwrap().with_ymd_and_hms(2023, 9, 8, 7, 3, 25).unwrap(),
        );
        assert_eq!(
            datetime!(2023-09-08 7:03:25-02:00),
            FixedOffset::east_opt(-7200).unwrap().with_ymd_and_hms(2023, 9, 8, 7, 3, 25).unwrap(),
        );
    }
}
