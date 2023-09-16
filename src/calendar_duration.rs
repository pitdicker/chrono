use core::fmt;
use core::num::NonZeroU32;
use core::str;
use core::time::Duration;

use crate::format::{parse_iso8601_duration, ParseError, TOO_LONG};
use crate::{expect, try_opt};

/// ISO 8601 duration type.
///
/// With this type a duration can be expressed as a combination of four components: *months*,
/// *days*, *minutes*, and *seconds and nanoseconds*.
///
/// # Examples
///
/// ```
/// # use chrono::CalendarDuration;
/// // Encoding 1½ year as a duration of a year and 6 months:
/// let _duration = CalendarDuration::new().with_years_and_months(1, 6).unwrap();
///
/// // Encoding 1½ year as a duration of 12 months and 183 days (366 / 2):
/// let _duration = CalendarDuration::new().with_months(12).with_days(183);
///
/// // Encoding 1½ year as a duration of 548 days (365 + 366 / 2):
/// let _duration = CalendarDuration::new().with_days(548);
///
/// // Encoding 1½ year as a duration in seconds:
/// let _duration = CalendarDuration::new().with_seconds(548 * 24 * 60 * 60);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CalendarDuration {
    // Components with a nominal duration
    months: u32,
    days: u32,
    // Components with an accurate duration
    // `seconds` can either encode `minutes << 6 | seconds`, or just seconds.
    seconds: u32,
    // `nanos` encodes `nanoseconds << 2 | has_minutes << 1 | 1`.
    nanos: NonZeroU32,
}

impl Default for CalendarDuration {
    fn default() -> Self { CalendarDuration::new() }
}

impl fmt::Debug for CalendarDuration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (mins, secs) = self.mins_and_secs();
        f.debug_struct("CalendarDuration")
            .field("months", &self.months)
            .field("days", &self.days)
            .field("minutes", &mins)
            .field("seconds", &secs)
            .field("nanos", &self.nanos())
            .finish()
    }
}

impl fmt::Display for CalendarDuration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("P")?;
        // Plenty of ways to encode an empty string. `P0D` is short and not too strange.
        if self.is_zero() {
            return f.write_str("0D");
        }

        // Nominal components
        let years = self.months / 12;
        let months = self.months % 12;
        if years > 0 {
            f.write_fmt(format_args!("{}Y", years))?;
        }
        if months > 0 {
            f.write_fmt(format_args!("{}M", months))?;
        }
        if self.days > 0 {
            f.write_fmt(format_args!("{}D", self.days))?;
        }

        // Accurate components
        let nanos = self.nanos();
        if self.seconds == 0 && nanos == 0 {
            return Ok(());
        }
        f.write_str("T")?;
        let (mins, secs) = self.mins_and_secs();
        let hours = mins / 60;
        let mins = mins % 60;
        if hours > 0 {
            f.write_fmt(format_args!("{}H", hours))?;
        }
        if mins > 0 {
            f.write_fmt(format_args!("{}M", mins))?;
        }

        if secs == 0 && nanos == 0 {
            return Ok(());
        }
        f.write_fmt(format_args!("{}", secs))?;
        if nanos > 0 {
            // Count the number of significant digits, while removing all trailing zero's.
            let mut figures = 9usize;
            let mut fraction_digits = nanos;
            loop {
                let div = fraction_digits / 10;
                let last_digit = fraction_digits % 10;
                if last_digit != 0 {
                    break;
                }
                fraction_digits = div;
                figures -= 1;
            }
            f.write_fmt(format_args!(".{:01$}", fraction_digits, figures))?;
        }
        f.write_str("S")?;
        Ok(())
    }
}

impl str::FromStr for CalendarDuration {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<CalendarDuration, ParseError> {
        let (s, duration) = parse_iso8601_duration(s)?;
        if !s.is_empty() {
            return Err(TOO_LONG);
        }
        Ok(duration)
    }
}

impl CalendarDuration {
    /// Create a new duration initialized to `0`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use chrono::CalendarDuration;
    /// // Duration in calendar months and days.
    /// CalendarDuration::new().with_months(15).with_days(5);
    /// // Duration in calendar days, and 3 hours.
    /// CalendarDuration::new().with_days(5).with_hms(3, 0, 0).unwrap();
    /// // Duration that will precisely count the number of seconds, including leap seconds.
    /// CalendarDuration::new().with_seconds(23_456).with_millis(789).unwrap();
    /// ```
    pub const fn new() -> Self {
        Self {
            months: 0,
            days: 0,
            seconds: 0,
            nanos: expect!(NonZeroU32::new(1), "can't fail, non-zero"),
        }
    }

    /// Set the months component of this duration to `months`.
    pub const fn with_months(mut self, months: u32) -> Self {
        self.months = months;
        self
    }

    /// Set the months component of this duration to `years * 12 + months`.
    ///
    ///  # Errors
    ///
    /// Returns `None` if the value of the months component would be out of range.
    pub const fn with_years_and_months(mut self, years: u32, months: u32) -> Option<Self> {
        self.months = try_opt!(try_opt!(years.checked_mul(12)).checked_add(months));
        Some(self)
    }

    /// Set the days component of this duration to `days`.
    pub const fn with_days(mut self, days: u32) -> Self {
        self.days = days;
        self
    }

    /// Set the days component of this duration to `weeks * 7 + days`.
    ///
    ///  # Errors
    ///
    /// Returns `None` if the value of the days component would be out of range.
    pub const fn with_weeks_and_days(mut self, weeks: u32, days: u32) -> Option<Self> {
        self.days = try_opt!(try_opt!(weeks.checked_mul(7)).checked_add(days));
        Some(self)
    }

    /// Sets the accurate component of this duration to a value in minutes and seconds.
    ///
    /// The definition of a minute is not exactly 60 seconds; it can also be 61 or 59 in the
    /// presence of leap seconds.
    ///
    /// Durations made with this method are the closest thing to working like leap seconds don't
    /// exists.
    ///
    /// # Errors
    ///
    /// Returns `None` if `seconds` exceeds 60, of if the value of the minutes component
    /// (`hours * 60 + minutes`) would be out of range.
    pub const fn with_hms(mut self, hours: u32, minutes: u32, seconds: u32) -> Option<Self> {
        if seconds > 60 {
            return None;
        }
        let minutes = try_opt!(try_opt!(hours.checked_mul(60)).checked_add(minutes));
        if minutes > (u32::MAX >> 6) || seconds >= (1 << 6) {
            return None;
        }
        self.seconds = minutes << 6 | seconds;
        // Set the `0b10` flag that we store as discriminant in `nanos`.
        self.nanos = expect!(
            NonZeroU32::new(self.nanos.get() | 0b10),
            "can't fail because the `| 0b10` ensures the value is non-zero"
        );
        Some(self)
    }

    /// Sets the accurate component of this duration to a value in seconds.
    ///
    /// This duration will count an exact number of seconds, which includes the counting of leap
    /// seconds.
    pub const fn with_seconds(mut self, seconds: u32) -> Self {
        self.seconds = seconds;
        // Clear the `0b10` flag that we store as discriminant in `nanos`.
        self.nanos = expect!(
            NonZeroU32::new((self.nanos.get() & !0b10) | 1),
            "can't fail because the `| 1` ensures the value is non-zero"
        );
        self
    }

    /// Sets the nanoseconds component of this duration to `nanos`.
    ///
    /// # Errors
    ///
    /// Returns `None` if `nanos` exceeds 999_999_999.
    pub const fn with_nanos(mut self, nanos: u32) -> Option<Self> {
        if nanos >= 1_000_000_000 {
            return None;
        }
        self.nanos = expect!(
            NonZeroU32::new(nanos << 2 | (self.nanos.get() & 0b10) | 1),
            "can't fail because the `| 1` ensures the value is non-zero"
        );
        Some(self)
    }

    /// Sets the nanoseconds component of this duration to `micros * 1000`.
    ///
    /// # Errors
    ///
    /// Returns `None` if `micros` exceeds 999_999.
    pub const fn with_micros(self, micros: u32) -> Option<Self> {
        if micros >= 1_000_000 {
            return None;
        }
        self.with_nanos(micros * 1000)
    }

    /// Sets the nanoseconds component of this duration to `millis * 1000`.
    ///
    /// # Errors
    ///
    /// Returns `None` if `millis` exceeds 999.
    pub const fn with_millis(self, millis: u32) -> Option<Self> {
        if millis >= 1000 {
            return None;
        }
        self.with_nanos(millis * 1_000_000)
    }

    /// Returns the `months` component of this calendar duration.
    pub const fn months(&self) -> u32 {
        self.months
    }

    /// Returns the `days` component of this calendar duration.
    pub const fn days(&self) -> u32 {
        self.days
    }

    /// Returns the `minutes` and `seconds` components of this calendar duration.
    pub const fn mins_and_secs(&self) -> (u32, u32) {
        match self.nanos.get() & 0b10 != 0 {
            true => (self.seconds >> 6, self.seconds & 0b11_1111),
            false => (0, self.seconds),
        }
    }

    /// Returns the `nanos` component of this calendar duration.
    pub const fn nanos(&self) -> u32 {
        self.nanos.get() >> 2
    }

    /// Returns `true` if this `CalendarDuration` spans no time.
    pub const fn is_zero(&self) -> bool {
        self.months == 0 && self.days == 0 && self.seconds == 0 && self.nanos() == 0
    }
}

impl From<Duration> for CalendarDuration {
    fn from(value: Duration) -> Self {
        let seconds = u32::try_from(value.as_secs()).expect("value of `Duration` out of range");
        Self::new().with_seconds(seconds).with_nanos(value.subsec_nanos()).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::CalendarDuration;
    use std::time::Duration;

    #[test]
    fn test_basic_functionality() {
        #[track_caller]
        fn compare(d: CalendarDuration, months: u32, days: u32, mins: u32, secs: u32, nanos: u32) {
            assert_eq!(d.months(), months);
            assert_eq!(d.days(), days);
            assert_eq!((d.mins_and_secs()), (mins, secs));
            assert_eq!(d.nanos(), nanos);
        }

        let duration = CalendarDuration::new()
            .with_months(1)
            .with_days(2)
            .with_hms(3, 4, 5)
            .unwrap()
            .with_nanos(6)
            .unwrap();
        compare(duration, 1, 2, 3 * 60 + 4, 5, 6);

        compare(CalendarDuration::new().with_months(18), 18, 0, 0, 0, 0);
        compare(CalendarDuration::new().with_years_and_months(1, 6).unwrap(), 18, 0, 0, 0, 0);
        compare(CalendarDuration::new().with_days(15), 0, 15, 0, 0, 0);
        compare(CalendarDuration::new().with_weeks_and_days(2, 1).unwrap(), 0, 15, 0, 0, 0);
        compare(CalendarDuration::new().with_hms(3, 4, 5).unwrap(), 0, 0, 3 * 60 + 4, 5, 0);
        compare(CalendarDuration::new().with_seconds(123_456), 0, 0, 0, 123_456, 0);
        compare(CalendarDuration::new().with_nanos(123_456_789).unwrap(), 0, 0, 0, 0, 123_456_789);
        assert!(CalendarDuration::new().is_zero());
    }

    #[test]
    fn test_from_std_duration() {
        assert_eq!(
            CalendarDuration::new().with_seconds(7).with_nanos(8).unwrap(),
            Duration::new(7, 8).into()
        );
    }

    #[test]
    #[should_panic]
    fn test_from_extreme_duration_panics() {
        let _ = CalendarDuration::from(Duration::new(1 << 32, 0));
    }

    #[test]
    fn test_display_format() {
        let new = CalendarDuration::new;

        assert_eq!(
            new().with_months(45).with_days(5).with_hms(6, 5, 43).unwrap().to_string(),
            "P3Y9M5DT6H5M43S"
        );
        assert_eq!(new().to_string(), "P0D");
        assert_eq!(new().with_years_and_months(2, 0).unwrap().to_string(), "P2Y");
        assert_eq!(new().with_months(3).to_string(), "P3M");
        assert_eq!(new().with_weeks_and_days(3, 4).unwrap().to_string(), "P25D");
        assert_eq!(new().with_days(25).to_string(), "P25D");
        assert_eq!(new().with_hms(2, 0, 0).unwrap().to_string(), "PT2H");
        assert_eq!(new().with_hms(0, 3, 0).unwrap().to_string(), "PT3M");
        assert_eq!(new().with_hms(0, 0, 15).unwrap().to_string(), "PT15S");
        assert_eq!(
            new().with_hms(2, 3, 45).unwrap().with_millis(678).unwrap().to_string(),
            "PT2H3M45.678S"
        );
        assert_eq!(new().with_seconds(123_456).to_string(), "PT123456S");
        assert_eq!(new().with_micros(123).unwrap().to_string(), "PT0.000123S");
        assert_eq!(new().with_days(5).with_millis(123).unwrap().to_string(), "P5DT0.123S");
    }

    #[test]
    fn test_type_sizes() {
        use core::mem::size_of;
        assert_eq!(size_of::<CalendarDuration>(), 16);
        assert_eq!(size_of::<Option<CalendarDuration>>(), 16);
    }
}
