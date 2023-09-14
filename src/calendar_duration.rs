use core::fmt;
use core::num::NonZeroU32;

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
        let has_minutes = ((minutes != 0) as u32) << 1;
        self.nanos = expect!(
            NonZeroU32::new(self.nanos.get() | has_minutes | 1),
            "can't fail because the `| 1` ensures the value is non-zero"
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

#[cfg(test)]
mod tests {
    use super::CalendarDuration;

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
    fn test_invalid_returns_none() {
        assert!(CalendarDuration::new().with_years_and_months(0, u32::MAX).is_some());
        assert!(CalendarDuration::new().with_years_and_months(u32::MAX / 12 + 1, 0).is_none());
        assert!(CalendarDuration::new().with_years_and_months(u32::MAX, 0).is_none());
        assert!(CalendarDuration::new().with_years_and_months(u32::MAX, 1).is_none());

        assert!(CalendarDuration::new().with_weeks_and_days(0, u32::MAX).is_some());
        assert!(CalendarDuration::new().with_weeks_and_days(u32::MAX / 7 + 1, 0).is_none());
        assert!(CalendarDuration::new().with_weeks_and_days(u32::MAX, 0).is_none());
        assert!(CalendarDuration::new().with_weeks_and_days(u32::MAX, 1).is_none());

        assert!(CalendarDuration::new().with_nanos(1_000_000_000).is_none());
        assert!(CalendarDuration::new().with_nanos(u32::MAX).is_none());
        assert!(CalendarDuration::new().with_micros(1_000_000).is_none());
        assert!(CalendarDuration::new().with_micros(u32::MAX).is_none());
        assert!(CalendarDuration::new().with_millis(1_000_000).is_none());
        assert!(CalendarDuration::new().with_millis(u32::MAX).is_none());
    }

    #[test]
    fn test_type_sizes() {
        use core::mem::size_of;
        assert_eq!(size_of::<CalendarDuration>(), 16);
        assert_eq!(size_of::<Option<CalendarDuration>>(), 16);
    }
}
