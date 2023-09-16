use super::scan;
use super::{ParseResult, INVALID, OUT_OF_RANGE};
use crate::CalendarDuration;

/// Parser for the ISO 8601 designator fromat for a duration.
///
/// Supported formats:
/// - `Pnn̲Ynn̲Mnn̲DTnn̲Hnn̲Mnn̲S`
/// - `Pnn̲W`
pub(crate) fn parse_iso8601_duration(mut s: &str) -> ParseResult<(&str, CalendarDuration)> {
    macro_rules! consume {
        ($e:expr) => {{
            $e.map(|(s_, v)| {
                s = s_;
                v
            })
        }};
    }

    s = scan::char(s, b'P')?;
    let mut duration = CalendarDuration::new();

    let mut next = consume!(Decimal::parse(s)).ok();
    if let Some(val) = next {
        if s.as_bytes().first() == Some(&b'W') {
            s = &s[1..];
            // Nothing is allowed after a week value
            return Ok((s, duration.with_days(val.mul(7)?)));
        }
        if s.as_bytes().first() == Some(&b'Y') {
            s = &s[1..];
            duration = duration.with_months(val.mul(12)?);
            if val.fraction.is_some() {
                return Ok((s, duration));
            }
            next = consume!(Decimal::parse(s)).ok();
        }
    }

    if let Some(val) = next {
        if s.as_bytes().first() == Some(&b'M') {
            s = &s[1..];
            let months = duration.months().checked_add(val.integer()?).ok_or(OUT_OF_RANGE)?;
            duration = duration.with_months(months);
            next = consume!(Decimal::parse(s)).ok();
        }
    }

    if let Some(val) = next {
        if s.as_bytes().first() == Some(&b'D') {
            s = &s[1..];
            duration = duration.with_days(val.integer()?);
            next = None;
        }
    }

    if next.is_some() {
        // We have numbers without a matching designator.
        return Err(INVALID);
    }

    if s.as_bytes().first() == Some(&b'T') {
        if let Ok((s_, (hours, minutes, seconds, nanoseconds))) = parse_iso8601_duration_time(s) {
            s = s_;
            duration = match (hours, minutes) {
                (0, 0) => duration.with_hms(hours, minutes, seconds).ok_or(OUT_OF_RANGE)?,
                _ => duration.with_seconds(seconds),
            };
            duration = duration.with_nanos(nanoseconds).unwrap();
        }
    }
    Ok((s, duration))
}

/// The time part is encoded with up to three pairs of integers and designators.
/// The last pair may contain a decimal fraction instead of an integer.
///
/// We start parsing a new pair as a decimal fraction and designator. If there is data after a
/// fractional value we return it as trailing data, instead of calling the string invalid.
///
/// Supported formats:
/// - `Tnn̲H`
/// - `Tnn̲.nn̲H`
/// - `Tnn̲Hnn̲M`
/// - `Tnn̲Hnn̲.nn̲M`
/// - `Tnn̲Hnn̲Mnn̲S`
/// - `Tnn̲Hnn̲Mnn̲.nn̲S`
/// - `Tnn̲M`
/// - `Tnn̲.nn̲M`
/// - `Tnn̲Mnn̲S`
/// - `Tnn̲Mnn̲.nn̲S`
/// - `Tnn̲S`
/// - `Tnn̲.nn̲S`
pub(crate) fn parse_iso8601_duration_time(
    mut s: &str,
) -> ParseResult<(&str, (u32, u32, u32, u32))> {
    macro_rules! consume_or_return {
        ($e:expr, $return:expr) => {{
            match $e {
                Ok((s_, next)) => {
                    s = s_;
                    next
                }
                Err(_) => return $return,
            }
        }};
    }

    s = scan::char(s, b'T')?;
    let mut hours = 0;
    let mut minutes = 0;
    let mut incomplete = true; // at least one component is required

    let (s_, mut next) = Decimal::parse(s)?;
    s = s_;
    if s.as_bytes().first() == Some(&b'H') {
        s = &s[1..];
        incomplete = false;
        match next.integer() {
            Ok(h) => hours = h,
            _ => {
                let (secs, nanos) = next.mul_with_nanos(3600)?;
                let mins = secs / 60;
                let secs = (secs % 60) as u32;
                let minutes = u32::try_from(mins).map_err(|_| OUT_OF_RANGE)?;
                return Ok((s, (0, minutes, secs, nanos)));
            }
        }
        next = consume_or_return!(Decimal::parse(s), Ok((s, (hours, minutes, 0, 0))));
    }

    if s.as_bytes().first() == Some(&b'M') {
        s = &s[1..];
        incomplete = false;
        match next.integer() {
            Ok(m) => minutes = m,
            _ => {
                let (secs, nanos) = next.mul_with_nanos(60)?;
                let mins = secs / 60;
                let secs = (secs % 60) as u32;
                minutes = u32::try_from(mins).map_err(|_| OUT_OF_RANGE)?;
                return Ok((s, (hours, minutes, secs, nanos)));
            }
        }
        next = consume_or_return!(Decimal::parse(s), Ok((s, (hours, minutes, 0, 0))));
    }

    if s.as_bytes().first() == Some(&b'S') {
        s = &s[1..];
        let (secs, nanos) = next.mul_with_nanos(1)?;
        let secs = u32::try_from(secs).map_err(|_| OUT_OF_RANGE)?;
        return Ok((s, (hours, minutes, secs, nanos)));
    }

    if incomplete {
        return Err(INVALID);
    }
    Ok((s, (hours, minutes, 0, 0)))
}

/// Helper type for parsing decimals (as in an ISO 8601 duration).
#[derive(Copy, Clone)]
struct Decimal {
    base: u32,
    fraction: Option<Fraction>,
}

impl Decimal {
    fn parse(s: &str) -> ParseResult<(&str, Self)> {
        let (s, num) = scan::number(s, 1, 10)?;
        let (s, frac) = match Fraction::parse(s) {
            Ok((s, frac)) => (s, Some(frac)),
            Err(_) => (s, None),
        };
        let result =
            Decimal { base: u32::try_from(num).map_err(|_| OUT_OF_RANGE)?, fraction: frac };
        Ok((s, result))
    }

    /// Multiplying this `Decimal` with `unit`.
    ///
    /// Returns `None` on out of range.
    fn mul(&self, unit: u32) -> ParseResult<u32> {
        let frac = self.fraction.unwrap_or(Fraction(0)).mul(unit as u64) as u32;
        self.base.checked_mul(unit).and_then(|n| n.checked_add(frac)).ok_or(OUT_OF_RANGE)
    }

    /// Returns the result of multiplying this `Decimal` with `unit`.
    ///
    /// Returns two integers to represent the whole number and the fraction as nanos.
    fn mul_with_nanos(&self, unit: u64) -> ParseResult<(u64, u32)> {
        let (whole_from_rounding, fraction_as_nanos) =
            self.fraction.unwrap_or(Fraction(0)).mul_with_nanos(unit);
        let whole = (self.base as u64)
            .checked_mul(unit)
            .and_then(|n| n.checked_add(whole_from_rounding as u64))
            .ok_or(OUT_OF_RANGE)?;
        Ok((whole, fraction_as_nanos as u32))
    }

    /// Returns the value of this `Decimal` if it is an integer, otherwise `None`.
    fn integer(&self) -> ParseResult<u32> {
        match self.fraction {
            None => Ok(self.base),
            _ => Err(INVALID),
        }
    }
}

/// Helper type for parsing fractional numbers.
///
/// The fractions is stored as an integer in the range 0..=10^15.
/// With this limit `10^15 * 3600` fits in an `u64` without overflow.
///
// We don't use `f64` to support targets that may not have floating point support.
#[derive(Copy, Clone)]
struct Fraction(u64);

impl Fraction {
    /// Supported formats are `,fraction` and `.fraction`.
    /// `fraction` can have an unlimited length. We only keep the first 15 digits, and look at the
    /// 16th digit for correct rounding.
    fn parse(mut s: &str) -> ParseResult<(&str, Self)> {
        s = match s.as_bytes().first() {
            Some(&b',' | &b'.') => &s[1..],
            _ => return Err(INVALID),
        };
        let digits_in_fraction = s.as_bytes().iter().take_while(|c| c.is_ascii_digit()).count();
        let mut fraction = scan::number(s, 1, 15).map(|(_, f)| f)? as u64;
        if digits_in_fraction <= 15 {
            fraction *= POW10[15 - digits_in_fraction];
        } else if s.as_bytes()[15] >= b'5' {
            fraction += 1;
        }
        s = &s[digits_in_fraction..];
        Ok((s, Fraction(fraction)))
    }

    /// Returns the result of multiplying this `Fraction` with `unit`.
    ///
    /// Rounds to the nearest integer.
    fn mul(&self, unit: u64) -> i64 {
        assert!(unit <= 3600); // assumption to prevent overflow later.
        ((self.0 * unit + POW10[15] / 2) / POW10[15]) as i64
    }

    /// Returns the result of multiplying this `Fraction` with `unit`.
    ///
    /// Returns two integers to represent the whole number and the fraction as nanos.
    fn mul_with_nanos(&self, unit: u64) -> (i64, i64) {
        assert!(unit <= 3600); // assumption to prevent overflow later.
        let div = POW10[15 - 9];
        let huge = self.0 * unit + div / 2;
        let whole = huge / POW10[15];
        let fraction_as_nanos = (huge % POW10[15]) / div;
        dbg!(whole as i64, fraction_as_nanos as i64)
    }
}

const POW10: [u64; 16] = [
    1, // unused, for easy indexing
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
    10_000_000_000,
    100_000_000_000,
    1_000_000_000_000,
    10_000_000_000_000,
    100_000_000_000_000,
    1_000_000_000_000_000,
];

#[cfg(test)]
mod tests {
    use super::{parse_iso8601_duration, parse_iso8601_duration_time, Fraction};
    use crate::format::{INVALID, OUT_OF_RANGE};
    use crate::CalendarDuration;

    #[test]
    fn test_parse_fraction() {
        let (_, fraction) = Fraction::parse(",123").unwrap();
        assert_eq!(fraction.0, 123_000_000_000_000);
        let (_, fraction) = Fraction::parse(",123456789012345").unwrap();
        assert_eq!(fraction.0, 123_456_789_012_345);
        let (_, fraction) = Fraction::parse(",1234567890123454").unwrap();
        assert_eq!(fraction.0, 123_456_789_012_345);
        let (_, fraction) = Fraction::parse(",1234567890123455").unwrap();
        assert_eq!(fraction.0, 123_456_789_012_346);

        let (_, fraction) = Fraction::parse(",5").unwrap();
        assert_eq!(fraction.mul_with_nanos(1), (0, 500_000_000));
    }

    #[test]
    fn test_parse_duration_time() {
        assert_eq!(parse_iso8601_duration_time("T12H"), Ok(("", (12, 0, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T12.25H"), Ok(("", (0, 735, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T12,25H"), Ok(("", (0, 735, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T34M"), Ok(("", (0, 34, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T34.25M"), Ok(("", (0, 34, 15, 0))));
        assert_eq!(parse_iso8601_duration_time("T56S"), Ok(("", (0, 0, 56, 0))));
        assert_eq!(parse_iso8601_duration_time("T0.789S"), Ok(("", (0, 0, 0, 789_000_000))));
        assert_eq!(parse_iso8601_duration_time("T0,789S"), Ok(("", (0, 0, 0, 789_000_000))));
        assert_eq!(parse_iso8601_duration_time("T12H34M"), Ok(("", (12, 34, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T12H34M56S"), Ok(("", (12, 34, 56, 0))));
        assert_eq!(
            parse_iso8601_duration_time("T12H34M56.789S"),
            Ok(("", (12, 34, 56, 789_000_000)))
        );
        assert_eq!(parse_iso8601_duration_time("T12H56S"), Ok(("", (12, 0, 56, 0))));
        assert_eq!(parse_iso8601_duration_time("T34M56S"), Ok(("", (0, 34, 56, 0))));

        // Data after a fraction is ignored
        assert_eq!(parse_iso8601_duration_time("T12.5H16M"), Ok(("16M", (0, 750, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T12H16.5M30S"), Ok(("30S", (12, 16, 30, 0))));

        // Zero values
        assert_eq!(parse_iso8601_duration_time("T0H"), Ok(("", (0, 0, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T0M"), Ok(("", (0, 0, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T0S"), Ok(("", (0, 0, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T0,0S"), Ok(("", (0, 0, 0, 0))));

        // Empty or invalid values
        assert_eq!(parse_iso8601_duration_time("TH"), Err(INVALID));
        assert_eq!(parse_iso8601_duration_time("TM"), Err(INVALID));
        assert_eq!(parse_iso8601_duration_time("TS"), Err(INVALID));
        assert_eq!(parse_iso8601_duration_time("T.5S"), Err(INVALID));
        assert_eq!(parse_iso8601_duration_time("T,5S"), Err(INVALID));

        // Date components
        assert_eq!(parse_iso8601_duration_time("T5W"), Err(INVALID));
        assert_eq!(parse_iso8601_duration_time("T5Y"), Err(INVALID));
        assert_eq!(parse_iso8601_duration_time("T5D"), Err(INVALID));

        // Max values
        assert_eq!(parse_iso8601_duration_time("T71582788H"), Ok(("", (u32::MAX / 60, 0, 0, 0))));
        // assert_eq!(parse_iso8601_duration_time("T71582789H"), Err(OUT_OF_RANGE)); // up to the caller
        assert_eq!(parse_iso8601_duration_time("T71582788.25H"), Ok(("", (0, u32::MAX, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T71582788.5H"), Err(OUT_OF_RANGE));
        assert_eq!(parse_iso8601_duration_time("T4294967295M"), Ok(("", (0, u32::MAX, 0, 0))));
        assert_eq!(parse_iso8601_duration_time("T4294967296M"), Err(OUT_OF_RANGE));
        assert_eq!(parse_iso8601_duration_time("T4294967295.25M"), Ok(("", (0, u32::MAX, 15, 0))));
        assert_eq!(
            parse_iso8601_duration_time("T4294967295.99999999999M"),
            Ok(("", (0, u32::MAX, 59, 999_999_999)))
        );
        assert_eq!(parse_iso8601_duration_time("T4294967295.999999999999M"), Err(OUT_OF_RANGE));
        assert_eq!(parse_iso8601_duration_time("T4294967295S"), Ok(("", (0, 0, u32::MAX, 0))));
        assert_eq!(parse_iso8601_duration_time("T4294967296S"), Err(OUT_OF_RANGE));
        assert_eq!(
            parse_iso8601_duration_time("T4294967295.25S"),
            Ok(("", (0, 0, u32::MAX, 250_000_000)))
        );
        assert_eq!(
            parse_iso8601_duration_time("T4294967295.999999999S"),
            Ok(("", (0, 0, u32::MAX, 999_999_999)))
        );
        assert_eq!(parse_iso8601_duration_time("T4294967295.9999999995S"), Err(OUT_OF_RANGE));
    }

    #[test]
    fn test_parse_duration() {
        assert_eq!(
            parse_iso8601_duration("P12Y"),
            Ok(("", CalendarDuration::new().with_years_and_months(12, 0).unwrap()))
        );
        assert_eq!(
            parse_iso8601_duration("P34M"),
            Ok(("", CalendarDuration::new().with_months(34)))
        );
        assert_eq!(parse_iso8601_duration("P56D"), Ok(("", CalendarDuration::new().with_days(56))));
        assert_eq!(
            parse_iso8601_duration("P78W"),
            Ok(("", CalendarDuration::new().with_weeks_and_days(78, 0).unwrap()))
        );

        // Fractional date values
        assert_eq!(
            parse_iso8601_duration("P1.25Y"),
            Ok(("", CalendarDuration::new().with_years_and_months(1, 3).unwrap()))
        );
        assert_eq!(
            parse_iso8601_duration("P1.99Y"),
            Ok(("", CalendarDuration::new().with_years_and_months(2, 0).unwrap()))
        );
        assert_eq!(
            parse_iso8601_duration("P1.4W"),
            Ok(("", CalendarDuration::new().with_days(10)))
        );
        assert_eq!(
            parse_iso8601_duration("P1.95W"),
            Ok(("", CalendarDuration::new().with_days(14)))
        );
        assert_eq!(parse_iso8601_duration("P1.5M"), Err(INVALID));
        assert_eq!(parse_iso8601_duration("P1.5D"), Err(INVALID));

        // Data after a fraction is ignored
        assert_eq!(
            parse_iso8601_duration("P1.25Y5D"),
            Ok(("5D", CalendarDuration::new().with_years_and_months(1, 3).unwrap()))
        );
        assert_eq!(
            parse_iso8601_duration("P1.25YT3H"),
            Ok(("T3H", CalendarDuration::new().with_years_and_months(1, 3).unwrap()))
        );

        // Zero values
        assert_eq!(parse_iso8601_duration("P0Y"), Ok(("", CalendarDuration::new())));
        assert_eq!(parse_iso8601_duration("P0M"), Ok(("", CalendarDuration::new())));
        assert_eq!(parse_iso8601_duration("P0W"), Ok(("", CalendarDuration::new())));
        assert_eq!(parse_iso8601_duration("P0D"), Ok(("", CalendarDuration::new())));
        assert_eq!(parse_iso8601_duration("PT0M"), Ok(("", CalendarDuration::new())));
        assert_eq!(parse_iso8601_duration("PT0S"), Ok(("", CalendarDuration::new())));

        assert_eq!(
            parse_iso8601_duration("P12W34D"),
            Ok(("34D", CalendarDuration::new().with_weeks_and_days(12, 0).unwrap()))
        );
        assert_eq!(parse_iso8601_duration("P12Y12Y"), Err(INVALID)); // TODO
        assert_eq!(parse_iso8601_duration("P12M12M"), Err(INVALID)); // TODO
        assert_eq!(
            parse_iso8601_duration("P12D12D"),
            Ok(("12D", CalendarDuration::new().with_days(12)))
        );
        assert_eq!(parse_iso8601_duration("P12M12Y"), Err(INVALID)); // TODO
        assert_eq!(
            parse_iso8601_duration("P12D12Y"),
            Ok(("12Y", CalendarDuration::new().with_days(12)))
        );
    }
}
