use super::parse::set_weekday_with_number_from_monday;
use super::scan;
use super::{ParseResult, Parsed, INVALID, OUT_OF_RANGE, TOO_SHORT};
use crate::{CalendarDuration, DateTime, Days, FixedOffset, NaiveDateTime};

#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) enum Iso8601Format {
    Basic,
    Extended,
    Unknown,
}

/// TODO
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

/// Returns `(DateTime<FixedOffset>, remainder)`.
pub(crate) fn parse_iso8601(s: &str) -> ParseResult<(DateTime<FixedOffset>, &str)> {
    let (dt, s, format) = parse_iso8601_datetime(s)?;

    let (s, offset) = if format == Iso8601Format::Extended {
        scan::timezone_offset(s, |s| scan::char(s, b':'), true, true, true)?
    } else {
        scan::timezone_offset(s, |s| Ok(s), true, true, true)?
    };
    let offset = FixedOffset::east_opt(offset).ok_or(OUT_OF_RANGE)?;

    dt.and_local_timezone(offset).single().ok_or(OUT_OF_RANGE).map(|dt| (dt, s))
}

/// Returns `(NaiveDateTime, remainder, Iso8601Format)`.
/// - This method returns a `NaiveDateTime` instead of working with `Parsed` because `Parsed` can't
///   handle a time of `24:00:00` (which should parse to `00:00:00` the next day).
/// - The ISO 8601 format of the date and time is returned so the calling function can check it
///   matches the format of a offset component (basic or extended format).
pub(crate) fn parse_iso8601_datetime(s: &str) -> ParseResult<(NaiveDateTime, &str, Iso8601Format)> {
    let mut parsed = Parsed::new();

    let (s, date_format) = parse_iso8601_date(&mut parsed, s)?;
    let s = scan::char(s, b'T')?;
    let (s, time_format, hour24) = parse_iso8601_time(&mut parsed, s)?;
    if time_format != Iso8601Format::Unknown && date_format != time_format {
        return Err(INVALID);
    }

    let mut dt = parsed.to_naive_datetime_with_offset(0)?;
    if hour24 {
        dt = dt.checked_add_days(Days::new(1)).ok_or(OUT_OF_RANGE)?;
    }
    Ok((dt, s, time_format))
}

/// The ISO 8601 date format is a combination of 12 different date formats:
///
/// |                                           | calendar date | ordinal date |  week date   |
/// |-------------------------------------------|---------------|--------------|--------------|
/// | basic format                              | YYYYMMDD      | YYYYDDD      | YYYYWwwD     |
/// | extended format                           | YYYY-MM-DD    | YYYY-DDD     | YYYY-Www-D   |
/// | basic format, expanded representations    | ±Y̲YYYYMMDD    | ±Y̲YYYYDDD    | ±Y̲YYYYWwwD   |
/// | extended format, expanded representations | ±Y̲YYYY-MM-DD  | ±Y̲YYYY-DDD   | ±Y̲YYYY-Www-D |
///
/// Returns `(remainder, Iso8601Format)`.
//// - The ISO 8601 format of the date is returned so the calling function can check it matches the
///   format of a time component (basic or extended format).
pub(crate) fn parse_iso8601_date<'a>(
    parsed: &mut Parsed,
    mut s: &'a str,
) -> ParseResult<(&'a str, Iso8601Format)> {
    macro_rules! try_consume {
        ($e:expr) => {{
            let (s_, v) = $e?;
            s = s_;
            v
        }};
    }

    let year = try_consume!(parse_iso8601_year(s));

    let extended_format = s.as_bytes().first() == Some(&b'-');
    if extended_format {
        s = &s[1..];
    }

    if s.as_bytes().first() == Some(&b'W') {
        // Week date. Basic format: `WwwD`. Extended format: `Www-D`.
        parsed.set_isoyear(year)?;
        parsed.set_isoweek(try_consume!(scan::number(&s[1..], 2, 2)))?;
        if extended_format {
            s = scan::char(s, b'-')?;
        }
        set_weekday_with_number_from_monday(parsed, try_consume!(scan::number(s, 1, 1)))?;
    } else {
        parsed.set_year(year)?;
        let digits = s.as_bytes().iter().take_while(|c| c.is_ascii_digit()).count();
        if digits == 3 {
            // Week date. Format: `DDD`
            parsed.set_ordinal(try_consume!(scan::number(s, 3, 3)))?;
        } else {
            // Calendar date. Basic format: `MMDD`. Extended format: `MM-DD`.
            parsed.set_month(try_consume!(scan::number(s, 2, 2)))?;
            if extended_format {
                s = scan::char(s, b'-')?;
            }
            parsed.set_day(try_consume!(scan::number(s, 2, 2)))?;
        }
    }
    let format = if extended_format { Iso8601Format::Extended } else { Iso8601Format::Basic };
    Ok((s, format))
}

fn parse_iso8601_year(mut s: &str) -> ParseResult<(&str, i64)> {
    match s.as_bytes().first() {
        Some(sign) if sign == &b'-' || sign == &b'+' => {
            // expanded representation
            let negative = sign == &b'-';
            s = &s[1..];
            let mut digits = s.as_bytes().iter().take_while(|c| c.is_ascii_digit()).count();
            if let Some(&b'-' | &b'W') = s.as_bytes().get(digits) {
                // The date format is either an extended format with `-` as seperator between date
                // fields, or it is a week date in basic format. In both cases all counted digits
                // belong to the year.
                if digits < 4 {
                    return Err(TOO_SHORT);
                }
            } else if digits == 7 {
                digits -= 3; // must be the format ±YYYYDDD
            } else if digits > 7 {
                // The basic format with expanded representation of a calendar date (±Y̲YYYYMMDD)
                // and ordinal date (±Y̲YYYYDDD) are ambiguous. In this case we assume a calendar
                // date, where the last 4 digits are for the month and day.
                digits -= 4;
            } else {
                return Err(TOO_SHORT);
            }
            let (s, year) = scan::number(s, 4, digits)?;
            Ok((s, if negative { -year } else { year }))
        }
        Some(_) => scan::number(s, 4, 4),
        None => Err(TOO_SHORT),
    }
}

/// The ISO 8601 time format has a basic and an extended format, representations with reduced
/// accuracy, and representations with a decimal fraction:
///
/// |                                   | basic format | extended format |
/// |-----------------------------------|--------------|-----------------|
/// | complete representation           | hhmmss       | hh:mm:ss        |
/// | reduced accuracy: hour and minute | hhmm         | hh:mm           |
/// | reduced accuracy: hour            | hh           |                 |
/// | decimal fraction of the second    | hhmmss,ss̲    | hh:mm:ss,ss̲     |
/// | decimal fraction of the minute    | hhmm,mm̲      | hh:mm,mm̲        |
/// | decimal fraction of the hour      | hh,hh̲        | hh,hh̲           |
///
/// A decimal sign is either `,` or `.`; a `,` is preferred.  A decimal fraction must have at least
/// one digit. The standard puts no limit on the number of digits.
///
/// Midnight can be represented with both `00:00` (at the start of the day) and `24:00` (at the end
/// of the calendar day).
///
/// Returns `(remainder, Iso8601Format, hour24)`.
/// - The ISO 8601 format of the time is return so the calling function can check it matches the
///   format of a date component (basic or extended format). If there a representation with the
///   accuracy reduced to hours, the format is `Unknown`.
/// - `24:00` can't be encoded in `Parsed`, so we encode it as `00:00` and return a `bool` to
///   indicate the date should wrap to the next day.
pub(crate) fn parse_iso8601_time<'a>(
    parsed: &mut Parsed,
    mut s: &'a str,
) -> ParseResult<(&'a str, Iso8601Format, bool)> {
    use Iso8601Format::*;

    macro_rules! try_consume {
        ($e:expr) => {{
            let (s_, v) = $e?;
            s = s_;
            v
        }};
    }

    let mut format = Unknown;
    let mut hour;
    let mut minute = 0;
    let mut second = 0;
    let mut nanosecond = 0;
    fn set_time_fields(
        parsed: &mut Parsed,
        hour: i64,
        minute: i64,
        second: i64,
        nanosecond: i64,
    ) -> ParseResult<bool> {
        match hour < 24 {
            true => parsed.set_hour(hour)?,
            false => {
                if !(hour == 24 && minute == 0 && second == 0 && nanosecond == 0) {
                    return Err(INVALID);
                }
                parsed.set_hour(0)?;
            }
        }
        parsed.set_minute(minute)?;
        parsed.set_second(second)?;
        parsed.set_nanosecond(nanosecond)?;
        Ok(hour == 24)
    }

    hour = try_consume!(scan::number(s, 2, 2));

    if let Ok((s_, fraction)) = Fraction::parse(s) {
        s = s_;
        // Minute, second and nanosecond are expressed as a fraction of an hour.
        let (sec, nanos) = fraction.mul_with_nanos(3600);
        minute = sec / 60;
        second = sec % 60;
        nanosecond = nanos;
        return Ok((s, format, set_time_fields(parsed, hour, minute, second, nanosecond)?));
    }

    let c = s.as_bytes().first().unwrap_or(&b'a');
    if !(c.is_ascii_digit() || c == &b':') {
        // Allow reduced accuracy
        return Ok((s, format, set_time_fields(parsed, hour, minute, second, nanosecond)?));
    }

    format = if s.as_bytes().first() == Some(&b':') { Extended } else { Basic };
    if format == Extended {
        s = &s[1..];
    }
    minute = try_consume!(scan::number(s, 2, 2));

    if let Ok((s_, fraction)) = Fraction::parse(s) {
        s = s_;
        // Second and nanosecond are expressed as a fraction of a minute.
        let (sec, nanos) = fraction.mul_with_nanos(60);
        second = sec;
        nanosecond = nanos;
        if sec == 60 {
            second = 0;
            minute += 1;
            if minute == 60 {
                minute = 0;
                hour += 1;
            }
        }
        return Ok((s, format, set_time_fields(parsed, hour, minute, second, nanosecond)?));
    }

    let c = s.as_bytes().first().unwrap_or(&b'a');
    if !(c.is_ascii_digit() || (format == Extended && c == &b':')) {
        // Allow reduced accuracy
        return Ok((s, format, set_time_fields(parsed, hour, minute, second, nanosecond)?));
    }

    if format == Extended {
        s = scan::char(s, b':')?;
    }
    second = try_consume!(scan::number(s, 2, 2));

    if let Ok((s_, fraction)) = Fraction::parse(s) {
        s = s_;
        // Nanosecond are expressed as a fraction of a minute.
        let (sec_from_rounding, nanos) = fraction.mul_with_nanos(1);
        nanosecond = nanos;
        if sec_from_rounding != 0 {
            if second < 59 {
                second += 1;
            } else {
                second = 0;
                minute += 1;
                if minute == 60 {
                    minute = 0;
                    hour += 1;
                }
            }
        }
    }
    Ok((s, format, set_time_fields(parsed, hour, minute, second, nanosecond)?))
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
    use super::*;
    use crate::format::INVALID;
    use crate::NaiveDate;

    #[test]
    fn test_parse_iso8601_date() {
        use crate::Weekday::Fri;
        fn parse(s: &str) -> ParseResult<(NaiveDate, &str)> {
            let mut parsed = Parsed::new();
            let (s, _) = parse_iso8601_date(&mut parsed, s)?;
            parsed.to_naive_date().map(|d| (d, s))
        }

        // calendar date, basic format
        assert_eq!(parse("20230609 "), Ok((NaiveDate::from_ymd_opt(2023, 6, 9).unwrap(), " ")));
        // calendar date, extended format
        assert_eq!(parse("2023-06-09 "), Ok((NaiveDate::from_ymd_opt(2023, 6, 9).unwrap(), " ")));
        // calendar date, basic format, expanded representation
        assert_eq!(parse("-20230609 "), Ok((NaiveDate::from_ymd_opt(-2023, 6, 9).unwrap(), " ")));
        assert_eq!(parse("+20230609 "), Ok((NaiveDate::from_ymd_opt(2023, 6, 9).unwrap(), " ")));
        assert_eq!(parse("+020230609 "), Ok((NaiveDate::from_ymd_opt(2023, 6, 9).unwrap(), " ")));
        assert_eq!(parse("+120230609 "), Ok((NaiveDate::from_ymd_opt(12023, 6, 9).unwrap(), " ")));
        // calendar date, extended format, expanded representation
        assert_eq!(parse("-2023-06-09 "), Ok((NaiveDate::from_ymd_opt(-2023, 6, 9).unwrap(), " ")));
        assert_eq!(parse("+2023-06-09 "), Ok((NaiveDate::from_ymd_opt(2023, 6, 9).unwrap(), " ")));
        assert_eq!(parse("+02023-06-09 "), Ok((NaiveDate::from_ymd_opt(2023, 6, 9).unwrap(), " ")));
        assert_eq!(parse("+12023-06-09"), Ok((NaiveDate::from_ymd_opt(12023, 6, 9).unwrap(), "")));
        // mixed basic and extended format
        assert_eq!(parse("2023-0609 "), Err(INVALID));
        assert_eq!(parse("202306-09 "), Err(INVALID));
        assert_eq!(parse("-2023-0609 "), Err(INVALID));
        // No padding
        assert_eq!(parse("2023-6-09 "), Err(INVALID));
        assert_eq!(parse("2023-06-9 "), Err(INVALID));
        assert_eq!(parse("23-06-09 "), Err(INVALID));

        // ordinal date, basic format
        assert_eq!(parse("2023160 "), Ok((NaiveDate::from_yo_opt(2023, 160).unwrap(), " ")));
        // ordinal date, extended format
        assert_eq!(parse("2023-160 "), Ok((NaiveDate::from_yo_opt(2023, 160).unwrap(), " ")));
        // ordinal date, basic format, expanded representation
        assert_eq!(parse("-2023160 "), Ok((NaiveDate::from_yo_opt(-2023, 160).unwrap(), " ")));
        assert_eq!(parse("+2023160 "), Ok((NaiveDate::from_yo_opt(2023, 160).unwrap(), " ")));
        // ordinal date, extended format, expanded representation
        assert_eq!(parse("-2023-160 "), Ok((NaiveDate::from_yo_opt(-2023, 160).unwrap(), " ")));
        assert_eq!(parse("+2023-160 "), Ok((NaiveDate::from_yo_opt(2023, 160).unwrap(), " ")));
        assert_eq!(parse("+02023-160 "), Ok((NaiveDate::from_yo_opt(2023, 160).unwrap(), " ")));
        assert_eq!(parse("+12023-160 "), Ok((NaiveDate::from_yo_opt(12023, 160).unwrap(), " ")));
        // ambiguous, interpreted as calendar date
        assert!(parse("+02023160 ").is_err());
        assert!(parse("+12023160 ").is_err());
        // No padding
        assert_eq!(parse("2023-16 "), Err(INVALID));
        assert_eq!(parse("2023-1 "), Err(INVALID));
        assert_eq!(parse("23-160 "), Err(INVALID));

        let from_isoywd_opt = NaiveDate::from_isoywd_opt;
        // week date, basic format
        assert_eq!(parse("2023W235 "), Ok((from_isoywd_opt(2023, 23, Fri).unwrap(), " ")));
        // week date, extended format
        assert_eq!(parse("2023-W23-5 "), Ok((from_isoywd_opt(2023, 23, Fri).unwrap(), " ")));
        // week date, basic format, expanded representation
        assert_eq!(parse("-2023W235 "), Ok((from_isoywd_opt(-2023, 23, Fri).unwrap(), " ")));
        assert_eq!(parse("+2023W235 "), Ok((from_isoywd_opt(2023, 23, Fri).unwrap(), " ")));
        assert_eq!(parse("+02023W235 "), Ok((from_isoywd_opt(2023, 23, Fri).unwrap(), " ")));
        assert_eq!(parse("+12023W235 "), Ok((from_isoywd_opt(12023, 23, Fri).unwrap(), " ")));
        // calendar date, extended format, expanded representation
        assert_eq!(parse("-2023-W23-5 "), Ok((from_isoywd_opt(-2023, 23, Fri).unwrap(), " ")));
        assert_eq!(parse("+2023-W23-5 "), Ok((from_isoywd_opt(2023, 23, Fri).unwrap(), " ")));
        assert_eq!(parse("+02023-W23-5 "), Ok((from_isoywd_opt(2023, 23, Fri).unwrap(), " ")));
        assert_eq!(parse("+12023-W23-5 "), Ok((from_isoywd_opt(12023, 23, Fri).unwrap(), " ")));
        // mixed basic and extended format
        assert_eq!(parse("2023-W235 "), Err(INVALID));
        assert_eq!(parse("202306-W235 "), Err(INVALID));
        assert_eq!(parse("-2023-W235 "), Err(INVALID));
        // No padding
        assert_eq!(parse("2023-W25 "), Err(INVALID));
        assert_eq!(parse("23-W23-5 "), Err(INVALID));
        // Year is interpreted as `iso_year`
        assert_eq!(parse("2022-W52-7 "), Ok((NaiveDate::from_ymd_opt(2023, 1, 1).unwrap(), " ")));
    }

    #[test]
    fn test_parse_iso8601_time() {
        fn parse(s: &str) -> ParseResult<(&str, u32, u32, u32, u32, bool)> {
            let mut parsed = Parsed::new();
            let (s, _, hour24) = parse_iso8601_time(&mut parsed, s)?;
            Ok((
                s,
                12 * parsed.hour_div_12.unwrap() + parsed.hour_mod_12.unwrap(),
                parsed.minute.unwrap(),
                parsed.second.unwrap_or(0),
                parsed.nanosecond.unwrap_or(0),
                hour24,
            ))
        }

        // basic format, complete representation
        assert_eq!(parse("152830 "), Ok((" ", 15, 28, 30, 0, false)));
        // extended format, complete representation
        assert_eq!(parse("15:28:30 "), Ok((" ", 15, 28, 30, 0, false)));
        // basic format, fractional second
        assert_eq!(parse("152830,6 "), Ok((" ", 15, 28, 30, 600_000_000, false)));
        assert_eq!(parse("152830.60 "), Ok((" ", 15, 28, 30, 600_000_000, false)));
        assert_eq!(parse("152830.999999999 "), Ok((" ", 15, 28, 30, 999_999_999, false)));
        assert_eq!(parse("152830.9999999999 "), Ok((" ", 15, 28, 31, 0, false)));
        // extended format, fractional second
        assert_eq!(parse("15:28:30,6 "), Ok((" ", 15, 28, 30, 600_000_000, false)));
        assert_eq!(parse("15:28:30.60 "), Ok((" ", 15, 28, 30, 600_000_000, false)));
        // basic format, fractional minute
        assert_eq!(parse("1528,5 "), Ok((" ", 15, 28, 30, 0, false)));
        assert_eq!(parse("1528.51 "), Ok((" ", 15, 28, 30, 600_000_000, false)));
        // extended format, fractional minute
        assert_eq!(parse("15:28,5 "), Ok((" ", 15, 28, 30, 0, false)));
        assert_eq!(parse("15:28.51 "), Ok((" ", 15, 28, 30, 600_000_000, false)));
        assert_eq!(parse("15:59.999999999999 "), Ok((" ", 16, 0, 0, 0, false)));
        // extended format, fractional hour
        assert_eq!(parse("15,45 "), Ok((" ", 15, 27, 0, 0, false)));
        assert_eq!(parse("15.12345 "), Ok((" ", 15, 7, 24, 420_000_000, false)));
        assert_eq!(parse("15,999999999999 "), Ok((" ", 15, 59, 59, 999_999_996, false)));
        assert_eq!(parse("15,9999999999999 "), Ok((" ", 15, 60, 0, 0, false)));

        // 24:00:00 is allowed
        assert_eq!(parse("240000 "), Ok((" ", 0, 0, 0, 0, true)));
        assert_eq!(parse("24:00:00 "), Ok((" ", 0, 0, 0, 0, true)));
        assert_eq!(parse("24:00:00,0 "), Ok((" ", 0, 0, 0, 0, true)));
        // But no times beyond that
        assert_eq!(parse("24:30:00 "), Err(INVALID));
        assert_eq!(parse("24:00:30 "), Err(INVALID));
        assert_eq!(parse("24:00:00,5 "), Err(INVALID));
        assert_eq!(parse("24.99 "), Err(INVALID));
        assert_eq!(parse("24,9999999999999 "), Err(INVALID)); // rounds to 25:00:00

        // Reduced accuracy
        assert_eq!(parse("1528 "), Ok((" ", 15, 28, 0, 0, false)));
        assert_eq!(parse("15:28 "), Ok((" ", 15, 28, 0, 0, false)));
        assert_eq!(parse("15 "), Ok((" ", 15, 0, 0, 0, false)));
    }

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
        // FIXME: broken comparisons
        // assert_eq!(parse_iso8601_duration("PT0M"), Ok(("", CalendarDuration::new())));
        // assert_eq!(parse_iso8601_duration("PT0S"), Ok(("", CalendarDuration::new())));

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
