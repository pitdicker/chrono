use super::parse::set_weekday_with_number_from_monday;
use super::scan;
use super::{ParseResult, Parsed, TOO_SHORT};

#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) enum Iso8601Format {
    Basic,
    Extended,
    Unknown,
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
}
