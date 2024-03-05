// This is a part of Chrono.
// Portions copyright (c) 2015, John Nagle.
// See README.md and LICENSE.txt for details.

//! Date and time parsing routines.

use core::borrow::Borrow;
use core::str;
use core::usize;

use super::scan;
use super::{parse_error, ParseError};
use super::{Fixed, InternalFixed, InternalInternal, Item, Numeric, Pad, Parsed};
use crate::{DateTime, Error, FixedOffset, Weekday};

fn set_weekday_with_num_days_from_sunday(p: &mut Parsed, v: i64) -> Result<&mut Parsed, Error> {
    p.set_weekday(match v {
        0 => Weekday::Sun,
        1 => Weekday::Mon,
        2 => Weekday::Tue,
        3 => Weekday::Wed,
        4 => Weekday::Thu,
        5 => Weekday::Fri,
        6 => Weekday::Sat,
        _ => return Err(Error::InvalidArgument),
    })
}

fn set_weekday_with_number_from_monday(p: &mut Parsed, v: i64) -> Result<&mut Parsed, Error> {
    p.set_weekday(match v {
        1 => Weekday::Mon,
        2 => Weekday::Tue,
        3 => Weekday::Wed,
        4 => Weekday::Thu,
        5 => Weekday::Fri,
        6 => Weekday::Sat,
        7 => Weekday::Sun,
        _ => return Err(Error::InvalidArgument),
    })
}

fn consume_and_set<'s, 'p, V, F>(
    src: &'s str,
    result: Result<(&'s str, V), ParseError<'s>>,
    setter: F,
) -> Result<&'s str, ParseError<'s>>
where
    F: FnOnce(V) -> Result<&'p mut Parsed, Error> + 'p,
{
    let (s_, v) = result?;
    match setter(v) {
        Ok(_) => Ok(s_),
        Err(Error::Inconsistent) => Err(ParseError::Inconsistent),
        Err(Error::InvalidArgument) => Err(ParseError::InvalidValue(src)),
        //Err(Error::InvalidArgument) => ParseError::InvalidValue(src, (src.len() - s_.len()) as u8),
        _ => panic!("`Parsed::set_*` should only return `Inconsistent` or `InvalidArgument`"),
    }
}

/// Parse an RFC 2822 format datetime
/// e.g. `Fri, 21 Nov 1997 09:55:06 -0600`
///
/// This function allows arbitrary intermixed whitespace per RFC 2822 appendix A.5
fn parse_rfc2822<'a>(parsed: &mut Parsed, mut s: &'a str) -> Result<(&'a str, ()), ParseError<'a>> {
    // an adapted RFC 2822 syntax from Section 3.3 and 4.3:
    //
    // c-char      = <any char except '(', ')' and '\\'>
    // c-escape    = "\" <any char>
    // comment     = "(" *(comment / c-char / c-escape) ")" *S
    // date-time   = [ day-of-week "," ] date 1*S time *S *comment
    // day-of-week = *S day-name *S
    // day-name    = "Mon" / "Tue" / "Wed" / "Thu" / "Fri" / "Sat" / "Sun"
    // date        = day month year
    // day         = *S 1*2DIGIT *S
    // month       = 1*S month-name 1*S
    // month-name  = "Jan" / "Feb" / "Mar" / "Apr" / "May" / "Jun" /
    //               "Jul" / "Aug" / "Sep" / "Oct" / "Nov" / "Dec"
    // year        = *S 2*DIGIT *S
    // time        = time-of-day 1*S zone
    // time-of-day = hour ":" minute [ ":" second ]
    // hour        = *S 2DIGIT *S
    // minute      = *S 2DIGIT *S
    // second      = *S 2DIGIT *S
    // zone        = ( "+" / "-" ) 4DIGIT /
    //               "UT" / "GMT" /                  ; same as +0000
    //               "EST" / "CST" / "MST" / "PST" / ; same as -0500 to -0800
    //               "EDT" / "CDT" / "MDT" / "PDT" / ; same as -0400 to -0700
    //               1*(%d65-90 / %d97-122)          ; same as -0000
    //
    // some notes:
    //
    // - quoted characters can be in any mixture of lower and upper cases.
    //
    // - we do not recognize a folding white space (FWS) or comment (CFWS).
    //   for our purposes, instead, we accept any sequence of Unicode
    //   white space characters (denoted here to `S`). For comments, we accept
    //   any text within parentheses while respecting escaped parentheses.
    //   Any actual RFC 2822 parser is expected to parse FWS and/or CFWS themselves
    //   and replace it with a single SP (`%x20`); this is legitimate.
    //
    // - two-digit year < 50 should be interpreted by adding 2000.
    //   two-digit year >= 50 or three-digit year should be interpreted
    //   by adding 1900. note that four-or-more-digit years less than 1000
    //   are *never* affected by this rule.
    //
    // - mismatching day-of-week is always an error, which is consistent to
    //   Chrono's own rules.
    //
    // - zones can range from `-9959` to `+9959`, but `FixedOffset` does not
    //   support offsets larger than 24 hours. this is not *that* problematic
    //   since we do not directly go to a `DateTime` so one can recover
    //   the offset information from `Parsed` anyway.

    s = s.trim_start();

    if let Ok((s_, weekday)) = scan::short_weekday(s) {
        if !s_.starts_with(',') {
            return Err(ParseError::InvalidCharacter(s_));
        }
        s = &s_[1..];
        parsed.set_weekday(weekday).map_err(|e| parse_error(e, s))?;
    }

    s = s.trim_start();
    s = consume_and_set(s, scan::number(s, 1, 2, true), |d| parsed.set_day(d))?;
    s = scan::space(s)?; // mandatory
    s = consume_and_set(s, scan::short_month0(s), |m| parsed.set_month(1 + i64::from(m)))?;
    s = scan::space(s)?; // mandatory
    s = consume_and_set(s, parse_rfc2822_year(s), |y| parsed.set_year(y))?;

    s = scan::space(s)?; // mandatory
    s = consume_and_set(s, scan::number(s, 2, 2, true), |h| parsed.set_hour(h))?;
    s = scan::char(s.trim_start(), b':')?.trim_start(); // *S ":" *S
    s = consume_and_set(s, scan::number(s, 2, 2, true), |m| parsed.set_minute(m))?;
    if let Ok(s_) = scan::char(s.trim_start(), b':') {
        // [ ":" *S 2DIGIT ]
        s = consume_and_set(s_, scan::number(s_, 2, 2, true), |s| parsed.set_second(s))?;
    }

    s = scan::space(s)?; // mandatory
    s = consume_and_set(s, scan::timezone_offset_2822(s), |o| parsed.set_offset(i64::from(o)))?;

    // optional comments
    while let Ok((s_out, ())) = scan::comment_2822(s) {
        s = s_out;
    }

    Ok((s, ()))
}

fn parse_rfc2822_year(s: &str) -> Result<(&str, i64), ParseError> {
    // distinguish two- and three-digit years from four-digit years
    let (s_, year) = scan::number(s, 2, usize::MAX, true)?;
    let yearlen = s_.len() - s.len();
    let year = match (yearlen, year) {
        (2, 0..=49) => 2000 + year,  // 47 -> 2047, 05 -> 2005
        (2, 50..=99) => 1900 + year, // 79 -> 1979
        (3, _) => 1900 + year,       // 112 -> 2012, 009 -> 1909
        (_, _) => year,              // 1987 -> 1987, 0654 -> 0654
    };
    Ok((s_, year))
}

/// Parses an RFC 3339 date-and-time string into a `DateTime<FixedOffset>` value.
///
/// RFC 3339 syntax from Section 5.6:
///
/// ```text
/// date-fullyear  = 4DIGIT
/// date-month     = 2DIGIT ; 01-12
/// date-mday      = 2DIGIT ; 01-28, 01-29, 01-30, 01-31 based on month/year
/// time-hour      = 2DIGIT ; 00-23
/// time-minute    = 2DIGIT ; 00-59
/// time-second    = 2DIGIT ; 00-58, 00-59, 00-60 based on leap second rules
/// time-secfrac   = "." 1*DIGIT
/// time-numoffset = ("+" / "-") time-hour ":" time-minute
/// time-offset    = "Z" / time-numoffset
/// partial-time   = time-hour ":" time-minute ":" time-second [time-secfrac]
/// full-date      = date-fullyear "-" date-month "-" date-mday
/// full-time      = partial-time time-offset
/// date-time      = full-date "T" full-time
/// ```
///
/// - The "T" and "Z" characters in this syntax may alternatively be lower case "t" or "z".
/// - For readability a full-date and a full-time may be separated by a space character.
/// - Any number of fractional digits for seconds is allowed. We skip digits past first 9 digits.
pub(crate) fn parse_rfc3339(s: &str) -> Result<DateTime<FixedOffset>, Error> {
    let mut parsed = Parsed::new();
    let s = parse_rfc3339_inner(&mut parsed, s).map_err(|e| e.to_error(s))?;
    if !s.is_empty() {
        return Err(Error::TooLong);
    }
    parsed.to_datetime()
}

fn parse_rfc3339_inner<'a>(parsed: &mut Parsed, mut s: &'a str) -> Result<&'a str, ParseError<'a>> {
    macro_rules! try_consume {
        ($e:expr) => {{
            let (s_, v) = $e?;
            s = s_;
            v
        }};
    }

    s = consume_and_set(s, scan::number(s, 4, 4, true), |y| parsed.set_year(y))?;
    s = scan::char(s, b'-')?;
    s = consume_and_set(s, scan::number(s, 2, 2, true), |m| parsed.set_month(m))?;
    s = scan::char(s, b'-')?;
    s = consume_and_set(s, scan::number(s, 2, 2, true), |d| parsed.set_day(d))?;

    s = match s.as_bytes().first() {
        Some(&b't' | &b'T' | &b' ') => &s[1..],
        _ => return Err(ParseError::InvalidCharacter(s)),
    };

    s = consume_and_set(s, scan::number(s, 2, 2, true), |h| parsed.set_hour(h))?;
    s = scan::char(s, b':')?;
    s = consume_and_set(s, scan::number(s, 2, 2, true), |m| parsed.set_minute(m))?;
    s = scan::char(s, b':')?;
    s = consume_and_set(s, scan::number(s, 2, 2, true), |s| parsed.set_second(s))?;
    if s.starts_with('.') {
        s = consume_and_set(s, scan::nanosecond(&s[1..]), |ns| parsed.set_nanosecond(ns))?;
    }

    let offset = try_consume!(scan::timezone_offset(s, |s| scan::char(s, b':'), true, false, true));
    // This range check is similar to the one in `FixedOffset::east`, so it would be redundant.
    // But it is possible to read the offset directly from `Parsed`. We want to only successfully
    // populate `Parsed` if the input is fully valid RFC 3339.
    // Max for the hours field is `23`, and for the minutes field `59`.
    const MAX_RFC3339_OFFSET: i32 = (23 * 60 + 59) * 60;
    if !(-MAX_RFC3339_OFFSET..=MAX_RFC3339_OFFSET).contains(&offset) {
        return Err(ParseError::InvalidValue(s));
    }
    parsed.set_offset(i64::from(offset)).map_err(|e| parse_error(e, s))?;

    Ok(s)
}

/// Tries to parse given string into `parsed` with given formatting items.
/// Returns `Ok` when the entire string has been parsed (otherwise `parsed` should not be used).
/// There should be no trailing string after parsing;
/// use a stray [`Item::Space`](./enum.Item.html#variant.Space) to trim whitespaces.
///
/// This particular date and time parser is:
///
/// - Greedy. It will consume the longest possible prefix.
///   For example, `April` is always consumed entirely when the long month name is requested;
///   it equally accepts `Apr`, but prefers the longer prefix in this case.
///
/// - Padding-agnostic (for numeric items).
///   The [`Pad`](./enum.Pad.html) field is completely ignored,
///   so one can prepend any number of whitespace then any number of zeroes before numbers.
///
/// - (Still) obeying the intrinsic parsing width. This allows, for example, parsing `HHMMSS`.
pub fn parse<'a, I, B>(parsed: &mut Parsed, s: &str, items: I) -> Result<(), Error>
where
    I: Iterator<Item = B>,
    B: Borrow<Item<'a>>,
{
    match parse_internal(parsed, s, items) {
        Ok("") => Ok(()),
        Ok(_) => Err(Error::TooLong), // if there are trailing chars it is an error
        Err(e) => Err(e.to_error(s)),
    }
}

/// Tries to parse given string into `parsed` with given formatting items.
/// Returns `Ok` with a slice of the unparsed remainder.
///
/// This particular date and time parser is:
///
/// - Greedy. It will consume the longest possible prefix.
///   For example, `April` is always consumed entirely when the long month name is requested;
///   it equally accepts `Apr`, but prefers the longer prefix in this case.
///
/// - Padding-agnostic (for numeric items).
///   The [`Pad`](./enum.Pad.html) field is completely ignored,
///   so one can prepend any number of zeroes before numbers.
///
/// - (Still) obeying the intrinsic parsing width. This allows, for example, parsing `HHMMSS`.
pub fn parse_and_remainder<'a, 'b, I, B>(
    parsed: &mut Parsed,
    s: &'b str,
    items: I,
) -> Result<&'b str, Error>
where
    I: Iterator<Item = B>,
    B: Borrow<Item<'a>>,
{
    parse_internal(parsed, s, items).map_err(|e| e.to_error(s))
}

fn parse_internal<'a, 'b, I, B>(
    parsed: &mut Parsed,
    mut s: &'b str,
    items: I,
) -> Result<&'b str, ParseError<'b>>
where
    I: Iterator<Item = B>,
    B: Borrow<Item<'a>>,
{
    macro_rules! try_consume {
        ($e:expr) => {{
            match $e {
                Ok((s_, v)) => {
                    s = s_;
                    v
                }
                Err(e) => return Err(e),
            }
        }};
    }

    for item in items {
        match *item.borrow() {
            Item::Literal(prefix) => {
                if s.len() < prefix.len() {
                    return Err(ParseError::TooShort);
                }
                if !s.starts_with(prefix) {
                    return Err(ParseError::InvalidCharacter(s)); // FIXME: doesn't point at the offending character
                }
                s = &s[prefix.len()..];
            }

            #[cfg(feature = "alloc")]
            Item::OwnedLiteral(ref prefix) => {
                if s.len() < prefix.len() {
                    return Err(ParseError::TooShort);
                }
                if !s.starts_with(&prefix[..]) {
                    return Err(ParseError::InvalidCharacter(s)); // FIXME: doesn't point at the offending character
                }
                s = &s[prefix.len()..];
            }

            Item::Space(_) => {
                s = s.trim_start();
            }

            #[cfg(feature = "alloc")]
            Item::OwnedSpace(_) => {
                s = s.trim_start();
            }

            Item::Numeric(ref spec, ref _pad) => {
                use super::Numeric::*;
                type Setter = fn(&mut Parsed, i64) -> Result<&mut Parsed, Error>;

                let (width, signed, set): (usize, bool, Setter) = match *spec {
                    Year => (4, true, Parsed::set_year),
                    YearDiv100 => (2, false, Parsed::set_year_div_100),
                    YearMod100 => (2, false, Parsed::set_year_mod_100),
                    IsoYear => (4, true, Parsed::set_isoyear),
                    IsoYearDiv100 => (2, false, Parsed::set_isoyear_div_100),
                    IsoYearMod100 => (2, false, Parsed::set_isoyear_mod_100),
                    Month => (2, false, Parsed::set_month),
                    Day => (2, false, Parsed::set_day),
                    WeekFromSun => (2, false, Parsed::set_week_from_sun),
                    WeekFromMon => (2, false, Parsed::set_week_from_mon),
                    IsoWeek => (2, false, Parsed::set_isoweek),
                    NumDaysFromSun => (1, false, set_weekday_with_num_days_from_sunday),
                    WeekdayFromMon => (1, false, set_weekday_with_number_from_monday),
                    Ordinal => (3, false, Parsed::set_ordinal),
                    Hour => (2, false, Parsed::set_hour),
                    Hour12 => (2, false, Parsed::set_hour12),
                    Minute => (2, false, Parsed::set_minute),
                    Second => (2, false, Parsed::set_second),
                    Nanosecond => (9, false, Parsed::set_nanosecond),
                    Timestamp => (usize::MAX, true, Parsed::set_timestamp),

                    // for the future expansion
                    Internal(ref int) => match int._dummy {},
                };

                s = s.trim_start();
                let v = if signed {
                    if s.starts_with('-') {
                        try_consume!(scan::number(&s[1..], 1, usize::MAX, false))
                    } else if s.starts_with('+') {
                        try_consume!(scan::number(&s[1..], 1, usize::MAX, true))
                    } else {
                        // if there is no explicit sign, we respect the original `width`
                        try_consume!(scan::number(s, 1, width, true))
                    }
                } else {
                    try_consume!(scan::number(s, 1, width, true))
                };
                set(parsed, v).map_err(|e| parse_error(e, s))?;
            }

            Item::Fixed(ref spec) => {
                use super::Fixed::*;

                match spec {
                    &ShortMonthName => {
                        s = consume_and_set(s, scan::short_month0(s), |m| {
                            parsed.set_month(i64::from(m) + 1)
                        })?;
                    }

                    &LongMonthName => {
                        s = consume_and_set(s, scan::short_or_long_month0(s), |m| {
                            parsed.set_month(i64::from(m) + 1)
                        })?;
                    }

                    &ShortWeekdayName => {
                        s = consume_and_set(s, scan::short_weekday(s), |w| parsed.set_weekday(w))?;
                    }

                    &LongWeekdayName => {
                        s = consume_and_set(s, scan::short_or_long_weekday(s), |w| {
                            parsed.set_weekday(w)
                        })?;
                    }

                    &LowerAmPm | &UpperAmPm => {
                        if s.len() < 2 {
                            return Err(ParseError::TooShort);
                        }
                        let ampm = match (s.as_bytes()[0] | 32, s.as_bytes()[1] | 32) {
                            (b'a', b'm') => false,
                            (b'p', b'm') => true,
                            _ => return Err(ParseError::InvalidCharacter(s)),
                        };
                        parsed.set_ampm(ampm).map_err(|e| parse_error(e, s))?;
                        s = &s[2..];
                    }

                    &Nanosecond | &Nanosecond3 | &Nanosecond6 | &Nanosecond9 => {
                        if s.starts_with('.') {
                            s = consume_and_set(s, scan::nanosecond(&s[1..]), |ns| {
                                parsed.set_nanosecond(ns)
                            })?;
                        }
                    }

                    &Internal(InternalFixed { val: InternalInternal::Nanosecond3NoDot }) => {
                        s = consume_and_set(s, scan::nanosecond_fixed(s, 3), |ns| {
                            parsed.set_nanosecond(ns)
                        })?;
                    }

                    &Internal(InternalFixed { val: InternalInternal::Nanosecond6NoDot }) => {
                        s = consume_and_set(s, scan::nanosecond_fixed(s, 6), |ns| {
                            parsed.set_nanosecond(ns)
                        })?;
                    }

                    &Internal(InternalFixed { val: InternalInternal::Nanosecond9NoDot }) => {
                        s = consume_and_set(s, scan::nanosecond_fixed(s, 9), |ns| {
                            parsed.set_nanosecond(ns)
                        })?;
                    }

                    &TimezoneName => {
                        try_consume!(Ok((s.trim_start_matches(|c: char| !c.is_whitespace()), ())));
                    }

                    &TimezoneOffsetColon
                    | &TimezoneOffsetDoubleColon
                    | &TimezoneOffsetTripleColon
                    | &TimezoneOffset => {
                        let offset = try_consume!(scan::timezone_offset(
                            s.trim_start(),
                            scan::consume_colon_maybe,
                            false,
                            false,
                            true,
                        ));
                        parsed.set_offset(i64::from(offset)).map_err(|e| parse_error(e, s))?;
                    }

                    &TimezoneOffsetColonZ | &TimezoneOffsetZ => {
                        let offset = try_consume!(scan::timezone_offset(
                            s.trim_start(),
                            scan::consume_colon_maybe,
                            true,
                            false,
                            true,
                        ));
                        parsed.set_offset(i64::from(offset)).map_err(|e| parse_error(e, s))?;
                    }
                    &Internal(InternalFixed {
                        val: InternalInternal::TimezoneOffsetPermissive,
                    }) => {
                        let offset = try_consume!(scan::timezone_offset(
                            s.trim_start(),
                            scan::consume_colon_maybe,
                            true,
                            true,
                            true,
                        ));
                        parsed.set_offset(i64::from(offset)).map_err(|e| parse_error(e, s))?;
                    }

                    &RFC2822 => try_consume!(parse_rfc2822(parsed, s)),
                    &RFC3339 => {
                        // Used for the `%+` specifier, which has the description:
                        // "Same as `%Y-%m-%dT%H:%M:%S%.f%:z` (...)
                        // This format also supports having a `Z` or `UTC` in place of `%:z`."
                        // Use the relaxed parser to match this description.
                        try_consume!(parse_rfc3339_relaxed(parsed, s))
                    }
                }
            }

            Item::Error => {
                return Err(ParseError::UnsupportedSpecifier);
            }
        }
    }
    Ok(s)
}

/// Accepts a relaxed form of RFC3339.
///
/// Differences with RFC3339:
/// - Values don't require padding to two digits.
/// - Years outside the range 0...=9999 are accepted, but they must include a sign.
/// - `UTC` is accepted as a valid timezone name/offset (for compatibility with the debug format of
///   `DateTime<Utc>`.
/// - There can be spaces between any of the components.
/// - The colon in the offset may be missing.
fn parse_rfc3339_relaxed<'a>(
    parsed: &mut Parsed,
    mut s: &'a str,
) -> Result<(&'a str, ()), ParseError<'a>> {
    const DATE_ITEMS: &[Item<'static>] = &[
        Item::Numeric(Numeric::Year, Pad::Zero),
        Item::Space(""),
        Item::Literal("-"),
        Item::Numeric(Numeric::Month, Pad::Zero),
        Item::Space(""),
        Item::Literal("-"),
        Item::Numeric(Numeric::Day, Pad::Zero),
    ];
    const TIME_ITEMS: &[Item<'static>] = &[
        Item::Numeric(Numeric::Hour, Pad::Zero),
        Item::Space(""),
        Item::Literal(":"),
        Item::Numeric(Numeric::Minute, Pad::Zero),
        Item::Space(""),
        Item::Literal(":"),
        Item::Numeric(Numeric::Second, Pad::Zero),
        Item::Fixed(Fixed::Nanosecond),
        Item::Space(""),
    ];

    s = parse_internal(parsed, s, DATE_ITEMS.iter())?;

    s = match s.as_bytes().first() {
        Some(&b't' | &b'T' | &b' ') => &s[1..],
        Some(_) => return Err(ParseError::InvalidCharacter(s)),
        None => return Err(ParseError::TooShort),
    };

    s = parse_internal(parsed, s, TIME_ITEMS.iter())?;
    s = s.trim_start();
    let (s, offset) = if s.len() >= 3 && "UTC".as_bytes().eq_ignore_ascii_case(&s.as_bytes()[..3]) {
        (&s[3..], 0)
    } else {
        scan::timezone_offset(s, scan::consume_colon_maybe, true, false, true)?
    };
    parsed.set_offset(i64::from(offset)).map_err(|e| parse_error(e, s))?;
    Ok((s, ()))
}

#[cfg(test)]
mod tests {
    use crate::format::*;
    use crate::{DateTime, FixedOffset, NaiveDateTime, TimeZone, Timelike, Utc};

    const TOO_LONG: Error = Error::TooLong;

    #[test]
    fn test_parse_whitespace_and_literal() {
        use crate::format::Item::{Literal, Space};

        // empty string
        parses("", &[]);
        check(" ", &[], Err(TOO_LONG));
        check("a", &[], Err(TOO_LONG));
        check("abc", &[], Err(TOO_LONG));
        check("🤠", &[], Err(TOO_LONG));

        // whitespaces
        parses("", &[Space("")]);
        parses(" ", &[Space(" ")]);
        parses("  ", &[Space("  ")]);
        parses("   ", &[Space("   ")]);
        parses(" ", &[Space("")]);
        parses("  ", &[Space(" ")]);
        parses("   ", &[Space("  ")]);
        parses("    ", &[Space("  ")]);
        parses("", &[Space(" ")]);
        parses(" ", &[Space("  ")]);
        parses("  ", &[Space("   ")]);
        parses("  ", &[Space("  "), Space("  ")]);
        parses("   ", &[Space("  "), Space("  ")]);
        parses("  ", &[Space(" "), Space(" ")]);
        parses("   ", &[Space("  "), Space(" ")]);
        parses("   ", &[Space(" "), Space("  ")]);
        parses("   ", &[Space(" "), Space(" "), Space(" ")]);
        parses("\t", &[Space("")]);
        parses(" \n\r  \n", &[Space("")]);
        parses("\t", &[Space("\t")]);
        parses("\t", &[Space(" ")]);
        parses(" ", &[Space("\t")]);
        parses("\t\r", &[Space("\t\r")]);
        parses("\t\r ", &[Space("\t\r ")]);
        parses("\t \r", &[Space("\t \r")]);
        parses(" \t\r", &[Space(" \t\r")]);
        parses(" \n\r  \n", &[Space(" \n\r  \n")]);
        parses(" \t\n", &[Space(" \t")]);
        parses(" \n\t", &[Space(" \t\n")]);
        parses("\u{2002}", &[Space("\u{2002}")]);
        // most unicode whitespace characters
        parses(
            "\u{00A0}\u{1680}\u{2000}\u{2001}\u{2002}\u{2003}\u{2004}\u{2005}\u{2006}\u{2007}\u{2008}\u{2009}\u{3000}",
            &[Space("\u{00A0}\u{1680}\u{2000}\u{2001}\u{2002}\u{2003}\u{2004}\u{2005}\u{2006}\u{2007}\u{2008}\u{2009}\u{3000}")]
        );
        // most unicode whitespace characters
        parses(
            "\u{00A0}\u{1680}\u{2000}\u{2001}\u{2002}\u{2003}\u{2004}\u{2005}\u{2006}\u{2007}\u{2008}\u{2009}\u{3000}",
            &[
                Space("\u{00A0}\u{1680}\u{2000}\u{2001}\u{2002}\u{2003}\u{2004}"),
                Space("\u{2005}\u{2006}\u{2007}\u{2008}\u{2009}\u{3000}")
            ]
        );
        check("a", &[Space("")], Err(TOO_LONG));
        check("a", &[Space(" ")], Err(TOO_LONG));
        // a Space containing a literal does not match a literal
        check("a", &[Space("a")], Err(TOO_LONG));
        check("abc", &[Space("")], Err(TOO_LONG));
        check("abc", &[Space(" ")], Err(TOO_LONG));
        check(" abc", &[Space("")], Err(TOO_LONG));
        check(" abc", &[Space(" ")], Err(TOO_LONG));

        // `\u{0363}` is combining diacritic mark "COMBINING LATIN SMALL LETTER A"

        // literal
        parses("", &[Literal("")]);
        check("", &[Literal("a")], Err(Error::InvalidCharacter(0)));
        check(" ", &[Literal("a")], Err(Error::InvalidCharacter(0)));
        parses("a", &[Literal("a")]);
        parses("+", &[Literal("+")]);
        parses("-", &[Literal("-")]);
        parses("−", &[Literal("−")]); // MINUS SIGN (U+2212)
        parses(" ", &[Literal(" ")]); // a Literal may contain whitespace and match whitespace
        check("aa", &[Literal("a")], Err(TOO_LONG));
        check("🤠", &[Literal("a")], Err(Error::InvalidCharacter(0)));
        check("A", &[Literal("a")], Err(Error::InvalidCharacter(0)));
        check("a", &[Literal("z")], Err(Error::InvalidCharacter(0)));
        check("a", &[Literal("🤠")], Err(Error::InvalidCharacter(0)));
        check("a", &[Literal("\u{0363}a")], Err(Error::InvalidCharacter(0)));
        check("\u{0363}a", &[Literal("a")], Err(Error::InvalidCharacter(0)));
        parses("\u{0363}a", &[Literal("\u{0363}a")]);
        check("a", &[Literal("ab")], Err(Error::InvalidCharacter(0)));
        parses("xy", &[Literal("xy")]);
        parses("xy", &[Literal("x"), Literal("y")]);
        parses("1", &[Literal("1")]);
        parses("1234", &[Literal("1234")]);
        parses("+1234", &[Literal("+1234")]);
        parses("-1234", &[Literal("-1234")]);
        parses("−1234", &[Literal("−1234")]); // MINUS SIGN (U+2212)
        parses("PST", &[Literal("PST")]);
        parses("🤠", &[Literal("🤠")]);
        parses("🤠a", &[Literal("🤠"), Literal("a")]);
        parses("🤠a🤠", &[Literal("🤠"), Literal("a🤠")]);
        parses("a🤠b", &[Literal("a"), Literal("🤠"), Literal("b")]);
        // literals can be together
        parses("xy", &[Literal("xy")]);
        parses("xyz", &[Literal("xyz")]);
        // or literals can be apart
        parses("xy", &[Literal("x"), Literal("y")]);
        parses("xyz", &[Literal("x"), Literal("yz")]);
        parses("xyz", &[Literal("xy"), Literal("z")]);
        parses("xyz", &[Literal("x"), Literal("y"), Literal("z")]);
        //
        check("x y", &[Literal("x"), Literal("y")], Err(Error::InvalidCharacter(1)));
        parses("xy", &[Literal("x"), Space(""), Literal("y")]);
        parses("x y", &[Literal("x"), Space(""), Literal("y")]);
        parses("x y", &[Literal("x"), Space(" "), Literal("y")]);

        // whitespaces + literals
        parses("a\n", &[Literal("a"), Space("\n")]);
        parses("\tab\n", &[Space("\t"), Literal("ab"), Space("\n")]);
        parses(
            "ab\tcd\ne",
            &[Literal("ab"), Space("\t"), Literal("cd"), Space("\n"), Literal("e")],
        );
        parses(
            "+1ab\tcd\r\n+,.",
            &[Literal("+1ab"), Space("\t"), Literal("cd"), Space("\r\n"), Literal("+,.")],
        );
        // whitespace and literals can be intermixed
        parses("a\tb", &[Literal("a\tb")]);
        parses("a\tb", &[Literal("a"), Space("\t"), Literal("b")]);
    }

    #[test]
    fn test_parse_numeric() -> Result<(), Error> {
        use crate::format::Item::{Literal, Space};
        use crate::format::Numeric::*;

        let p = Parsed::new;

        // numeric
        check("1987", &[num(Year)], p().set_year(1987));
        check("1987 ", &[num(Year)], Err(TOO_LONG));
        check("0x12", &[num(Year)], Err(TOO_LONG)); // `0` is parsed
        check("x123", &[num(Year)], Err(Error::InvalidCharacter(0)));
        check("o123", &[num(Year)], Err(Error::InvalidCharacter(0)));
        check("2015", &[num(Year)], p().set_year(2015));
        check("0000", &[num(Year)], p().set_year(0));
        check("9999", &[num(Year)], p().set_year(9999));
        check(" \t987", &[num(Year)], p().set_year(987));
        check(" \t987", &[Space(" \t"), num(Year)], p().set_year(987));
        check(" \t987🤠", &[Space(" \t"), num(Year), Literal("🤠")], p().set_year(987));
        check("987🤠", &[num(Year), Literal("🤠")], p().set_year(987));
        check("5", &[num(Year)], p().set_year(5));
        check("5\0", &[num(Year)], Err(TOO_LONG));
        check("\x005", &[num(Year)], Err(Error::InvalidCharacter(0)));
        check("", &[num(Year)], Err(Error::InvalidCharacter(0)));
        check("12345", &[num(Year), Literal("5")], p().set_year(1234));
        check("12345", &[nums(Year), Literal("5")], p().set_year(1234));
        check("12345", &[num0(Year), Literal("5")], p().set_year(1234));
        check("12341234", &[num(Year), num(Year)], p().set_year(1234));
        check("1234 1234", &[num(Year), num(Year)], p().set_year(1234));
        check("1234 1234", &[num(Year), Space(" "), num(Year)], p().set_year(1234));
        check("1234 1235", &[num(Year), num(Year)], Err(Error::Inconsistent));
        check("1234 1234", &[num(Year), Literal("x"), num(Year)], Err(Error::InvalidCharacter(4)));
        check("1234x1234", &[num(Year), Literal("x"), num(Year)], p().set_year(1234));
        check(
            "1234 x 1234",
            &[num(Year), Literal("x"), num(Year)],
            Err(Error::InvalidCharacter(4)),
        );
        check("1234xx1234", &[num(Year), Literal("x"), num(Year)], Err(Error::InvalidCharacter(5)));
        check("1234xx1234", &[num(Year), Literal("xx"), num(Year)], p().set_year(1234));
        check(
            "1234 x 1234",
            &[num(Year), Space(" "), Literal("x"), Space(" "), num(Year)],
            p().set_year(1234),
        );
        check(
            "1234 x 1235",
            &[num(Year), Space(" "), Literal("x"), Space(" "), Literal("1235")],
            p().set_year(1234),
        );

        // signed numeric
        check("-42", &[num(Year)], p().set_year(-42));
        check("+42", &[num(Year)], p().set_year(42));
        check("-0042", &[num(Year)], p().set_year(-42));
        check("+0042", &[num(Year)], p().set_year(42));
        check("-42195", &[num(Year)], p().set_year(-42195));
        check("−42195", &[num(Year)], Err(Error::InvalidCharacter(0))); // MINUS SIGN (U+2212)
        check("+42195", &[num(Year)], p().set_year(42195));
        check("  -42195", &[num(Year)], p().set_year(-42195));
        check(" +42195", &[num(Year)], p().set_year(42195));
        check("  -42195", &[num(Year)], p().set_year(-42195));
        check("  +42195", &[num(Year)], p().set_year(42195));
        check("-42195 ", &[num(Year)], Err(TOO_LONG));
        check("+42195 ", &[num(Year)], Err(TOO_LONG));
        check("  -   42", &[num(Year)], Err(Error::InvalidCharacter(3)));
        check("  +   42", &[num(Year)], Err(Error::InvalidCharacter(3)));
        check("  -42195", &[Space("  "), num(Year)], p().set_year(-42195));
        check("  −42195", &[Space("  "), num(Year)], Err(Error::InvalidCharacter(2))); // MINUS SIGN (U+2212)
        check("  +42195", &[Space("  "), num(Year)], p().set_year(42195));
        check("  -   42", &[Space("  "), num(Year)], Err(Error::InvalidCharacter(3)));
        check("  +   42", &[Space("  "), num(Year)], Err(Error::InvalidCharacter(3)));
        check("-", &[num(Year)], Err(Error::InvalidCharacter(0)));
        check("+", &[num(Year)], Err(Error::InvalidCharacter(0)));
        check("-9223372036854775808", &[num(Timestamp)], p().set_timestamp(i64::MIN));

        // unsigned numeric
        check("345", &[num(Ordinal)], p().set_ordinal(345));
        check("+345", &[num(Ordinal)], Err(Error::InvalidCharacter(0)));
        check("-345", &[num(Ordinal)], Err(Error::InvalidCharacter(0)));
        check(" 345", &[num(Ordinal)], p().set_ordinal(345));
        check("−345", &[num(Ordinal)], Err(Error::InvalidCharacter(0))); // MINUS SIGN (U+2212)
        check("345 ", &[num(Ordinal)], Err(TOO_LONG));
        check(" 345", &[Space(" "), num(Ordinal)], p().set_ordinal(345));
        check("345 ", &[num(Ordinal), Space(" ")], p().set_ordinal(345));
        check("345🤠 ", &[num(Ordinal), Literal("🤠"), Space(" ")], p().set_ordinal(345));
        check("345🤠", &[num(Ordinal)], Err(TOO_LONG));
        check("\u{0363}345", &[num(Ordinal)], Err(Error::InvalidCharacter(0)));
        check(" +345", &[num(Ordinal)], Err(Error::InvalidCharacter(1)));
        check(" -345", &[num(Ordinal)], Err(Error::InvalidCharacter(1)));
        check("\t345", &[Space("\t"), num(Ordinal)], p().set_ordinal(345));
        check(" +345", &[Space(" "), num(Ordinal)], Err(Error::InvalidCharacter(1)));
        check(" -345", &[Space(" "), num(Ordinal)], Err(Error::InvalidCharacter(1)));

        // various numeric fields
        check("1234 5678", &[num(Year), num(IsoYear)], p().set_year(1234)?.set_isoyear(5678));
        check(
            "12 34 56 78",
            &[num(YearDiv100), num(YearMod100), num(IsoYearDiv100), num(IsoYearMod100)],
            p().set_year_div_100(12)?
                .set_year_mod_100(34)?
                .set_isoyear_div_100(56)?
                .set_isoyear_mod_100(78),
        );
        check(
            "1 2 3 45",
            &[num(Month), num(Day), num(WeekFromSun), num(NumDaysFromSun), num(IsoWeek)],
            p().set_month(1)?
                .set_day(2)?
                .set_week_from_sun(3)?
                .set_weekday(Weekday::Thu)?
                .set_isoweek(5),
        );
        check(
            "6 7 89 01",
            &[num(WeekFromMon), num(WeekdayFromMon), num(Ordinal), num(Hour12)],
            p().set_week_from_mon(6)?.set_weekday(Weekday::Sun)?.set_ordinal(89)?.set_hour12(1),
        );
        check(
            "23 45 6 78901234 567890123",
            &[num(Hour), num(Minute), num(Second), num(Nanosecond), num(Timestamp)],
            p().set_ampm(true)?
                .set_hour12(11)?
                .set_minute(45)?
                .set_second(6)?
                .set_nanosecond(78_901_234)?
                .set_timestamp(567_890_123),
        );

        Ok(())
    }

    #[test]
    fn test_parse_fixed() -> Result<(), Error> {
        use crate::format::Fixed::*;
        use crate::format::Item::{Literal, Space};

        let p = Parsed::new;

        // fixed: month and weekday names
        check("apr", &[fixed(ShortMonthName)], p().set_month(4));
        check("Apr", &[fixed(ShortMonthName)], p().set_month(4));
        check("APR", &[fixed(ShortMonthName)], p().set_month(4));
        check("ApR", &[fixed(ShortMonthName)], p().set_month(4));
        check("\u{0363}APR", &[fixed(ShortMonthName)], Err(Error::InvalidCharacter(0)));
        check("April", &[fixed(ShortMonthName)], Err(TOO_LONG)); // `Apr` is parsed
        check("A", &[fixed(ShortMonthName)], Err(Error::InvalidCharacter(0)));
        check("Sol", &[fixed(ShortMonthName)], Err(Error::InvalidCharacter(0)));
        check("Apr", &[fixed(LongMonthName)], p().set_month(4));
        check("Apri", &[fixed(LongMonthName)], Err(TOO_LONG)); // `Apr` is parsed
        check("April", &[fixed(LongMonthName)], p().set_month(4));
        check("Aprill", &[fixed(LongMonthName)], Err(TOO_LONG));
        check("Aprill", &[fixed(LongMonthName), Literal("l")], p().set_month(4));
        check("Aprl", &[fixed(LongMonthName), Literal("l")], p().set_month(4));
        check("April", &[fixed(LongMonthName), Literal("il")], Err(Error::InvalidCharacter(0))); // do not backtrack
        check("thu", &[fixed(ShortWeekdayName)], p().set_weekday(Weekday::Thu));
        check("Thu", &[fixed(ShortWeekdayName)], p().set_weekday(Weekday::Thu));
        check("THU", &[fixed(ShortWeekdayName)], p().set_weekday(Weekday::Thu));
        check("tHu", &[fixed(ShortWeekdayName)], p().set_weekday(Weekday::Thu));
        check("Thursday", &[fixed(ShortWeekdayName)], Err(TOO_LONG)); // `Thu` is parsed
        check("T", &[fixed(ShortWeekdayName)], Err(Error::InvalidCharacter(0)));
        check("The", &[fixed(ShortWeekdayName)], Err(Error::InvalidCharacter(0)));
        check("Nop", &[fixed(ShortWeekdayName)], Err(Error::InvalidCharacter(0)));
        check("Thu", &[fixed(LongWeekdayName)], p().set_weekday(Weekday::Thu));
        check("Thur", &[fixed(LongWeekdayName)], Err(TOO_LONG)); // `Thu` is parsed
        check("Thurs", &[fixed(LongWeekdayName)], Err(TOO_LONG)); // `Thu` is parsed
        check("Thursday", &[fixed(LongWeekdayName)], p().set_weekday(Weekday::Thu));
        check("Thursdays", &[fixed(LongWeekdayName)], Err(TOO_LONG));
        check("Thursdays", &[fixed(LongWeekdayName), Literal("s")], p().set_weekday(Weekday::Thu));
        check("Thus", &[fixed(LongWeekdayName), Literal("s")], p().set_weekday(Weekday::Thu));
        check(
            "Thursday",
            &[fixed(LongWeekdayName), Literal("rsday")],
            Err(Error::InvalidCharacter(0)),
        ); // do not backtrack

        // fixed: am/pm
        check("am", &[fixed(LowerAmPm)], p().set_ampm(false));
        check("pm", &[fixed(LowerAmPm)], p().set_ampm(true));
        check("AM", &[fixed(LowerAmPm)], p().set_ampm(false));
        check("PM", &[fixed(LowerAmPm)], p().set_ampm(true));
        check("am", &[fixed(UpperAmPm)], p().set_ampm(false));
        check("pm", &[fixed(UpperAmPm)], p().set_ampm(true));
        check("AM", &[fixed(UpperAmPm)], p().set_ampm(false));
        check("PM", &[fixed(UpperAmPm)], p().set_ampm(true));
        check("Am", &[fixed(LowerAmPm)], p().set_ampm(false));
        check(" Am", &[Space(" "), fixed(LowerAmPm)], p().set_ampm(false));
        check("Am🤠", &[fixed(LowerAmPm), Literal("🤠")], p().set_ampm(false));
        check("🤠Am", &[Literal("🤠"), fixed(LowerAmPm)], p().set_ampm(false));
        check("\u{0363}am", &[fixed(LowerAmPm)], Err(Error::InvalidCharacter(0)));
        check("\u{0360}am", &[fixed(LowerAmPm)], Err(Error::InvalidCharacter(0)));
        check(" Am", &[fixed(LowerAmPm)], Err(Error::InvalidCharacter(0)));
        check("Am ", &[fixed(LowerAmPm)], Err(TOO_LONG));
        check("a.m.", &[fixed(LowerAmPm)], Err(Error::InvalidCharacter(0)));
        check("A.M.", &[fixed(LowerAmPm)], Err(Error::InvalidCharacter(0)));
        check("ame", &[fixed(LowerAmPm)], Err(Error::TooLong)); // `am` is parsed
        check("a", &[fixed(LowerAmPm)], Err(Error::InvalidCharacter(0)));
        check("p", &[fixed(LowerAmPm)], Err(Error::InvalidCharacter(0)));
        check("x", &[fixed(LowerAmPm)], Err(Error::InvalidCharacter(0)));
        check("xx", &[fixed(LowerAmPm)], Err(Error::InvalidCharacter(0)));
        check("", &[fixed(LowerAmPm)], Err(Error::InvalidCharacter(0)));

        Ok(())
    }

    #[test]
    fn test_parse_fixed_nanosecond() -> Result<(), Error> {
        use crate::format::Fixed::Nanosecond;
        use crate::format::InternalInternal::*;
        use crate::format::Item::Literal;
        use crate::format::Numeric::Second;

        let p = Parsed::new;

        // fixed: dot plus nanoseconds
        check("", &[fixed(Nanosecond)], Ok(&mut p())); // no field set, but not an error
        check(".", &[fixed(Nanosecond)], Err(Error::InvalidCharacter(0)));
        check("4", &[fixed(Nanosecond)], Err(TOO_LONG)); // never consumes `4`
        check("4", &[fixed(Nanosecond), num(Second)], p().set_second(4));
        check(".0", &[fixed(Nanosecond)], p().set_nanosecond(0));
        check(".4", &[fixed(Nanosecond)], p().set_nanosecond(400_000_000));
        check(".42", &[fixed(Nanosecond)], p().set_nanosecond(420_000_000));
        check(".421", &[fixed(Nanosecond)], p().set_nanosecond(421_000_000));
        check(".42195", &[fixed(Nanosecond)], p().set_nanosecond(421_950_000));
        check(".421951", &[fixed(Nanosecond)], p().set_nanosecond(421_951_000));
        check(".4219512", &[fixed(Nanosecond)], p().set_nanosecond(421_951_200));
        check(".42195123", &[fixed(Nanosecond)], p().set_nanosecond(421_951_230));
        check(".421950803", &[fixed(Nanosecond)], p().set_nanosecond(421_950_803));
        check(".4219508035", &[fixed(Nanosecond)], p().set_nanosecond(421_950_803));
        check(".42195080354", &[fixed(Nanosecond)], p().set_nanosecond(421_950_803));
        check(".421950803547", &[fixed(Nanosecond)], p().set_nanosecond(421_950_803));
        check(".000000003", &[fixed(Nanosecond)], p().set_nanosecond(3));
        check(".0000000031", &[fixed(Nanosecond)], p().set_nanosecond(3));
        check(".0000000035", &[fixed(Nanosecond)], p().set_nanosecond(3));
        check(".000000003547", &[fixed(Nanosecond)], p().set_nanosecond(3));
        check(".0000000009", &[fixed(Nanosecond)], p().set_nanosecond(0));
        check(".000000000547", &[fixed(Nanosecond)], p().set_nanosecond(0));
        check(".0000000009999999999999999999999999", &[fixed(Nanosecond)], p().set_nanosecond(0));
        check(".4🤠", &[fixed(Nanosecond), Literal("🤠")], p().set_nanosecond(400_000_000));
        check(".4x", &[fixed(Nanosecond)], Err(TOO_LONG));
        check(".  4", &[fixed(Nanosecond)], Err(Error::InvalidCharacter(0)));
        check("  .4", &[fixed(Nanosecond)], Err(TOO_LONG)); // no automatic trimming

        // fixed: nanoseconds without the dot
        check("", &[internal_fixed(Nanosecond3NoDot)], Err(Error::InvalidCharacter(0)));
        check(".", &[internal_fixed(Nanosecond3NoDot)], Err(Error::InvalidCharacter(0)));
        check("0", &[internal_fixed(Nanosecond3NoDot)], Err(Error::InvalidCharacter(0)));
        check("4", &[internal_fixed(Nanosecond3NoDot)], Err(Error::InvalidCharacter(0)));
        check("42", &[internal_fixed(Nanosecond3NoDot)], Err(Error::InvalidCharacter(0)));
        check("421", &[internal_fixed(Nanosecond3NoDot)], p().set_nanosecond(421_000_000));
        check("4210", &[internal_fixed(Nanosecond3NoDot)], Err(TOO_LONG));
        check(
            "42143",
            &[internal_fixed(Nanosecond3NoDot), num(Second)],
            p().set_nanosecond(421_000_000)?.set_second(43),
        );
        check(
            "421🤠",
            &[internal_fixed(Nanosecond3NoDot), Literal("🤠")],
            p().set_nanosecond(421_000_000),
        );
        check(
            "🤠421",
            &[Literal("🤠"), internal_fixed(Nanosecond3NoDot)],
            p().set_nanosecond(421_000_000),
        );
        check("42195", &[internal_fixed(Nanosecond3NoDot)], Err(TOO_LONG));
        check("123456789", &[internal_fixed(Nanosecond3NoDot)], Err(TOO_LONG));
        check("4x", &[internal_fixed(Nanosecond3NoDot)], Err(Error::InvalidCharacter(0)));
        check("  4", &[internal_fixed(Nanosecond3NoDot)], Err(Error::InvalidCharacter(0)));
        check(".421", &[internal_fixed(Nanosecond3NoDot)], Err(Error::InvalidCharacter(0)));

        check("", &[internal_fixed(Nanosecond6NoDot)], Err(Error::InvalidCharacter(0)));
        check(".", &[internal_fixed(Nanosecond6NoDot)], Err(Error::InvalidCharacter(0)));
        check("0", &[internal_fixed(Nanosecond6NoDot)], Err(Error::InvalidCharacter(0)));
        check("1234", &[internal_fixed(Nanosecond6NoDot)], Err(Error::InvalidCharacter(0)));
        check("12345", &[internal_fixed(Nanosecond6NoDot)], Err(Error::InvalidCharacter(0)));
        check("421950", &[internal_fixed(Nanosecond6NoDot)], p().set_nanosecond(421_950_000));
        check("000003", &[internal_fixed(Nanosecond6NoDot)], p().set_nanosecond(3000));
        check("000000", &[internal_fixed(Nanosecond6NoDot)], p().set_nanosecond(0));
        check("1234567", &[internal_fixed(Nanosecond6NoDot)], Err(TOO_LONG));
        check("123456789", &[internal_fixed(Nanosecond6NoDot)], Err(TOO_LONG));
        check("4x", &[internal_fixed(Nanosecond6NoDot)], Err(Error::InvalidCharacter(0)));
        check("     4", &[internal_fixed(Nanosecond6NoDot)], Err(Error::InvalidCharacter(0)));
        check(".42100", &[internal_fixed(Nanosecond6NoDot)], Err(Error::InvalidCharacter(0)));

        check("", &[internal_fixed(Nanosecond9NoDot)], Err(Error::InvalidCharacter(0)));
        check(".", &[internal_fixed(Nanosecond9NoDot)], Err(Error::InvalidCharacter(0)));
        check("42195", &[internal_fixed(Nanosecond9NoDot)], Err(Error::InvalidCharacter(0)));
        check("12345678", &[internal_fixed(Nanosecond9NoDot)], Err(Error::InvalidCharacter(0)));
        check("421950803", &[internal_fixed(Nanosecond9NoDot)], p().set_nanosecond(421_950_803));
        check("000000003", &[internal_fixed(Nanosecond9NoDot)], p().set_nanosecond(3));
        check(
            "42195080354",
            &[internal_fixed(Nanosecond9NoDot), num(Second)],
            p().set_nanosecond(421_950_803)?.set_second(54),
        ); // don't skip digits that come after the 9
        check("1234567890", &[internal_fixed(Nanosecond9NoDot)], Err(TOO_LONG));
        check("000000000", &[internal_fixed(Nanosecond9NoDot)], p().set_nanosecond(0));
        check("00000000x", &[internal_fixed(Nanosecond9NoDot)], Err(Error::InvalidCharacter(0)));
        check("        4", &[internal_fixed(Nanosecond9NoDot)], Err(Error::InvalidCharacter(0)));
        check(".42100000", &[internal_fixed(Nanosecond9NoDot)], Err(Error::InvalidCharacter(0)));

        Ok(())
    }

    #[test]
    fn test_parse_fixed_timezone_offset() -> Result<(), Error> {
        use crate::format::Fixed::*;
        use crate::format::InternalInternal::*;
        use crate::format::Item::Literal;

        let p = Parsed::new;

        // TimezoneOffset
        check("1", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("12", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("123", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("1234", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("12345", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("123456", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("1234567", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+1", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+123", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+1234", &[fixed(TimezoneOffset)], p().set_offset(45_240));
        check("+12345", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+123456", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+1234567", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+12345678", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+12:", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12:3", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12:34", &[fixed(TimezoneOffset)], p().set_offset(45_240));
        check("-12:34", &[fixed(TimezoneOffset)], p().set_offset(-45_240));
        check("−12:34", &[fixed(TimezoneOffset)], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("+12:34:", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+12:34:5", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+12:34:56", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+12:34:56:", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+12 34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12  34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("12:34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("12:34:56", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12::34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12: :34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12:::34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12::::34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12::34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12:34:56", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+12:3456", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+1234:56", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+1234:567", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+00:00", &[fixed(TimezoneOffset)], p().set_offset(0));
        check("-00:00", &[fixed(TimezoneOffset)], p().set_offset(0));
        check("−00:00", &[fixed(TimezoneOffset)], p().set_offset(0)); // MINUS SIGN (U+2212)
        check("+00:01", &[fixed(TimezoneOffset)], p().set_offset(60));
        check("-00:01", &[fixed(TimezoneOffset)], p().set_offset(-60));
        check("+00:30", &[fixed(TimezoneOffset)], p().set_offset(1800));
        check("-00:30", &[fixed(TimezoneOffset)], p().set_offset(-1800));
        check("+24:00", &[fixed(TimezoneOffset)], p().set_offset(86_400));
        check("-24:00", &[fixed(TimezoneOffset)], p().set_offset(-86_400));
        check("−24:00", &[fixed(TimezoneOffset)], p().set_offset(-86_400)); // MINUS SIGN (U+2212)
        check("+99:59", &[fixed(TimezoneOffset)], p().set_offset(359_940));
        check("-99:59", &[fixed(TimezoneOffset)], p().set_offset(-359_940));
        check("+00:60", &[fixed(TimezoneOffset)], Err(Error::InvalidValue(0)));
        check("+00:99", &[fixed(TimezoneOffset)], Err(Error::InvalidValue(0)));
        check("#12:34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12:34 ", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+12 34 ", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check(" +12:34", &[fixed(TimezoneOffset)], p().set_offset(45_240));
        check(" -12:34", &[fixed(TimezoneOffset)], p().set_offset(-45_240));
        check(" −12:34", &[fixed(TimezoneOffset)], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("  +12:34", &[fixed(TimezoneOffset)], p().set_offset(45_240));
        check("  -12:34", &[fixed(TimezoneOffset)], p().set_offset(-45_240));
        check("\t -12:34", &[fixed(TimezoneOffset)], p().set_offset(-45_240));
        check("-12: 34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("-12 :34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("-12 : 34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("-12 :  34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("-12  : 34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("-12:  34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("-12  :34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("-12  :  34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("12:34 ", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check(" 12:34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check(
            "+12345",
            &[fixed(TimezoneOffset), num(Numeric::Day)],
            p().set_offset(45_240)?.set_day(5),
        );
        check(
            "+12:345",
            &[fixed(TimezoneOffset), num(Numeric::Day)],
            p().set_offset(45_240)?.set_day(5),
        );
        check("+12:34:", &[fixed(TimezoneOffset), Literal(":")], p().set_offset(45_240));
        check("Z12:34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("X12:34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("Z+12:34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("X+12:34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("X−12:34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0))); // MINUS SIGN (U+2212)
        check("🤠+12:34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+12:34🤠", &[fixed(TimezoneOffset)], Err(TOO_LONG));
        check("+12:🤠34", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+1234🤠", &[fixed(TimezoneOffset), Literal("🤠")], p().set_offset(45_240));
        check("-1234🤠", &[fixed(TimezoneOffset), Literal("🤠")], p().set_offset(-45_240));
        check("−1234🤠", &[fixed(TimezoneOffset), Literal("🤠")], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("+12:34🤠", &[fixed(TimezoneOffset), Literal("🤠")], p().set_offset(45_240));
        check("-12:34🤠", &[fixed(TimezoneOffset), Literal("🤠")], p().set_offset(-45_240));
        check("−12:34🤠", &[fixed(TimezoneOffset), Literal("🤠")], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("🤠+12:34", &[Literal("🤠"), fixed(TimezoneOffset)], p().set_offset(45_240));
        check("Z", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("A", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("PST", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("#Z", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check(":Z", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+Z", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+:Z", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("+Z:", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check("z", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check(" :Z", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check(" Z", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));
        check(" z", &[fixed(TimezoneOffset)], Err(Error::InvalidCharacter(0)));

        // TimezoneOffsetColon
        check("1", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("12", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("123", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("1234", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("12345", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("123456", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("1234567", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("12345678", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+1", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+123", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+1234", &[fixed(TimezoneOffsetColon)], p().set_offset(45_240));
        check("-1234", &[fixed(TimezoneOffsetColon)], p().set_offset(-45_240));
        check("−1234", &[fixed(TimezoneOffsetColon)], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("+12345", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("+123456", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("+1234567", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("+12345678", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("1:", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("12:", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("12:3", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("12:34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("12:34:", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("12:34:5", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("12:34:56", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+1:", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12:", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12:3", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12:34", &[fixed(TimezoneOffsetColon)], p().set_offset(45_240));
        check("-12:34", &[fixed(TimezoneOffsetColon)], p().set_offset(-45_240));
        check("−12:34", &[fixed(TimezoneOffsetColon)], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("+12:34:", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("+12:34:5", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("+12:34:56", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("+12:34:56:", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("+12:34:56:7", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("+12:34:56:78", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("+12:3456", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("+1234:56", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check("−12:34", &[fixed(TimezoneOffsetColon)], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("−12 : 34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0))); // MINUS SIGN (U+2212)
        check("+12 :34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12: 34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12 34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12: 34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12 :34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12 : 34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("-12 : 34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12  : 34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12 :  34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12  :  34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12::34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12: :34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12:::34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12::::34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12::34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("#1234", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("#12:34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+12:34 ", &[fixed(TimezoneOffsetColon)], Err(TOO_LONG));
        check(" +12:34", &[fixed(TimezoneOffsetColon)], p().set_offset(45_240));
        check("\t+12:34", &[fixed(TimezoneOffsetColon)], p().set_offset(45_240));
        check("\t\t+12:34", &[fixed(TimezoneOffsetColon)], p().set_offset(45_240));
        check("12:34 ", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check(" 12:34", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check(":", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check(
            "+12345",
            &[fixed(TimezoneOffsetColon), num(Numeric::Day)],
            p().set_offset(45_240)?.set_day(5),
        );
        check(
            "+12:345",
            &[fixed(TimezoneOffsetColon), num(Numeric::Day)],
            p().set_offset(45_240)?.set_day(5),
        );
        check("+12:34:", &[fixed(TimezoneOffsetColon), Literal(":")], p().set_offset(45_240));
        check("Z", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("A", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("PST", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("#Z", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check(":Z", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+Z", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+:Z", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("+Z:", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check("z", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check(" :Z", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check(" Z", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        check(" z", &[fixed(TimezoneOffsetColon)], Err(Error::InvalidCharacter(0)));
        // testing `TimezoneOffsetColon` also tests same path as `TimezoneOffsetDoubleColon`
        // and `TimezoneOffsetTripleColon` for function `parse_internal`.
        // No need for separate tests for `TimezoneOffsetDoubleColon` and
        // `TimezoneOffsetTripleColon`.

        // TimezoneOffsetZ
        check("1", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("12", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("123", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("1234", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("12345", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("123456", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("1234567", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("12345678", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+1", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+123", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+1234", &[fixed(TimezoneOffsetZ)], p().set_offset(45_240));
        check("-1234", &[fixed(TimezoneOffsetZ)], p().set_offset(-45_240));
        check("−1234", &[fixed(TimezoneOffsetZ)], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("+12345", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+123456", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+1234567", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+12345678", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("1:", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("12:", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("12:3", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("12:34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("12:34:", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("12:34:5", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("12:34:56", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+1:", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12:", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12:3", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12:34", &[fixed(TimezoneOffsetZ)], p().set_offset(45_240));
        check("-12:34", &[fixed(TimezoneOffsetZ)], p().set_offset(-45_240));
        check("−12:34", &[fixed(TimezoneOffsetZ)], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("+12:34:", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+12:34:5", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+12:34:56", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+12:34:56:", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+12:34:56:7", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+12:34:56:78", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+12::34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12:3456", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+1234:56", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+12 34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12  34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12: 34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12 :34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12 : 34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12  : 34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12 :  34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12  :  34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("12:34 ", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check(" 12:34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+12:34 ", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("+12 34 ", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check(" +12:34", &[fixed(TimezoneOffsetZ)], p().set_offset(45_240));
        check(
            "+12345",
            &[fixed(TimezoneOffsetZ), num(Numeric::Day)],
            p().set_offset(45_240)?.set_day(5),
        );
        check(
            "+12:345",
            &[fixed(TimezoneOffsetZ), num(Numeric::Day)],
            p().set_offset(45_240)?.set_day(5),
        );
        check("+12:34:", &[fixed(TimezoneOffsetZ), Literal(":")], p().set_offset(45_240));
        check("Z12:34", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("X12:34", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("Z", &[fixed(TimezoneOffsetZ)], p().set_offset(0));
        check("z", &[fixed(TimezoneOffsetZ)], p().set_offset(0));
        check(" Z", &[fixed(TimezoneOffsetZ)], p().set_offset(0));
        check(" z", &[fixed(TimezoneOffsetZ)], p().set_offset(0));
        check("\u{0363}Z", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("Z ", &[fixed(TimezoneOffsetZ)], Err(TOO_LONG));
        check("A", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("PST", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("#Z", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check(":Z", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check(":z", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+Z", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("-Z", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+A", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+🙃", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+Z:", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check(" :Z", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check(" +Z", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check(" -Z", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("+:Z", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("Y", &[fixed(TimezoneOffsetZ)], Err(Error::InvalidCharacter(0)));
        check("Zulu", &[fixed(TimezoneOffsetZ), Literal("ulu")], p().set_offset(0));
        check("zulu", &[fixed(TimezoneOffsetZ), Literal("ulu")], p().set_offset(0));
        check("+1234ulu", &[fixed(TimezoneOffsetZ), Literal("ulu")], p().set_offset(45_240));
        check("+12:34ulu", &[fixed(TimezoneOffsetZ), Literal("ulu")], p().set_offset(45_240));
        // Testing `TimezoneOffsetZ` also tests same path as `TimezoneOffsetColonZ`
        // in function `parse_internal`.
        // No need for separate tests for `TimezoneOffsetColonZ`.

        // TimezoneOffsetPermissive
        check("1", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("12", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("123", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("1234", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("12345", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("123456", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("1234567", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("12345678", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+1", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+12", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(43_200));
        check("+123", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+1234", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(45_240));
        check("-1234", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(-45_240));
        check("−1234", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("+12345", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+123456", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+1234567", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12345678", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("1:", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("12:", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("12:3", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("12:34", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("12:34:", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("12:34:5", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("12:34:56", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+1:", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+12:", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(43_200));
        check("+12:3", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:34", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(45_240));
        check("-12:34", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(-45_240));
        check("−12:34", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check("+12:34:", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:34:5", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:34:56", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:34:56:", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:34:56:7", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:34:56:78", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12 34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12  34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12 :34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12: 34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12 : 34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12  :34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:  34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12  :  34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12::34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12 ::34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12: :34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:: 34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12  ::34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:  :34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12::  34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:::34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12::::34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("12:34 ", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check(" 12:34", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+12:34 ", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check(" +12:34", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(45_240));
        check(" -12:34", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(-45_240));
        check(" −12:34", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(-45_240)); // MINUS SIGN (U+2212)
        check(
            "+12345",
            &[internal_fixed(TimezoneOffsetPermissive), num(Numeric::Day)],
            p().set_offset(45_240)?.set_day(5),
        );
        check(
            "+12:345",
            &[internal_fixed(TimezoneOffsetPermissive), num(Numeric::Day)],
            p().set_offset(45_240)?.set_day(5),
        );
        check(
            "+12:34:",
            &[internal_fixed(TimezoneOffsetPermissive), Literal(":")],
            p().set_offset(45_240),
        );
        check("🤠+12:34", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+12:34🤠", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("+12:🤠34", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check(
            "+12:34🤠",
            &[internal_fixed(TimezoneOffsetPermissive), Literal("🤠")],
            p().set_offset(45_240),
        );
        check(
            "🤠+12:34",
            &[Literal("🤠"), internal_fixed(TimezoneOffsetPermissive)],
            p().set_offset(45_240),
        );
        check("Z", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(0));
        check("A", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("PST", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("z", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(0));
        check(" Z", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(0));
        check(" z", &[internal_fixed(TimezoneOffsetPermissive)], p().set_offset(0));
        check("Z ", &[internal_fixed(TimezoneOffsetPermissive)], Err(TOO_LONG));
        check("#Z", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check(":Z", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check(":z", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+Z", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("-Z", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+A", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+PST", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+🙃", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+Z:", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check(" :Z", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check(" +Z", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check(" -Z", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("+:Z", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));
        check("Y", &[internal_fixed(TimezoneOffsetPermissive)], Err(Error::InvalidCharacter(0)));

        // TimezoneName
        check("CEST", &[fixed(TimezoneName)], Ok(&mut p()));
        check("cest", &[fixed(TimezoneName)], Ok(&mut p())); // lowercase
        check("XXXXXXXX", &[fixed(TimezoneName)], Ok(&mut p())); // not a real timezone name
        check("!!!!", &[fixed(TimezoneName)], Ok(&mut p())); // not a real timezone name!
        check("CEST 5", &[fixed(TimezoneName), Literal(" "), num(Numeric::Day)], p().set_day(5));
        check("CEST ", &[fixed(TimezoneName)], Err(TOO_LONG));
        check(" CEST", &[fixed(TimezoneName)], Err(TOO_LONG));
        check("CE ST", &[fixed(TimezoneName)], Err(TOO_LONG));

        Ok(())
    }

    #[test]
    #[rustfmt::skip]
    fn test_parse_practical_examples() -> Result<(), Error> {
        use crate::format::InternalInternal::*;
        use crate::format::Item::{Literal, Space};
        use crate::format::Numeric::*;

        let p = Parsed::new;

        // some practical examples
        check(
            "2015-02-04T14:37:05+09:00",
            &[
                num(Year), Literal("-"), num(Month), Literal("-"), num(Day), Literal("T"),
                num(Hour), Literal(":"), num(Minute), Literal(":"), num(Second),
                fixed(Fixed::TimezoneOffset),
            ],
            p().set_year(2015)?.set_month(2)?.set_day(4)?.set_hour(14)?.set_minute(37)?.set_second(5)?.set_offset(32_400),
        );
        check(
            "2015-02-04T14:37:05-09:00",
            &[
                num(Year), Literal("-"), num(Month), Literal("-"), num(Day), Literal("T"),
                num(Hour), Literal(":"), num(Minute), Literal(":"), num(Second),
                fixed(Fixed::TimezoneOffset),
            ],
            p().set_year(2015)?.set_month(2)?.set_day(4)?.set_hour(14)?.set_minute(37)?.set_second(5)?.set_offset(-32_400),
        );
        check(
            "2015-02-04T14:37:05−09:00", // timezone offset using MINUS SIGN (U+2212)
            &[
                num(Year), Literal("-"), num(Month), Literal("-"), num(Day), Literal("T"),
                num(Hour), Literal(":"), num(Minute), Literal(":"), num(Second),
                fixed(Fixed::TimezoneOffset)
            ],
            p().set_year(2015)?.set_month(2)?.set_day(4)?.set_hour(14)?.set_minute(37)?.set_second(5)?.set_offset(-32_400),
        );
        check(
            "20150204143705567",
            &[
                num(Year), num(Month), num(Day), num(Hour), num(Minute), num(Second),
                internal_fixed(Nanosecond3NoDot)
            ],
            p().set_year(2015)?.set_month(2)?.set_day(4)?.set_hour(14)?.set_minute(37)?.set_second(5)?.set_nanosecond(567_000_000),
        );
        check(
            "Mon, 10 Jun 2013 09:32:37 GMT",
            &[
                fixed(Fixed::ShortWeekdayName), Literal(","), Space(" "), num(Day), Space(" "),
                fixed(Fixed::ShortMonthName), Space(" "), num(Year), Space(" "), num(Hour),
                Literal(":"), num(Minute), Literal(":"), num(Second), Space(" "), Literal("GMT")
            ],
            p().set_year(2013)?.set_month(6)?.set_day(10)?.set_weekday(Weekday::Mon)?.set_hour(9)?.set_minute(32)?.set_second(37),
        );
        check(
            "🤠Mon, 10 Jun🤠2013 09:32:37  GMT🤠",
            &[
                Literal("🤠"), fixed(Fixed::ShortWeekdayName), Literal(","), Space(" "), num(Day),
                Space(" "), fixed(Fixed::ShortMonthName), Literal("🤠"), num(Year), Space(" "),
                num(Hour), Literal(":"), num(Minute), Literal(":"), num(Second), Space("  "),
                Literal("GMT"), Literal("🤠")
            ],
            p().set_year(2013)?.set_month(6)?.set_day(10)?.set_weekday(Weekday::Mon)?.set_hour(9)?.set_minute(32)?.set_second(37),
        );
        check(
            "Sun Aug 02 13:39:15 CEST 2020",
            &[
                fixed(Fixed::ShortWeekdayName), Space(" "), fixed(Fixed::ShortMonthName),
                Space(" "), num(Day), Space(" "), num(Hour), Literal(":"), num(Minute),
                Literal(":"), num(Second), Space(" "), fixed(Fixed::TimezoneName), Space(" "),
                num(Year)
            ],
            p().set_year(2020)?.set_month(8)?.set_day(2)?.set_weekday(Weekday::Sun)?.set_hour(13)?.set_minute(39)?.set_second(15),
        );
        check(
            "20060102150405",
            &[num(Year), num(Month), num(Day), num(Hour), num(Minute), num(Second)],
            p().set_year(2006)?.set_month(1)?.set_day(2)?.set_hour(15)?.set_minute(4)?.set_second(5),
        );
        check(
            "3:14PM",
            &[num(Hour12), Literal(":"), num(Minute), fixed(Fixed::LowerAmPm)],
            p().set_ampm(true)?.set_hour12(3)?.set_minute(14),
        );
        check(
            "12345678901234.56789",
            &[num(Timestamp), Literal("."), num(Nanosecond)],
            p().set_nanosecond(56_789)?.set_timestamp(12_345_678_901_234),
        );
        check(
            "12345678901234.56789",
            &[num(Timestamp), fixed(Fixed::Nanosecond)],
            p().set_nanosecond(567_890_000)?.set_timestamp(12_345_678_901_234),
        );

        // docstring examples from `impl str::FromStr`
        check(
            "2000-01-02T03:04:05Z",
            &[
                num(Year), Literal("-"), num(Month), Literal("-"), num(Day), Literal("T"),
                num(Hour), Literal(":"), num(Minute), Literal(":"), num(Second),
                internal_fixed(TimezoneOffsetPermissive)
            ],
            p().set_year(2000)?.set_month(1)?.set_day(2)?.set_hour(3)?.set_minute(4)?.set_second(5)?.set_offset(0),
        );
        check(
            "2000-01-02 03:04:05Z",
            &[
                num(Year), Literal("-"), num(Month), Literal("-"), num(Day), Space(" "),
                num(Hour), Literal(":"), num(Minute), Literal(":"), num(Second),
                internal_fixed(TimezoneOffsetPermissive)
            ],
            p().set_year(2000)?.set_month(1)?.set_day(2)?.set_hour(3)?.set_minute(4)?.set_second(5)?.set_offset(0),
        );

        Ok(())
    }

    #[track_caller]
    fn parses(s: &str, items: &[Item]) {
        let mut parsed = Parsed::new();
        assert!(parse(&mut parsed, s, items.iter()).is_ok());
    }

    #[track_caller]
    fn check(s: &str, items: &[Item], expected: Result<&mut Parsed, Error>) {
        let mut parsed = Parsed::new();
        let result = parse(&mut parsed, s, items.iter());
        let parsed = result.map(|_| parsed);
        assert_eq!(parsed.as_ref(), expected.as_deref());
    }

    #[test]
    fn test_rfc2822() {
        let ymd_hmsn = |y, m, d, h, n, s, nano, off| {
            FixedOffset::east(off * 60 * 60)
                .unwrap()
                .with_ymd_and_hms(y, m, d, h, n, s)
                .unwrap()
                .with_nanosecond(nano)
                .unwrap()
        };

        // Test data - (input, Ok(expected result) or Err(error code))
        let testdates = [
            ("Tue, 20 Jan 2015 17:35:20 -0800", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8))), // normal case
            ("Fri,  2 Jan 2015 17:35:20 -0800", Ok(ymd_hmsn(2015, 1, 2, 17, 35, 20, 0, -8))), // folding whitespace
            ("Fri, 02 Jan 2015 17:35:20 -0800", Ok(ymd_hmsn(2015, 1, 2, 17, 35, 20, 0, -8))), // leading zero
            ("Tue, 20 Jan 2015 17:35:20 -0800 (UTC)", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8))), // trailing comment
            (
                r"Tue, 20 Jan 2015 17:35:20 -0800 ( (UTC ) (\( (a)\(( \t ) ) \\( \) ))",
                Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8)),
            ), // complex trailing comment
            (r"Tue, 20 Jan 2015 17:35:20 -0800 (UTC\)", Err(TOO_LONG)), // incorrect comment, not enough closing parentheses
            (
                "Tue, 20 Jan 2015 17:35:20 -0800 (UTC)\t \r\n(Anothercomment)",
                Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8)),
            ), // multiple comments
            ("Tue, 20 Jan 2015 17:35:20 -0800 (UTC) ", Err(TOO_LONG)), // trailing whitespace after comment
            ("20 Jan 2015 17:35:20 -0800", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8))), // no day of week
            ("20 JAN 2015 17:35:20 -0800", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8))), // upper case month
            ("Tue, 20 Jan 2015 17:35 -0800", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 0, 0, -8))), // no second
            ("11 Sep 2001 09:45:00 +0000", Ok(ymd_hmsn(2001, 9, 11, 9, 45, 0, 0, 0))),
            ("11 Sep 2001 09:45:00 EST", Ok(ymd_hmsn(2001, 9, 11, 9, 45, 0, 0, -5))),
            ("11 Sep 2001 09:45:00 GMT", Ok(ymd_hmsn(2001, 9, 11, 9, 45, 0, 0, 0))),
            ("30 Feb 2015 17:35:20 -0800", Err(Error::DoesNotExist)), // bad day of month
            ("Tue, 20 Jan 2015", Err(Error::InvalidCharacter(16))),    // omitted fields
            ("Tue, 20 Avr 2015 17:35:20 -0800", Err(Error::InvalidValue(11))),        // bad month name
            ("Tue, 20 Jan 2015 25:35:20 -0800", Err(Error::InvalidValue(19))),   // bad hour
            ("Tue, 20 Jan 2015 7:35:20 -0800", Err(Error::InvalidCharacter(18))),         // bad # of digits in hour
            ("Tue, 20 Jan 2015 17:65:20 -0800", Err(Error::InvalidValue(22))),   // bad minute
            ("Tue, 20 Jan 2015 17:35:90 -0800", Err(Error::InvalidValue(25))),   // bad second
            ("Tue, 20 Jan 2015 17:35:20 -0890", Err(Error::InvalidValue(29))),   // bad offset
            ("6 Jun 1944 04:00:00Z", Err(Error::InvalidCharacter(0))), // bad offset (zulu not allowed)
            // named timezones that have specific timezone offsets
            // see https://www.rfc-editor.org/rfc/rfc2822#section-4.3
            ("Tue, 20 Jan 2015 17:35:20 GMT", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, 0))),
            ("Tue, 20 Jan 2015 17:35:20 UT", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, 0))),
            ("Tue, 20 Jan 2015 17:35:20 ut", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, 0))),
            ("Tue, 20 Jan 2015 17:35:20 EDT", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -4))),
            ("Tue, 20 Jan 2015 17:35:20 EST", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -5))),
            ("Tue, 20 Jan 2015 17:35:20 CDT", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -5))),
            ("Tue, 20 Jan 2015 17:35:20 CST", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -6))),
            ("Tue, 20 Jan 2015 17:35:20 MDT", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -6))),
            ("Tue, 20 Jan 2015 17:35:20 MST", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -7))),
            ("Tue, 20 Jan 2015 17:35:20 PDT", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -7))),
            ("Tue, 20 Jan 2015 17:35:20 PST", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8))),
            ("Tue, 20 Jan 2015 17:35:20 pst", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8))),
            // named single-letter military timezones must fallback to +0000
            ("Tue, 20 Jan 2015 17:35:20 Z", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, 0))),
            ("Tue, 20 Jan 2015 17:35:20 A", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, 0))),
            ("Tue, 20 Jan 2015 17:35:20 a", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, 0))),
            ("Tue, 20 Jan 2015 17:35:20 K", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, 0))),
            ("Tue, 20 Jan 2015 17:35:20 k", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, 0))),
            // named single-letter timezone "J" is specifically not valid
            ("Tue, 20 Jan 2015 17:35:20 J", Err(Error::InvalidCharacter(0))),
            ("Tue, 20 Jan 2015 17:35:20 -0890", Err(Error::InvalidValue(0))), // bad offset minutes
            ("Tue, 20 Jan 2015 17:35:20Z", Err(Error::InvalidCharacter(0))),           // bad offset: zulu not allowed
            ("Tue, 20 Jan 2015 17:35:20 Zulu", Err(Error::InvalidCharacter(0))),       // bad offset: zulu not allowed
            ("Tue, 20 Jan 2015 17:35:20 ZULU", Err(Error::InvalidCharacter(0))),       // bad offset: zulu not allowed
            ("Tue, 20 Jan 2015 17:35:20 −0800", Err(Error::InvalidCharacter(0))), // bad offset: timezone offset using MINUS SIGN (U+2212), not specified for RFC 2822
            ("Tue, 20 Jan 2015 17:35:20 0800", Err(Error::InvalidCharacter(0))),  // missing offset sign
            ("Tue, 20 Jan 2015 17:35:20 HAS", Err(Error::InvalidCharacter(0))),   // bad named timezone
            ("Tue, 20 Jan 2015😈17:35:20 -0800", Err(Error::InvalidCharacter(0))), // bad character!
        ];

        fn rfc2822_to_datetime(date: &str) -> Result<DateTime<FixedOffset>, Error> {
            let mut parsed = Parsed::new();
            parse(&mut parsed, date, [Item::Fixed(Fixed::RFC2822)].iter())?;
            parsed.to_datetime()
        }

        // Test against test data above
        for &(date, checkdate) in testdates.iter() {
            #[cfg(feature = "std")]
            eprintln!("Test input: {:?}\n    Expect: {:?}", date, checkdate);
            let dt = rfc2822_to_datetime(date); // parse a date
            if dt != checkdate {
                // check for expected result
                panic!(
                    "Date conversion failed for {}\nReceived: {:?}\nExpected: {:?}",
                    date, dt, checkdate
                );
            }
        }
    }

    #[test]
    fn parse_rfc850() {
        static RFC850_FMT: &str = "%A, %d-%b-%y %T GMT";

        let dt = Utc.with_ymd_and_hms(1994, 11, 6, 8, 49, 37).unwrap();

        // Check that the format is what we expect
        #[cfg(feature = "alloc")]
        assert_eq!(dt.format(RFC850_FMT).to_string(), "Sunday, 06-Nov-94 08:49:37 GMT");

        // Check that it parses correctly
        assert_eq!(
            NaiveDateTime::parse_from_str("Sunday, 06-Nov-94 08:49:37 GMT", RFC850_FMT),
            Ok(dt.naive_utc())
        );

        // Check that the rest of the weekdays parse correctly (this test originally failed because
        // Sunday parsed incorrectly).
        let testdates = [
            (
                Utc.with_ymd_and_hms(1994, 11, 7, 8, 49, 37).unwrap(),
                "Monday, 07-Nov-94 08:49:37 GMT",
            ),
            (
                Utc.with_ymd_and_hms(1994, 11, 8, 8, 49, 37).unwrap(),
                "Tuesday, 08-Nov-94 08:49:37 GMT",
            ),
            (
                Utc.with_ymd_and_hms(1994, 11, 9, 8, 49, 37).unwrap(),
                "Wednesday, 09-Nov-94 08:49:37 GMT",
            ),
            (
                Utc.with_ymd_and_hms(1994, 11, 10, 8, 49, 37).unwrap(),
                "Thursday, 10-Nov-94 08:49:37 GMT",
            ),
            (
                Utc.with_ymd_and_hms(1994, 11, 11, 8, 49, 37).unwrap(),
                "Friday, 11-Nov-94 08:49:37 GMT",
            ),
            (
                Utc.with_ymd_and_hms(1994, 11, 12, 8, 49, 37).unwrap(),
                "Saturday, 12-Nov-94 08:49:37 GMT",
            ),
        ];

        for val in &testdates {
            assert_eq!(NaiveDateTime::parse_from_str(val.1, RFC850_FMT), Ok(val.0.naive_utc()));
        }

        let test_dates_fail = [
            "Saturday, 12-Nov-94 08:49:37",
            "Saturday, 12-Nov-94 08:49:37 Z",
            "Saturday, 12-Nov-94 08:49:37 GMTTTT",
            "Saturday, 12-Nov-94 08:49:37 gmt",
            "Saturday, 12-Nov-94 08:49:37 +08:00",
            "Caturday, 12-Nov-94 08:49:37 GMT",
            "Saturday, 99-Nov-94 08:49:37 GMT",
            "Saturday, 12-Nov-2000 08:49:37 GMT",
            "Saturday, 12-Mop-94 08:49:37 GMT",
            "Saturday, 12-Nov-94 28:49:37 GMT",
            "Saturday, 12-Nov-94 08:99:37 GMT",
            "Saturday, 12-Nov-94 08:49:99 GMT",
        ];

        for val in &test_dates_fail {
            assert!(NaiveDateTime::parse_from_str(val, RFC850_FMT).is_err());
        }
    }

    #[test]
    fn test_rfc3339() {
        let ymd_hmsn = |y, m, d, h, n, s, nano, off| {
            FixedOffset::east(off * 60 * 60)
                .unwrap()
                .with_ymd_and_hms(y, m, d, h, n, s)
                .unwrap()
                .with_nanosecond(nano)
                .unwrap()
        };

        // Test data - (input, Ok(expected result) or Err(error code))
        let testdates = [
            ("2015-01-20T17:35:20-08:00", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8))), // normal case
            ("2015-01-20T17:35:20−08:00", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8))), // normal case with MINUS SIGN (U+2212)
            ("1944-06-06T04:04:00Z", Ok(ymd_hmsn(1944, 6, 6, 4, 4, 0, 0, 0))),           // D-day
            ("2001-09-11T09:45:00-08:00", Ok(ymd_hmsn(2001, 9, 11, 9, 45, 0, 0, -8))),
            ("2015-01-20T17:35:20.001-08:00", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 1_000_000, -8))),
            ("2015-01-20T17:35:20.001−08:00", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 1_000_000, -8))), // with MINUS SIGN (U+2212)
            ("2015-01-20T17:35:20.000031-08:00", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 31_000, -8))),
            ("2015-01-20T17:35:20.000000004-08:00", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 4, -8))),
            ("2015-01-20T17:35:20.000000004−08:00", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 4, -8))), // with MINUS SIGN (U+2212)
            (
                "2015-01-20T17:35:20.000000000452-08:00",
                Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8)),
            ), // too small
            (
                "2015-01-20T17:35:20.000000000452−08:00",
                Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8)),
            ), // too small with MINUS SIGN (U+2212)
            ("2015-01-20 17:35:20-08:00", Ok(ymd_hmsn(2015, 1, 20, 17, 35, 20, 0, -8))), // without 'T'
            ("2015/01/20T17:35:20.001-08:00", Err(Error::InvalidCharacter(0))), // wrong separator char YMD
            ("2015-01-20T17-35-20.001-08:00", Err(Error::InvalidCharacter(0))), // wrong separator char HMS
            ("-01-20T17:35:20-08:00", Err(Error::InvalidCharacter(0))),         // missing year
            ("99-01-20T17:35:20-08:00", Err(Error::InvalidCharacter(0))),       // bad year format
            ("99999-01-20T17:35:20-08:00", Err(Error::InvalidCharacter(0))),    // bad year value
            ("-2000-01-20T17:35:20-08:00", Err(Error::InvalidCharacter(0))),    // bad year value
            ("2015-02-30T17:35:20-08:00", Err(Error::DoesNotExist)), // bad day of month value
            ("2015-01-20T25:35:20-08:00", Err(Error::InvalidValue(0))), // bad hour value
            ("2015-01-20T17:65:20-08:00", Err(Error::InvalidValue(0))), // bad minute value
            ("2015-01-20T17:35:90-08:00", Err(Error::InvalidValue(0))), // bad second value
            ("2015-01-20T17:35:20-24:00", Err(Error::InvalidValue(0))), // bad offset value
            ("15-01-20T17:35:20-08:00", Err(Error::InvalidCharacter(0))), // bad year format
            ("15-01-20T17:35:20-08:00:00", Err(Error::InvalidCharacter(0))), // bad year format, bad offset format
            ("2015-01-20T17:35:2008:00", Err(Error::InvalidCharacter(0))),   // missing offset sign
            ("2015-01-20T17:35:20 08:00", Err(Error::InvalidCharacter(0))),  // missing offset sign
            ("2015-01-20T17:35:20Zulu", Err(Error::TooLong)),             // bad offset format
            ("2015-01-20T17:35:20 Zulu", Err(Error::InvalidCharacter(0))),   // bad offset format
            ("2015-01-20T17:35:20GMT", Err(Error::InvalidCharacter(0))),     // bad offset format
            ("2015-01-20T17:35:20 GMT", Err(Error::InvalidCharacter(0))),    // bad offset format
            ("2015-01-20T17:35:20+GMT", Err(Error::InvalidCharacter(0))),    // bad offset format
            ("2015-01-20T17:35:20++08:00", Err(Error::InvalidCharacter(0))), // bad offset format
            ("2015-01-20T17:35:20--08:00", Err(Error::InvalidCharacter(0))), // bad offset format
            ("2015-01-20T17:35:20−−08:00", Err(Error::InvalidCharacter(0))), // bad offset format with MINUS SIGN (U+2212)
            ("2015-01-20T17:35:20±08:00", Err(Error::InvalidCharacter(0))),  // bad offset sign
            ("2015-01-20T17:35:20-08-00", Err(Error::InvalidCharacter(0))),  // bad offset separator
            ("2015-01-20T17:35:20-08;00", Err(Error::InvalidCharacter(0))),  // bad offset separator
            ("2015-01-20T17:35:20-0800", Err(Error::InvalidCharacter(0))),   // bad offset separator
            ("2015-01-20T17:35:20-08:0", Err(Error::InvalidCharacter(0))),           // bad offset minutes
            ("2015-01-20T17:35:20-08:AA", Err(Error::InvalidCharacter(0))),  // bad offset minutes
            ("2015-01-20T17:35:20-08:ZZ", Err(Error::InvalidCharacter(0))),  // bad offset minutes
            ("2015-01-20T17:35:20.001-08 : 00", Err(Error::InvalidCharacter(0))), // bad offset separator
            ("2015-01-20T17:35:20-08:00:00", Err(Error::TooLong)),             // bad offset format
            ("2015-01-20T17:35:20+08:", Err(Error::InvalidCharacter(0))),                 // bad offset format
            ("2015-01-20T17:35:20-08:", Err(Error::InvalidCharacter(0))),                 // bad offset format
            ("2015-01-20T17:35:20−08:", Err(Error::InvalidCharacter(0))), // bad offset format with MINUS SIGN (U+2212)
            ("2015-01-20T17:35:20-08", Err(Error::InvalidCharacter(0))),  // bad offset format
            ("2015-01-20T", Err(Error::InvalidCharacter(0))),             // missing HMS
            ("2015-01-20T00:00:1", Err(Error::InvalidCharacter(0))),      // missing complete S
            ("2015-01-20T00:00:1-08:00", Err(Error::InvalidCharacter(0))), // missing complete S
        ];

        // Test against test data above
        for &(date, checkdate) in testdates.iter() {
            let dt = DateTime::parse_from_rfc3339(date);
            if dt != checkdate {
                // check for expected result
                panic!(
                    "Date conversion failed for {}\nReceived: {:?}\nExpected: {:?}",
                    date, dt, checkdate
                );
            }
        }
    }

    #[test]
    fn test_issue_1010() {
        let dt = crate::NaiveDateTime::parse_from_str("\u{c}SUN\u{e}\u{3000}\0m@J\u{3000}\0\u{3000}\0m\u{c}!\u{c}\u{b}\u{c}\u{c}\u{c}\u{c}%A\u{c}\u{b}\0SU\u{c}\u{c}",
        "\u{c}\u{c}%A\u{c}\u{b}\0SUN\u{c}\u{c}\u{c}SUNN\u{c}\u{c}\u{c}SUN\u{c}\u{c}!\u{c}\u{b}\u{c}\u{c}\u{c}\u{c}%A\u{c}\u{b}%a");
        assert_eq!(dt, Err(Error::InvalidCharacter(4)));
    }
}
