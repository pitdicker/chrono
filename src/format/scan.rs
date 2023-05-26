// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

/*!
 * Various scanning routines for the parser.
 */

use super::{Colons, OffsetFormat, OffsetPrecision, Pad, ParseResult};
use super::{INVALID, OUT_OF_RANGE, TOO_SHORT};
use crate::Weekday;

/// Tries to parse the non-negative number from `min` to `max` digits.
///
/// The absence of digits at all is an unconditional error.
/// More than `max` digits are consumed up to the first `max` digits.
/// Any number that does not fit in `i64` is an error.
#[inline]
pub(super) fn number(s: &str, min: usize, max: usize) -> ParseResult<(&str, i64)> {
    assert!(min <= max);

    // We are only interested in ascii numbers, so we can work with the `str` as bytes. We stop on
    // the first non-numeric byte, which may be another ascii character or beginning of multi-byte
    // UTF-8 character.
    let bytes = s.as_bytes();
    if bytes.len() < min {
        return Err(TOO_SHORT);
    }

    let mut n = 0i64;
    for (i, c) in bytes.iter().take(max).cloned().enumerate() {
        // cloned() = copied()
        if !c.is_ascii_digit() {
            if i < min {
                return Err(INVALID);
            } else {
                return Ok((&s[i..], n));
            }
        }

        n = match n.checked_mul(10).and_then(|n| n.checked_add((c - b'0') as i64)) {
            Some(n) => n,
            None => return Err(OUT_OF_RANGE),
        };
    }

    Ok((&s[core::cmp::min(max, bytes.len())..], n))
}

/// Tries to consume at least one digits as a fractional second.
/// Returns the number of whole nanoseconds (0--999,999,999).
pub(super) fn nanosecond(s: &str) -> ParseResult<(&str, i64)> {
    // record the number of digits consumed for later scaling.
    let origlen = s.len();
    let (s, v) = number(s, 1, 9)?;
    let consumed = origlen - s.len();

    // scale the number accordingly.
    static SCALE: [i64; 10] =
        [0, 100_000_000, 10_000_000, 1_000_000, 100_000, 10_000, 1_000, 100, 10, 1];
    let v = v.checked_mul(SCALE[consumed]).ok_or(OUT_OF_RANGE)?;

    // if there are more than 9 digits, skip next digits.
    let s = s.trim_start_matches(|c: char| c.is_ascii_digit());

    Ok((s, v))
}

/// Tries to consume a fixed number of digits as a fractional second.
/// Returns the number of whole nanoseconds (0--999,999,999).
pub(super) fn nanosecond_fixed(s: &str, digits: usize) -> ParseResult<(&str, i64)> {
    // record the number of digits consumed for later scaling.
    let (s, v) = number(s, digits, digits)?;

    // scale the number accordingly.
    static SCALE: [i64; 10] =
        [0, 100_000_000, 10_000_000, 1_000_000, 100_000, 10_000, 1_000, 100, 10, 1];
    let v = v.checked_mul(SCALE[digits]).ok_or(OUT_OF_RANGE)?;

    Ok((s, v))
}

/// Tries to parse the month index (0 through 11) with the first three ASCII letters.
pub(super) fn short_month0(s: &str) -> ParseResult<(&str, u8)> {
    if s.len() < 3 {
        return Err(TOO_SHORT);
    }
    let buf = s.as_bytes();
    let month0 = match (buf[0] | 32, buf[1] | 32, buf[2] | 32) {
        (b'j', b'a', b'n') => 0,
        (b'f', b'e', b'b') => 1,
        (b'm', b'a', b'r') => 2,
        (b'a', b'p', b'r') => 3,
        (b'm', b'a', b'y') => 4,
        (b'j', b'u', b'n') => 5,
        (b'j', b'u', b'l') => 6,
        (b'a', b'u', b'g') => 7,
        (b's', b'e', b'p') => 8,
        (b'o', b'c', b't') => 9,
        (b'n', b'o', b'v') => 10,
        (b'd', b'e', b'c') => 11,
        _ => return Err(INVALID),
    };
    Ok((&s[3..], month0))
}

/// Tries to parse the weekday with the first three ASCII letters.
pub(super) fn short_weekday(s: &str) -> ParseResult<(&str, Weekday)> {
    if s.len() < 3 {
        return Err(TOO_SHORT);
    }
    let buf = s.as_bytes();
    let weekday = match (buf[0] | 32, buf[1] | 32, buf[2] | 32) {
        (b'm', b'o', b'n') => Weekday::Mon,
        (b't', b'u', b'e') => Weekday::Tue,
        (b'w', b'e', b'd') => Weekday::Wed,
        (b't', b'h', b'u') => Weekday::Thu,
        (b'f', b'r', b'i') => Weekday::Fri,
        (b's', b'a', b't') => Weekday::Sat,
        (b's', b'u', b'n') => Weekday::Sun,
        _ => return Err(INVALID),
    };
    Ok((&s[3..], weekday))
}

/// Tries to parse the month index (0 through 11) with short or long month names.
/// It prefers long month names to short month names when both are possible.
pub(super) fn short_or_long_month0(s: &str) -> ParseResult<(&str, u8)> {
    // lowercased month names, minus first three chars
    static LONG_MONTH_SUFFIXES: [&[u8]; 12] = [
        b"uary", b"ruary", b"ch", b"il", b"", b"e", b"y", b"ust", b"tember", b"ober", b"ember",
        b"ember",
    ];

    let (mut s, month0) = short_month0(s)?;

    // tries to consume the suffix if possible
    let suffix = LONG_MONTH_SUFFIXES[month0 as usize];
    if s.len() >= suffix.len() && s.as_bytes()[..suffix.len()].eq_ignore_ascii_case(suffix) {
        s = &s[suffix.len()..];
    }

    Ok((s, month0))
}

/// Tries to parse the weekday with short or long weekday names.
/// It prefers long weekday names to short weekday names when both are possible.
pub(super) fn short_or_long_weekday(s: &str) -> ParseResult<(&str, Weekday)> {
    // lowercased weekday names, minus first three chars
    static LONG_WEEKDAY_SUFFIXES: [&[u8]; 7] =
        [b"day", b"sday", b"nesday", b"rsday", b"day", b"urday", b"day"];

    let (mut s, weekday) = short_weekday(s)?;

    // tries to consume the suffix if possible
    let suffix = LONG_WEEKDAY_SUFFIXES[weekday.num_days_from_monday() as usize];
    if s.len() >= suffix.len() && s.as_bytes()[..suffix.len()].eq_ignore_ascii_case(suffix) {
        s = &s[suffix.len()..];
    }

    Ok((s, weekday))
}

/// Tries to consume exactly one given character.
pub(super) fn char(s: &str, c1: u8) -> ParseResult<&str> {
    match s.as_bytes().first() {
        Some(&c) if c == c1 => Ok(&s[1..]),
        Some(_) => Err(INVALID),
        None => Err(TOO_SHORT),
    }
}

/// Tries to consume one or more whitespace.
pub(super) fn space(s: &str) -> ParseResult<&str> {
    let s_ = s.trim_start();
    if s_.len() < s.len() {
        Ok(s_)
    } else if s.is_empty() {
        Err(TOO_SHORT)
    } else {
        Err(INVALID)
    }
}

/// Tries to parse an utc offset as specified with `OffsetFormat`. Return an offset in seconds
/// if possible.
pub(crate) fn utc_offset(s: &str, fmt: OffsetFormat) -> ParseResult<(&str, i32)> {
    if fmt.allow_zulu && (s.starts_with('Z') || s.starts_with('z')) {
        return Ok((&s[1..], 0));
    }

    let (sign, mut s) = match s.chars().next() {
        Some('+') => (1, &s[1..]),
        Some('-') => (-1, &s[1..]),              // HYPHEN-MINUS (U+2D)
        Some('−') => (-1, &s['−'.len_utf8()..]), // MINUS SIGN (U+2212)
        Some(_) => return Err(INVALID),
        None => return Err(TOO_SHORT),
    };

    macro_rules! try_consume {
        ($e:expr) => {{
            let (s_, v) = $e?;
            s = s_;
            v
        }};
    }

    let hours = if fmt.padding == Pad::Zero {
        try_consume!(number(s, 2, 2))
    } else {
        let digits = match fmt.precision {
            OffsetPrecision::Hours => 2,
            OffsetPrecision::Minutes | OffsetPrecision::OptionalMinutes => 4,
            OffsetPrecision::Seconds
            | OffsetPrecision::OptionalSeconds
            | OffsetPrecision::OptionalMinutesAndSeconds => 6,
        };
        if s.as_bytes().iter().take_while(|c| c.is_ascii_digit()).take(digits).count() % 2 == 0 {
            if fmt.padding == Pad::Space && s.as_bytes()[0] == b'0' {
                return Err(INVALID);
            }
            try_consume!(number(s, 2, 2))
        } else {
            try_consume!(number(s, 1, 1))
        }
    };
    let mut offset = 3600 * hours as i32;

    if fmt.precision == OffsetPrecision::Hours {
        return Ok((s, offset * sign));
    }

    let minutes_optional = matches!(
        fmt.precision,
        OffsetPrecision::OptionalMinutes | OffsetPrecision::OptionalMinutesAndSeconds
    );
    let (s_new, minutes) = parse_offset_minute(s, fmt.colons, minutes_optional)?;
    match minutes {
        Some(m) => offset += m * 60,
        None => return Ok((s, offset * sign)),
    }
    let mut colons = fmt.colons;
    if colons == Colons::Maybe {
        colons = match s.starts_with(':') {
            true => Colons::Colon,
            false => Colons::None,
        };
    }
    s = s_new;

    if fmt.precision == OffsetPrecision::Minutes
        || fmt.precision == OffsetPrecision::OptionalMinutes
    {
        return Ok((s, offset * sign));
    }

    let seconds_optional = matches!(
        fmt.precision,
        OffsetPrecision::OptionalSeconds | OffsetPrecision::OptionalMinutesAndSeconds
    );
    let (s_new, seconds) = parse_offset_minute(s, colons, seconds_optional)?;
    if let Some(s) = seconds {
        offset += s;
    }
    s = s_new;

    Ok((s, offset * sign))
}

fn parse_offset_minute(
    mut s: &str,
    colon: Colons,
    optional: bool,
) -> ParseResult<(&str, Option<i32>)> {
    fn minutes(s: &str) -> ParseResult<(&str, Option<i32>)> {
        let b = s.as_bytes();
        if b.len() < 2 {
            return Err(TOO_SHORT);
        }
        let num = match (b[0], b[1]) {
            (m1 @ b'0'..=b'5', m2 @ b'0'..=b'9') => i32::from((m1 - b'0') * 10 + (m2 - b'0')),
            (b'6'..=b'9', b'0'..=b'9') => return Err(OUT_OF_RANGE),
            _ => return Err(INVALID),
        };
        Ok((&s[2..], Some(num)))
    }

    if (colon != Colons::None) && s.starts_with(':') {
        s = &s[1..];
        let result = minutes(s);
        if optional && (result == Err(TOO_SHORT) || result == Err(INVALID)) {
            Ok((s, None))
        } else {
            result
        }
    } else if colon != Colons::Colon {
        let result = minutes(s);
        if optional && (result == Err(TOO_SHORT) || result == Err(INVALID)) {
            Ok((s, None))
        } else {
            result
        }
    } else if optional {
        Ok((s, None))
    } else {
        Err(if s.is_empty() { TOO_SHORT } else { INVALID })
    }
}

/// Same as `timezone_offset` but also allows for RFC 2822 legacy timezones.
/// May return `None` which indicates an insufficient offset data (i.e. `-0000`).
/// See [RFC 2822 Section 4.3].
///
/// [RFC 2822 Section 4.3]: https://tools.ietf.org/html/rfc2822#section-4.3
pub(super) fn timezone_offset_2822(s: &str) -> ParseResult<(&str, Option<i32>)> {
    // tries to parse legacy time zone names
    let upto = s.as_bytes().iter().position(|&c| !c.is_ascii_alphabetic()).unwrap_or(s.len());
    if upto > 0 {
        let name = &s.as_bytes()[..upto];
        let s = &s[upto..];
        let offset_hours = |o| Ok((s, Some(o * 3600)));
        if name.eq_ignore_ascii_case(b"gmt") || name.eq_ignore_ascii_case(b"ut") {
            offset_hours(0)
        } else if name.eq_ignore_ascii_case(b"edt") {
            offset_hours(-4)
        } else if name.eq_ignore_ascii_case(b"est") || name.eq_ignore_ascii_case(b"cdt") {
            offset_hours(-5)
        } else if name.eq_ignore_ascii_case(b"cst") || name.eq_ignore_ascii_case(b"mdt") {
            offset_hours(-6)
        } else if name.eq_ignore_ascii_case(b"mst") || name.eq_ignore_ascii_case(b"pdt") {
            offset_hours(-7)
        } else if name.eq_ignore_ascii_case(b"pst") {
            offset_hours(-8)
        } else if name.len() == 1 {
            match name[0] {
                // recommended by RFC 2822: consume but treat it as -0000
                b'a'..=b'i' | b'k'..=b'z' | b'A'..=b'I' | b'K'..=b'Z' => offset_hours(0),
                _ => Ok((s, None)),
            }
        } else {
            Ok((s, None))
        }
    } else {
        let offset_format = OffsetFormat {
            precision: OffsetPrecision::Minutes,
            colons: Colons::None,
            allow_zulu: false,
            padding: Pad::Zero,
        };
        let (s_, offset) = utc_offset(s, offset_format)?;
        Ok((s_, Some(offset)))
    }
}

/// Tries to consume an RFC2822 comment including preceding ` `.
///
/// Returns the remaining string after the closing parenthesis.
pub(super) fn comment_2822(s: &str) -> ParseResult<(&str, ())> {
    use CommentState::*;

    let s = s.trim_start();

    let mut state = Start;
    for (i, c) in s.bytes().enumerate() {
        state = match (state, c) {
            (Start, b'(') => Next(1),
            (Next(1), b')') => return Ok((&s[i + 1..], ())),
            (Next(depth), b'\\') => Escape(depth),
            (Next(depth), b'(') => Next(depth + 1),
            (Next(depth), b')') => Next(depth - 1),
            (Next(depth), _) | (Escape(depth), _) => Next(depth),
            _ => return Err(INVALID),
        };
    }

    Err(TOO_SHORT)
}

enum CommentState {
    Start,
    Next(usize),
    Escape(usize),
}

#[cfg(test)]
mod tests {
    use super::{
        comment_2822, nanosecond, nanosecond_fixed, short_or_long_month0, short_or_long_weekday,
        timezone_offset_2822, utc_offset,
    };
    use crate::format::{Colons, OffsetFormat, OffsetPrecision, Pad};
    use crate::format::{INVALID, TOO_SHORT};
    use crate::Weekday;

    #[test]
    fn test_rfc2822_comments() {
        let testdata = [
            ("", Err(TOO_SHORT)),
            (" ", Err(TOO_SHORT)),
            ("x", Err(INVALID)),
            ("(", Err(TOO_SHORT)),
            ("()", Ok("")),
            (" \r\n\t()", Ok("")),
            ("() ", Ok(" ")),
            ("()z", Ok("z")),
            ("(x)", Ok("")),
            ("(())", Ok("")),
            ("((()))", Ok("")),
            ("(x(x(x)x)x)", Ok("")),
            ("( x ( x ( x ) x ) x )", Ok("")),
            (r"(\)", Err(TOO_SHORT)),
            (r"(\()", Ok("")),
            (r"(\))", Ok("")),
            (r"(\\)", Ok("")),
            ("(()())", Ok("")),
            ("( x ( x ) x ( x ) x )", Ok("")),
        ];

        for (test_in, expected) in testdata.iter() {
            let actual = comment_2822(test_in).map(|(s, _)| s);
            assert_eq!(
                *expected, actual,
                "{:?} expected to produce {:?}, but produced {:?}.",
                test_in, expected, actual
            );
        }
    }

    #[test]
    fn test_timezone_offset_2822() {
        assert_eq!(timezone_offset_2822("cSt").unwrap(), ("", Some(-21600)));
        assert_eq!(timezone_offset_2822("pSt").unwrap(), ("", Some(-28800)));
        assert_eq!(timezone_offset_2822("mSt").unwrap(), ("", Some(-25200)));
        assert_eq!(timezone_offset_2822("-1551").unwrap(), ("", Some(-57060)));
        assert_eq!(timezone_offset_2822("Gp").unwrap(), ("", None));
    }

    #[test]
    fn test_short_or_long_month0() {
        assert_eq!(short_or_long_month0("JUn").unwrap(), ("", 5));
        assert_eq!(short_or_long_month0("mAy").unwrap(), ("", 4));
        assert_eq!(short_or_long_month0("AuG").unwrap(), ("", 7));
        assert_eq!(short_or_long_month0("Aprâ").unwrap(), ("â", 3));
        assert_eq!(short_or_long_month0("JUl").unwrap(), ("", 6));
        assert_eq!(short_or_long_month0("mAr").unwrap(), ("", 2));
        assert_eq!(short_or_long_month0("Jan").unwrap(), ("", 0));
    }

    #[test]
    fn test_short_or_long_weekday() {
        assert_eq!(short_or_long_weekday("sAtu").unwrap(), ("u", Weekday::Sat));
        assert_eq!(short_or_long_weekday("thu").unwrap(), ("", Weekday::Thu));
    }

    #[test]
    fn test_nanosecond_fixed() {
        assert_eq!(nanosecond_fixed("", 0usize).unwrap(), ("", 0));
        assert!(nanosecond_fixed("", 1usize).is_err());
    }

    #[test]
    fn test_nanosecond() {
        assert_eq!(nanosecond("2Ù").unwrap(), ("Ù", 200000000));
        assert_eq!(nanosecond("8").unwrap(), ("", 800000000));
    }

    #[test]
    fn test_offset_colons() {
        let mut offset_format = OffsetFormat {
            precision: OffsetPrecision::Seconds,
            colons: Colons::Maybe,
            allow_zulu: false,
            padding: Pad::Zero,
        };
        assert_eq!(utc_offset("+123456", offset_format).unwrap().1, 45_296);
        assert_eq!(utc_offset("+12:34:56", offset_format).unwrap().1, 45_296);
        assert!(utc_offset("+12 : 34 : 56", offset_format).is_err());
        assert!(utc_offset("+12.34.56", offset_format).is_err());
        assert!(utc_offset("+12 34 56", offset_format).is_err());
        assert!(utc_offset("+12😼34😼56", offset_format).is_err());
        // colons are optional, but they must match
        assert!(utc_offset("+12:3456", offset_format).is_err());
        assert!(utc_offset("+1234:56", offset_format).is_err());

        offset_format.colons = Colons::None;
        assert_eq!(utc_offset("+123456", offset_format).unwrap().1, 45_296);
        assert!(utc_offset("+12:34:56", offset_format).is_err());
        assert!(utc_offset("+12 : 34 : 56", offset_format).is_err());
        assert!(utc_offset("+12.34.56", offset_format).is_err());
        assert!(utc_offset("+12 34 56", offset_format).is_err());
        assert!(utc_offset("+12😼34😼56", offset_format).is_err());
        assert!(utc_offset("+12:3456", offset_format).is_err());
        assert!(utc_offset("+1234:56", offset_format).is_err());

        offset_format.colons = Colons::Colon;
        assert!(utc_offset("+123456", offset_format).is_err());
        assert_eq!(utc_offset("+12:34:56", offset_format).unwrap().1, 45_296);
        assert!(utc_offset("+12 : 34 : 56", offset_format).is_err());
        assert!(utc_offset("+12.34.56", offset_format).is_err());
        assert!(utc_offset("+12 34 56", offset_format).is_err());
        assert!(utc_offset("+12😼34😼56", offset_format).is_err());
        assert!(utc_offset("+12:3456", offset_format).is_err());
        assert!(utc_offset("+1234:56", offset_format).is_err());
    }

    #[test]
    fn test_offset_padding_with_colons() {
        let mut offset_format = OffsetFormat {
            precision: OffsetPrecision::OptionalSeconds,
            colons: Colons::Colon,
            allow_zulu: false,
            padding: Pad::Zero,
        };
        assert_eq!(utc_offset("+12:34:56", offset_format).unwrap().1, 45_296);
        assert_eq!(utc_offset("+01:23:45", offset_format).unwrap().1, 5025);
        assert_eq!(utc_offset("+01:23", offset_format).unwrap().1, 4980);
        assert!(utc_offset("+1:23:45", offset_format).is_err());
        assert!(utc_offset("+1:23", offset_format).is_err());
        assert!(utc_offset("+ 1:23:45", offset_format).is_err());
        assert!(utc_offset(" +1:23:45", offset_format).is_err());
        assert!(utc_offset("+012:34:56", offset_format).is_err());
        assert!(utc_offset("+001:23:45", offset_format).is_err());

        offset_format.padding = Pad::None;
        assert_eq!(utc_offset("+12:34:56", offset_format).unwrap().1, 45_296);
        assert_eq!(utc_offset("+01:23:45", offset_format).unwrap().1, 5025);
        assert_eq!(utc_offset("+01:23", offset_format).unwrap().1, 4980);
        assert_eq!(utc_offset("+1:23:45", offset_format).unwrap().1, 5025);
        assert_eq!(utc_offset("+1:23", offset_format).unwrap().1, 4980);
        assert!(utc_offset("+ 1:23:45", offset_format).is_err());
        assert!(utc_offset(" +1:23:45", offset_format).is_err());
        assert!(utc_offset("+012:34:56", offset_format).is_err());
        assert!(utc_offset("+001:23:45", offset_format).is_err());

        offset_format.padding = Pad::Space;
        assert_eq!(utc_offset("+12:34:56", offset_format).unwrap().1, 45_296);
        assert!(utc_offset("+01:23:45", offset_format).is_err());
        assert!(utc_offset("+01:23", offset_format).is_err());
        assert_eq!(utc_offset("+1:23:45", offset_format).unwrap().1, 5025);
        assert_eq!(utc_offset("+1:23", offset_format).unwrap().1, 4980);
        assert!(utc_offset("+ 1:23:45", offset_format).is_err());
        assert!(utc_offset(" +1:23:45", offset_format).is_err());
        assert!(utc_offset("+012:34:56", offset_format).is_err());
        assert!(utc_offset("+001:23:45", offset_format).is_err());
    }

    #[test]
    fn test_offset_padding_with_no_colons() {
        let mut offset_format = OffsetFormat {
            precision: OffsetPrecision::OptionalSeconds,
            colons: Colons::None,
            allow_zulu: false,
            padding: Pad::Zero,
        };
        assert_eq!(utc_offset("+123456", offset_format).unwrap().1, 45_296);
        assert_eq!(utc_offset("+012345", offset_format).unwrap().1, 5025);
        assert_eq!(utc_offset("+0123", offset_format).unwrap().1, 4980);
        assert_eq!(utc_offset("+12345", offset_format).unwrap().1, 45_240); // parsed as +12:34
        assert!(utc_offset("+123", offset_format).is_err());
        assert!(utc_offset("+ 12345", offset_format).is_err());
        assert!(utc_offset(" +12345", offset_format).is_err());

        offset_format.padding = Pad::None;
        assert_eq!(utc_offset("+123456", offset_format).unwrap().1, 45_296);
        assert_eq!(utc_offset("+012345", offset_format).unwrap().1, 5025);
        assert_eq!(utc_offset("+0123", offset_format).unwrap().1, 4980);
        assert_eq!(utc_offset("+12345", offset_format).unwrap().1, 5025);
        assert_eq!(utc_offset("+123", offset_format).unwrap().1, 4980);
        assert!(utc_offset("+ 12345", offset_format).is_err());
        assert!(utc_offset(" +12345", offset_format).is_err());

        offset_format.padding = Pad::Space;
        assert_eq!(utc_offset("+123456", offset_format).unwrap().1, 45_296);
        assert!(utc_offset("+012345", offset_format).is_err());
        assert!(utc_offset("+0123", offset_format).is_err());
        assert_eq!(utc_offset("+12345", offset_format).unwrap().1, 5025);
        assert_eq!(utc_offset("+123", offset_format).unwrap().1, 4980);
        assert!(utc_offset("+ 12345", offset_format).is_err());
        assert!(utc_offset(" +12345", offset_format).is_err());
    }

    #[test]
    fn test_offset_zulu() {
        let offset_format = OffsetFormat {
            precision: OffsetPrecision::Minutes,
            colons: Colons::Colon,
            allow_zulu: true,
            padding: Pad::Zero,
        };
        assert_eq!(utc_offset("Z", offset_format).unwrap().1, 0);
        assert_eq!(utc_offset("z", offset_format).unwrap().1, 0);
        assert_eq!(utc_offset("+00:00", offset_format).unwrap().1, 0);
        assert_eq!(utc_offset("+01:23", offset_format).unwrap().1, 4980);
        assert_eq!(utc_offset("-00:00", offset_format).unwrap().1, 0);
        assert!(utc_offset("+Z", offset_format).is_err());
        assert!(utc_offset("-Z", offset_format).is_err());
        assert!(utc_offset(" Z", offset_format).is_err());
    }

    #[test]
    fn test_offset_precision() {
        let mut offset_format = OffsetFormat {
            precision: OffsetPrecision::Hours,
            colons: Colons::Colon,
            allow_zulu: false,
            padding: Pad::Zero,
        };
        assert_eq!(utc_offset("+03", offset_format).unwrap(), ("", 10_800));
        assert_eq!(utc_offset("+03:30", offset_format).unwrap(), (":30", 10_800));

        offset_format.precision = OffsetPrecision::Minutes;
        assert!(utc_offset("+03", offset_format).is_err());
        assert_eq!(utc_offset("+03:30", offset_format).unwrap(), ("", 12_600));
        assert_eq!(utc_offset("+03:30:00", offset_format).unwrap(), (":00", 12_600));

        offset_format.precision = OffsetPrecision::OptionalMinutes;
        assert_eq!(utc_offset("+03", offset_format).unwrap(), ("", 10_800));
        assert_eq!(utc_offset("+03:30", offset_format).unwrap(), ("", 12_600));
        assert_eq!(utc_offset("+03:30:00", offset_format).unwrap(), (":00", 12_600));

        offset_format.precision = OffsetPrecision::Seconds;
        assert!(utc_offset("+03", offset_format).is_err());
        assert!(utc_offset("+03:30", offset_format).is_err());
        assert_eq!(utc_offset("+03:30:00", offset_format).unwrap(), ("", 12_600));

        offset_format.precision = OffsetPrecision::OptionalSeconds;
        assert!(utc_offset("+03", offset_format).is_err());
        assert_eq!(utc_offset("+03:30", offset_format).unwrap(), ("", 12_600));
        assert_eq!(utc_offset("+03:30:00", offset_format).unwrap(), ("", 12_600));

        offset_format.precision = OffsetPrecision::OptionalMinutesAndSeconds;
        assert_eq!(utc_offset("+03", offset_format).unwrap(), ("", 10_800));
        assert_eq!(utc_offset("+03:30", offset_format).unwrap(), ("", 12_600));
        assert_eq!(utc_offset("+03:30:00", offset_format).unwrap(), ("", 12_600));
    }

    #[test]
    fn test_offset_precision_no_padding() {
        let mut offset_format = OffsetFormat {
            precision: OffsetPrecision::Hours,
            colons: Colons::None,
            allow_zulu: false,
            padding: Pad::None,
        };
        assert_eq!(utc_offset("+3", offset_format).unwrap(), ("", 10_800));
        assert_eq!(utc_offset("+330", offset_format).unwrap(), ("0", 33 * 60 * 60));

        offset_format.precision = OffsetPrecision::Minutes;
        assert!(utc_offset("+3", offset_format).is_err());
        assert_eq!(utc_offset("+330", offset_format).unwrap(), ("", 12_600));
        assert_eq!(utc_offset("+33000", offset_format).unwrap(), ("0", 33 * 60 * 60));

        offset_format.precision = OffsetPrecision::OptionalMinutes;
        assert_eq!(utc_offset("+3", offset_format).unwrap(), ("", 10_800));
        assert_eq!(utc_offset("+330", offset_format).unwrap(), ("", 12_600));
        assert_eq!(utc_offset("+33000", offset_format).unwrap(), ("0", 33 * 60 * 60));

        offset_format.precision = OffsetPrecision::Seconds;
        assert!(utc_offset("+3", offset_format).is_err());
        assert!(utc_offset("+330", offset_format).is_err());
        assert_eq!(utc_offset("+33000", offset_format).unwrap(), ("", 12_600));

        offset_format.precision = OffsetPrecision::OptionalSeconds;
        assert!(utc_offset("+3", offset_format).is_err());
        assert_eq!(utc_offset("+330", offset_format).unwrap(), ("", 12_600));
        assert_eq!(utc_offset("+33000", offset_format).unwrap(), ("", 12_600));

        offset_format.precision = OffsetPrecision::OptionalMinutesAndSeconds;
        assert_eq!(utc_offset("+3", offset_format).unwrap(), ("", 10_800));
        assert_eq!(utc_offset("+330", offset_format).unwrap(), ("", 12_600));
        assert_eq!(utc_offset("+33000", offset_format).unwrap(), ("", 12_600));
    }
}
