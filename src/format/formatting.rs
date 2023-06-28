// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! Date and time formatting routines.

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::string::{String, ToString};
use core::borrow::Borrow;
use core::fmt;
use core::fmt::Write;
use core::iter::IntoIterator;
use core::marker::PhantomData;

use crate::naive::{NaiveDate, NaiveTime};
use crate::offset::{FixedOffset, Offset};
use crate::{Datelike, Timelike, Weekday};

#[cfg(feature = "unstable-locales")]
use super::locales;
use super::{Fixed, InternalFixed, InternalInternal, Item, Locale, Numeric, Pad};

#[cfg(not(feature = "unstable-locales"))]
mod locales {
    use crate::format::Locale;
    pub(crate) fn short_months(_locale: Locale) -> &'static [&'static str] {
        &["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
    }
    pub(crate) fn long_months(_locale: Locale) -> &'static [&'static str] {
        &[
            "January",
            "February",
            "March",
            "April",
            "May",
            "June",
            "July",
            "August",
            "September",
            "October",
            "November",
            "December",
        ]
    }
    pub(crate) fn short_weekdays(_locale: Locale) -> &'static [&'static str] {
        &["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
    }
    pub(crate) fn long_weekdays(_locale: Locale) -> &'static [&'static str] {
        &["Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"]
    }
    pub(crate) fn am_pm(_locale: Locale) -> &'static [&'static str] {
        &["AM", "PM"]
    }
}

/// TODO
#[derive(Clone, Debug)]
pub struct FormattingSpec<'a, I, T> {
    pub(crate) items: I,
    pub(crate) _generics: PhantomData<&'a T>,
}

/// A *temporary* object which can be used as an argument to `format!` or others.
/// This is normally constructed via `format` methods of each date and time type.
#[derive(Debug)]
pub struct Formatter<I, O> {
    /// The date view, if any.
    date: Option<NaiveDate>,
    /// The time view, if any.
    time: Option<NaiveTime>,
    /// The offset from UTC, if any
    offset: Option<O>,
    /// An iterator returning formatting items.
    items: I,
    /// Locale used for text
    /// ZST if the `unstable-locales` feature is not enabled.
    locale: Locale,
}

impl<'a, I, B, Off> Formatter<I, Off>
where
    I: Iterator<Item = B> + Clone,
    B: Borrow<Item<'a>>,
    Off: Offset + fmt::Display,
{
    /// Makes a new `Formatter` value out of local date and time and UTC offset.
    #[must_use]
    pub fn new(
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        offset: Option<Off>,
        items: I,
    ) -> Formatter<I, Off> {
        #[cfg(not(feature = "unstable-locales"))]
        let locale = Locale;
        #[cfg(feature = "unstable-locales")]
        let locale = Locale::POSIX;
        Formatter { date, time, offset, items, locale }
    }

    /// Makes a new `DelayedFormat` value out of local date and time, UTC offset and locale.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[must_use]
    pub fn new_with_locale(
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        offset: Option<Off>,
        items: I,
        locale: Locale,
    ) -> Formatter<I, Off> {
        Formatter { date, time, offset, items, locale }
    }

    #[inline]
    fn format(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for item in self.items.clone() {
            match *item.borrow() {
                Item::Literal(s) | Item::Space(s) => f.write_str(s),
                #[cfg(any(feature = "alloc", feature = "std", test))]
                Item::OwnedLiteral(ref s) | Item::OwnedSpace(ref s) => f.write_str(s),
                Item::Numeric(ref spec, ref pad) => self.format_numeric(f, &spec, &pad),
                Item::Fixed(ref spec) => self.format_fixed(f, &spec),
                Item::Error => Err(fmt::Error),
            }?;
        }
        Ok(())
    }

    fn format_numeric(&self, f: &mut fmt::Formatter, spec: &Numeric, pad: &Pad) -> fmt::Result {
        use self::Numeric::*;

        let (width, v) = match (spec, self.date, self.time) {
            (Year, Some(d), _) => (4, d.year()),
            (YearDiv100, Some(d), _) => (2, d.year().div_euclid(100)),
            (YearMod100, Some(d), _) => (2, d.year().rem_euclid(100)),
            (IsoYear, Some(d), _) => (4, d.iso_week().year()),
            (IsoYearDiv100, Some(d), _) => (2, d.iso_week().year().div_euclid(100)),
            (IsoYearMod100, Some(d), _) => (2, d.iso_week().year().rem_euclid(100)),
            (Month, Some(d), _) => (2, d.month() as i32),
            (Day, Some(d), _) => (2, d.day() as i32),
            (WeekFromSun, Some(d), _) => (2, d.weeks_from(Weekday::Sun)),
            (WeekFromMon, Some(d), _) => (2, d.weeks_from(Weekday::Mon)),
            (IsoWeek, Some(d), _) => (2, d.iso_week().week() as i32),
            (NumDaysFromSun, Some(d), _) => (1, d.weekday().num_days_from_sunday() as i32),
            (WeekdayFromMon, Some(d), _) => (1, d.weekday().number_from_monday() as i32),
            (Ordinal, Some(d), _) => (3, d.ordinal() as i32),
            (Hour, _, Some(t)) => (2, t.hour() as i32),
            (Hour12, _, Some(t)) => (2, t.hour12().1 as i32),
            (Minute, _, Some(t)) => (2, t.minute() as i32),
            (Second, _, Some(t)) => (2, (t.second() + t.nanosecond() / 1_000_000_000) as i32),
            (Nanosecond, _, Some(t)) => (9, (t.nanosecond() % 1_000_000_000) as i32),
            (Timestamp, Some(d), Some(t)) => {
                let offset =
                    self.offset.as_ref().map(|o| i64::from(o.fix().local_minus_utc())).unwrap_or(0);
                let timestamp = d.and_time(t).timestamp() - offset;
                return write!(f, "{}", timestamp);
            }
            (Internal(_), _, _) => return Ok(()), // for future expansion
            _ => return Err(fmt::Error),          // insufficient arguments for given format
        };

        if (spec == &Year || spec == &IsoYear) && !(0..10_000).contains(&v) {
            // non-four-digit years require an explicit sign as per ISO 8601
            match *pad {
                Pad::None => write!(f, "{:+}", v),
                Pad::Zero => write!(f, "{:+01$}", v, width + 1),
                Pad::Space => write!(f, "{:+1$}", v, width + 1),
            }
        } else {
            match *pad {
                Pad::None => write!(f, "{}", v),
                Pad::Zero => write!(f, "{:01$}", v, width),
                Pad::Space => write!(f, "{:1$}", v, width),
            }
        }
    }

    fn format_fixed(&self, f: &mut fmt::Formatter, spec: &Fixed) -> fmt::Result {
        use self::Fixed::*;

        macro_rules! internal_fix {
            ($x:ident) => {
                Fixed::Internal(InternalFixed { val: InternalInternal::$x })
            };
        }

        match (spec, self.date, self.time, self.offset.as_ref()) {
            (ShortMonthName, Some(d), _, _) => {
                f.write_str(locales::short_months(self.locale)[d.month0() as usize])
            }
            (LongMonthName, Some(d), _, _) => {
                f.write_str(locales::long_months(self.locale)[d.month0() as usize])
            }
            (ShortWeekdayName, Some(d), _, _) => f.write_str(
                locales::short_weekdays(self.locale)[d.weekday().num_days_from_sunday() as usize],
            ),
            (LongWeekdayName, Some(d), _, _) => f.write_str(
                locales::long_weekdays(self.locale)[d.weekday().num_days_from_sunday() as usize],
            ),
            (LowerAmPm, _, Some(t), _) => {
                let ampm = if t.hour12().0 {
                    locales::am_pm(self.locale)[1]
                } else {
                    locales::am_pm(self.locale)[0]
                };
                for c in ampm.chars().flat_map(|c| c.to_lowercase()) {
                    f.write_char(c)?
                }
                Ok(())
            }
            (UpperAmPm, _, Some(t), _) => f.write_str(if t.hour12().0 {
                locales::am_pm(self.locale)[1]
            } else {
                locales::am_pm(self.locale)[0]
            }),
            (Nanosecond, _, Some(t), _) => {
                let nano = t.nanosecond() % 1_000_000_000;
                if nano == 0 {
                    Ok(())
                } else if nano % 1_000_000 == 0 {
                    write!(f, ".{:03}", nano / 1_000_000)
                } else if nano % 1_000 == 0 {
                    write!(f, ".{:06}", nano / 1_000)
                } else {
                    write!(f, ".{:09}", nano)
                }
            }
            (Nanosecond3, _, Some(t), _) => {
                let nano = t.nanosecond() % 1_000_000_000;
                write!(f, ".{:03}", nano / 1_000_000)
            }
            (Nanosecond6, _, Some(t), _) => {
                let nano = t.nanosecond() % 1_000_000_000;
                write!(f, ".{:06}", nano / 1_000)
            }
            (Nanosecond9, _, Some(t), _) => {
                let nano = t.nanosecond() % 1_000_000_000;
                write!(f, ".{:09}", nano)
            }
            (internal_fix!(Nanosecond3NoDot), _, Some(t), _) => {
                let nano = t.nanosecond() % 1_000_000_000;
                write!(f, "{:03}", nano / 1_000_000)
            }
            (internal_fix!(Nanosecond6NoDot), _, Some(t), _) => {
                let nano = t.nanosecond() % 1_000_000_000;
                write!(f, "{:06}", nano / 1_000)
            }
            (internal_fix!(Nanosecond9NoDot), _, Some(t), _) => {
                let nano = t.nanosecond() % 1_000_000_000;
                write!(f, "{:09}", nano)
            }
            (TimezoneName, _, _, Some(off)) => write!(f, "{}", off),
            (TimezoneOffsetColon, _, _, Some(off)) => {
                write_local_minus_utc(f, off.fix(), false, Colons::Single)
            }
            (TimezoneOffsetDoubleColon, _, _, Some(off)) => {
                write_local_minus_utc(f, off.fix(), false, Colons::Double)
            }
            (TimezoneOffsetTripleColon, _, _, Some(off)) => {
                write_local_minus_utc(f, off.fix(), false, Colons::Triple)
            }
            (TimezoneOffsetColonZ, _, _, Some(off)) => {
                write_local_minus_utc(f, off.fix(), true, Colons::Single)
            }
            (TimezoneOffset, _, _, Some(off)) => {
                write_local_minus_utc(f, off.fix(), false, Colons::None)
            }
            (TimezoneOffsetZ, _, _, Some(off)) => {
                write_local_minus_utc(f, off.fix(), true, Colons::None)
            }
            (RFC2822, Some(d), Some(t), Some(off)) => {
                write_rfc2822_inner(f, &d, &t, off.fix(), self.locale)
            }
            (RFC3339, Some(d), Some(t), Some(off)) => {
                write_rfc3339_inner(f, crate::NaiveDateTime::new(d, t), off.fix())
            }
            _ => Err(fmt::Error), // insufficient arguments for given format
        }
    }
}

impl<'a, I, B, Off> fmt::Display for Formatter<I, Off>
where
    I: Iterator<Item = B> + Clone,
    B: Borrow<Item<'a>>,
    Off: Offset + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        #[cfg(any(feature = "alloc", feature = "std", test))]
        #[allow(clippy::recursive_format_impl)]
        if f.width().is_some() {
            // Justify/pad/truncate the formatted result by rendering it to a temporary `String`
            // first.
            // We skip this step if there are no 'external' formatting specifiers.
            // This is the only formatting functionality that is missing without `alloc`.
            let mut result = String::new();
            write!(result, "{}", self)?;
            return f.pad(&result);
        }
        self.format(f)
    }
}

/// Only used to make `DelayedFormat` a wrapper around `Formatter`.
#[cfg(any(feature = "alloc", feature = "std", test))]
#[derive(Clone, Debug)]
struct OffsetFormatter {
    offset: FixedOffset,
    tz_name: String,
}

#[cfg(any(feature = "alloc", feature = "std", test))]
impl Offset for OffsetFormatter {
    fn fix(&self) -> FixedOffset {
        self.offset
    }
}

#[cfg(any(feature = "alloc", feature = "std", test))]
impl fmt::Display for OffsetFormatter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.tz_name)
    }
}

/// A *temporary* object which can be used as an argument to `format!` or others.
/// This is normally constructed via `format` methods of each date and time type.
#[cfg(any(feature = "alloc", feature = "std", test))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
#[derive(Debug)]
pub struct DelayedFormat<I> {
    inner: Formatter<I, OffsetFormatter>,
}

#[cfg(any(feature = "alloc", feature = "std", test))]
impl<'a, I: Iterator<Item = B> + Clone, B: Borrow<Item<'a>>> DelayedFormat<I> {
    /// Makes a new `DelayedFormat` value out of local date and time.
    #[must_use]
    pub fn new(date: Option<NaiveDate>, time: Option<NaiveTime>, items: I) -> DelayedFormat<I> {
        DelayedFormat { inner: Formatter::new(date, time, None, items) }
    }

    /// Makes a new `DelayedFormat` value out of local date and time and UTC offset.
    #[must_use]
    pub fn new_with_offset<Off>(
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        offset: &Off,
        items: I,
    ) -> DelayedFormat<I>
    where
        Off: Offset + fmt::Display,
    {
        let offset = Some(OffsetFormatter { offset: offset.fix(), tz_name: offset.to_string() });
        DelayedFormat { inner: Formatter::new(date, time, offset, items) }
    }

    /// Makes a new `DelayedFormat` value out of local date and time and locale.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[must_use]
    pub fn new_with_locale(
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        items: I,
        locale: Locale,
    ) -> DelayedFormat<I> {
        DelayedFormat { inner: Formatter::new_with_locale(date, time, None, items, locale) }
    }

    /// Makes a new `DelayedFormat` value out of local date and time, UTC offset and locale.
    #[cfg(feature = "unstable-locales")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
    #[must_use]
    pub fn new_with_offset_and_locale<Off>(
        date: Option<NaiveDate>,
        time: Option<NaiveTime>,
        offset: &Off,
        items: I,
        locale: Locale,
    ) -> DelayedFormat<I>
    where
        Off: Offset + fmt::Display,
    {
        let offset = Some(OffsetFormatter { offset: offset.fix(), tz_name: offset.to_string() });
        DelayedFormat { inner: Formatter::new_with_locale(date, time, offset, items, locale) }
    }
}

#[cfg(any(feature = "alloc", feature = "std", test))]
impl<'a, I: Iterator<Item = B> + Clone, B: Borrow<Item<'a>>> fmt::Display for DelayedFormat<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/// Tries to format given arguments with given formatting items.
/// Internally used by `DelayedFormat`.
#[cfg(any(feature = "alloc", feature = "std", test))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
pub fn format<'a, I, B>(
    f: &mut fmt::Formatter,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    items: I,
) -> fmt::Result
where
    I: Iterator<Item = B> + Clone,
    B: Borrow<Item<'a>>,
{
    use std::fmt::Display;
    let offset = off
        .as_ref()
        .map(|(tz_name, offset)| OffsetFormatter { tz_name: tz_name.clone(), offset: *offset });
    Formatter::new(date.copied(), time.copied(), offset, items).fmt(f)
}
/// Formats single formatting item
#[cfg(any(feature = "alloc", feature = "std", test))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
pub fn format_item(
    f: &mut fmt::Formatter,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    item: &Item<'_>,
) -> fmt::Result {
    use std::fmt::Display;
    let offset = off
        .as_ref()
        .map(|(tz_name, offset)| OffsetFormatter { tz_name: tz_name.clone(), offset: *offset });
    Formatter::new(date.copied(), time.copied(), offset, [item].into_iter()).fmt(f)
}

/// Tries to format given arguments with given formatting items.
/// Internally used by `DelayedFormat`.
#[cfg(feature = "unstable-locales")]
#[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
pub fn format_localized<'a, I, B>(
    f: &mut fmt::Formatter,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    items: I,
    locale: Locale,
) -> fmt::Result
where
    I: Iterator<Item = B> + Clone,
    B: Borrow<Item<'a>>,
{
    use std::fmt::Display;
    let offset = off
        .as_ref()
        .map(|(tz_name, offset)| OffsetFormatter { tz_name: tz_name.clone(), offset: *offset });
    Formatter::new_with_locale(date.copied(), time.copied(), offset, items, locale).fmt(f)
}

/// Formats single formatting item
#[cfg(feature = "unstable-locales")]
#[cfg_attr(docsrs, doc(cfg(feature = "unstable-locales")))]
pub fn format_item_localized(
    f: &mut fmt::Formatter,
    date: Option<&NaiveDate>,
    time: Option<&NaiveTime>,
    off: Option<&(String, FixedOffset)>,
    item: &Item<'_>,
    locale: Locale,
) -> fmt::Result {
    use std::fmt::Display;
    let offset = off
        .as_ref()
        .map(|(tz_name, offset)| OffsetFormatter { tz_name: tz_name.clone(), offset: *offset });
    Formatter::new_with_locale(date.copied(), time.copied(), offset, [item].into_iter(), locale)
        .fmt(f)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Colons {
    None,
    Single,
    Double,
    Triple,
}

/// Prints an offset from UTC in the format of `+HHMM` or `+HH:MM`.
/// `Z` instead of `+00[:]00` is allowed when `allow_zulu` is true.
fn write_local_minus_utc(
    result: &mut fmt::Formatter,
    off: FixedOffset,
    allow_zulu: bool,
    colon_type: Colons,
) -> fmt::Result {
    let off = off.local_minus_utc();
    if allow_zulu && off == 0 {
        result.write_char('Z')?;
    }
    let (sign, off) = if off < 0 { ('-', -off) } else { ('+', off) };
    result.write_char(sign)?;

    write_hundreds(result, (off / 3600) as u8)?;

    match colon_type {
        Colons::None => write_hundreds(result, (off / 60 % 60) as u8),
        Colons::Single => {
            result.write_char(':')?;
            write_hundreds(result, (off / 60 % 60) as u8)
        }
        Colons::Double => {
            result.write_char(':')?;
            write_hundreds(result, (off / 60 % 60) as u8)?;
            result.write_char(':')?;
            write_hundreds(result, (off % 60) as u8)
        }
        Colons::Triple => Ok(()),
    }
}

/// Writes the date, time and offset to the string. same as `%Y-%m-%dT%H:%M:%S%.f%:z`
#[cfg(any(feature = "alloc", feature = "std", test))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
pub(crate) fn write_rfc3339(
    result: &mut String,
    dt: crate::NaiveDateTime,
    off: FixedOffset,
) -> fmt::Result {
    // reuse `Debug` impls which already print ISO 8601 format.
    // this is faster in this way.
    write!(result, "{:?}", dt)?;
    let item = [Item::Fixed(Fixed::TimezoneOffsetColon)];
    let formatter = Formatter::new(None, None, Some(off), item.iter());
    write!(result, "{}", formatter)
}

/// Writes the date, time and offset to the string. same as `%Y-%m-%dT%H:%M:%S%.f%:z`
pub(crate) fn write_rfc3339_inner(
    result: &mut fmt::Formatter,
    dt: crate::NaiveDateTime,
    off: FixedOffset,
) -> fmt::Result {
    // reuse `Debug` impls which already print ISO 8601 format.
    // this is faster in this way.
    write!(result, "{:?}", dt)?;
    write_local_minus_utc(result, off, false, Colons::Single)
}

/// write datetimes like `Tue, 1 Jul 2003 10:52:37 +0200`, same as `%a, %d %b %Y %H:%M:%S %z`
#[cfg(any(feature = "alloc", feature = "std", test))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "alloc", feature = "std"))))]
pub(crate) fn write_rfc2822(
    result: &mut String,
    dt: crate::NaiveDateTime,
    off: FixedOffset,
) -> fmt::Result {
    let item = [Item::Fixed(Fixed::RFC2822)];
    let formatter = Formatter::new(Some(dt.date()), Some(dt.time()), Some(off), item.iter());
    write!(result, "{}", formatter)
}

/// write datetimes like `Tue, 1 Jul 2003 10:52:37 +0200`, same as `%a, %d %b %Y %H:%M:%S %z`
fn write_rfc2822_inner(
    result: &mut fmt::Formatter,
    d: &NaiveDate,
    t: &NaiveTime,
    off: FixedOffset,
    locale: Locale,
) -> fmt::Result {
    let year = d.year();
    // RFC2822 is only defined on years 0 through 9999
    if !(0..=9999).contains(&year) {
        return Err(fmt::Error);
    }

    result
        .write_str(locales::short_weekdays(locale)[d.weekday().num_days_from_sunday() as usize])?;
    result.write_str(", ")?;
    write_hundreds(result, d.day() as u8)?;
    result.write_char(' ')?;
    result.write_str(locales::short_months(locale)[d.month0() as usize])?;
    result.write_char(' ')?;
    write_hundreds(result, (year / 100) as u8)?;
    write_hundreds(result, (year % 100) as u8)?;
    result.write_char(' ')?;
    write_hundreds(result, t.hour() as u8)?;
    result.write_char(':')?;
    write_hundreds(result, t.minute() as u8)?;
    result.write_char(':')?;
    let sec = t.second() + t.nanosecond() / 1_000_000_000;
    write_hundreds(result, sec as u8)?;
    result.write_char(' ')?;
    write_local_minus_utc(result, off, false, Colons::None)
}

/// Equivalent to `{:02}` formatting for n < 100.
pub(crate) fn write_hundreds(w: &mut impl Write, n: u8) -> fmt::Result {
    if n >= 100 {
        return Err(fmt::Error);
    }

    let tens = b'0' + n / 10;
    let ones = b'0' + n % 10;
    w.write_char(tens as char)?;
    w.write_char(ones as char)
}


#[test]
fn test_type_sizes() {
    use crate::format::StrftimeItems;
    use core::mem::size_of;
    assert_eq!(size_of::<DelayedFormat<StrftimeItems<'_>>>(), 88);
    assert_eq!(size_of::<DelayedFormat<std::slice::Iter<'_, Item<'_>>>>(), 72);
    assert_eq!(size_of::<Formatter<std::slice::Iter<'_, Item<'_>>, FixedOffset>>(), 48);
}
