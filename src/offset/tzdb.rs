use std::cmp::{Ord, Ordering};
use std::num::NonZeroU32;
use std::str;

use crate::{expect, Datelike, Days, FixedOffset, NaiveDate, NaiveDateTime, NaiveTime, Weekday, Timelike};

struct TimeZone(&'static [TzChange]);

#[derive(Clone, Debug, Default)]
struct TzChange {
    date: Option<NaiveDate>,
    time: u32, // range 0..86400
    local_minus_utc: i32,
    rules_or_offset: RulesOrOffset,
}

const fn new(
    ymd_time_offset: (i32, u32, u32, u32, i32),
    rules_or_offset: RulesOrOffset,
) -> TzChange {
    let date = match (ymd_time_offset.0, ymd_time_offset.1, ymd_time_offset.2) {
        (0, 0, 0) => None,
        (y, m, d) => Some(expect!(NaiveDate::from_ymd_opt(y, m, d), "invalid date")),
    };
    let time = ymd_time_offset.3;
    let local_minus_utc = ymd_time_offset.4;
    TzChange { date, time, local_minus_utc, rules_or_offset }
}

const fn change(
    ymd_time_offset: (i32, u32, u32, u32, i32),
    offset: (i32, &str, bool)
) -> TzChange {
    TzChange::default()
}

const fn rule(
    ymd_time_offset: (DateSpec, u32, i32),
    offset: (i32, &str, bool)
) -> TzChange {
    TzChange::default()
}

#[derive(Copy, Clone, Debug)]
enum DateSpec {
    MonthDay(u8, u8),            // month, day
    Last(u8, Weekday),           // month, weekday
    OnOrBefore(u8, Weekday, u8), // month, weekday, day
    OnOrAfter(u8, Weekday, u8),  // month, weekday, day
}

impl DateSpec {
    fn cmp_in_year(self, rhs: NaiveDate) -> Ordering {
        let year = rhs.year();
        match self {
            MonthDay(m, d) => {
                let rhs_mdf = rhs.mdf().0;
                let flags = rhs_mdf & 0b1111;
                let lhs_mdf = ((m as u32) << 9) | ((d as u32) << 4) | flags;
                // TODO: validate rhs_mdf
                lhs_mdf.cmp(&rhs_mdf)
            }
            Last(_, _) => todo!(),
            OnOrBefore(_, _, _) => {
                // assume this is on or before December 25
                todo!()
            }
            OnOrAfter(m, wd, d) => {
                // assume this is after January 6
                let on_or_after = NaiveDate::from_ymd_opt(rhs.year(), m as u32, d as u32).unwrap();
                if on_or_after < rhs {
                    return Ordering::Less;
                } else if on_or_after + Days(7) >= rhs {
                    return Ordering::Greater;
                }
                todo!()
            }
        }
    }
}

use crate::Weekday::*;
use DateSpec::*;

#[derive(Clone, Debug)]
enum RulesOrOffset {
    Rules([((DateSpec, i32, i32), (i32, &'static str, bool)); 2]), // (date rule, local time, offset), (offset, name, dst)
    Offset(i32, &'static str, bool),                               // (offset, name, dst)
}
use RulesOrOffset::*;

const EUROPE_AMSTERDAM: &'static [TzChange] = &[
    rule((Last(3, Sun), 7200, 3600), (7200, "CEST", true)),
    rule((Last(10, Sun), 10800, 7200), (3600, "CET", true)),
    change((1996, 3, 29, 7200, 3600), (7200, "CEST", true)),
    rule((Last(3, Sun), 7200, 3600), (7200, "CEST", true)),
    rule((Last(9, Sun), 10800, 7200), (3600, "CET", true)),
    change((1981, 3, 29, 7200, 3600), (7200, "CEST", true)),
    rule((OnOrAfter(4, Sun, 1), 7200, 3600), (7200, "CEST", true)),
    rule((Last(9, Sun), 10800, 7200), (3600, "CET", true)),
    change((1979, 4, 1, 7200, 3600), (7200, "CEST", true)),
    change((1978, 10, 1, 10800, 7200), (3600, "CET", false)),
    change((1978, 4, 2, 7200, 3600), (7200, "CEST", true)),
    change((1977, 9, 25, 10800, 7200), (3600, "CET", false)),
    change((1977, 4, 3, 7200, 3600), (7200, "CEST", true)),
    change((1945, 9, 16, 10800, 7200), (3600, "CET", false)),
    change((1945, 4, 2, 7200, 3600), (7200, "CEST", true)),
    change((1944, 10, 2, 10800, 7200), (3600, "CET", false)),
    change((1944, 4, 3, 7200, 3600), (7200, "CEST", true)),
    change((1943, 10, 4, 10800, 7200), (3600, "CET", false)),
    change((1943, 3, 29, 7200, 3600), (7200, "CEST", true)),
    change((1942, 11, 2, 10800, 7200), (3600, "CET", false)),
    change((1940, 5, 16, 0, 1200), (7200, "CEST", true)),
    change((1939, 10, 8, 10800, 4800), (1200, "+0020", false)), // inserted because the next transition is later
    rule((MonthDay(5, 15), 7200, 1200), (4800, "+0120", true)),
    rule((OnOrAfter(10, Sun, 2), 10800, 4800), (1200, "+0020", false)),
    change((1937, 7, 1, 0, 4772), (4800, "+0120", true)),
    change((1937, 5, 22, 7200, 1172), (4772, "NST", true)), // a week later
    change((1936, 10, 4, 10800, 4772), (1172, "AMT", false)), // inserted because the next transition is later
    rule((MonthDay(5, 15), 7200, 1172), (4772, "NST", true)),
    rule((OnOrAfter(10, Sun, 2), 10800, 4772), (1172, "AMT", false)),
    change((1932, 10, 2, 10800, 4772), (1172, "AMT", false)),
    change((1932, 5, 22, 7200, 1172), (4772, "NST", true)),   // a week later
    change((1931, 10, 4, 10800, 4772), (1172, "AMT", false)), // inserted because the next transition is later
    rule((MonthDay(5, 15), 7200, 1172), (4772, "NST", true)),
    rule((OnOrAfter(10, Sun, 2), 10800, 4772), (1172, "AMT", false)),
    change((1926, 5, 15, 7200, 1172), (4772, "NST", true)),
    change((1925, 10, 4, 10800, 4772), (1172, "AMT", false)),
    change((1925, 6, 5, 7200, 1172), (4772, "NST", true)),
    change((1924, 10, 5, 10800, 4772), (1172, "AMT", false)),
    change((1924, 3, 30, 7200, 1172), (4772, "NST", true)),
    change((1923, 10, 7, 10800, 4772), (1172, "AMT", false)),
    change((1923, 6, 1, 7200, 1172), (4772, "NST", true)),
    change((1922, 10, 8, 10800, 4772), (1172, "AMT", false)),
    change((1922, 3, 26, 7200, 1172), (4772, "NST", true)),
    rule((OnOrAfter(4, Mon, 1), 7200, 1172), (4772, "NST", true)),
    rule((Last(9, Mon), 10800, 4772), (1172, "AMT", false)),
    change((1918, 4, 1, 7200, 1172), (4772, "NST", true)),
    change((1917, 9, 17, 10800, 4772), (1172, "AMT", false)),
    change((1917, 4, 16, 7200, 1172), (4772, "NST", true)),
    change((1916, 10, 1, 0, 4772), (1172, "AMT", false)),
    change((1916, 5, 1, 0, 1172), (4772, "NST", true)),
    change((1835, 5, 1, 0, 1172), (1172, "AMT", false)), // can we calculate this line?
    change((0, 0, 0, 0, 0), (1172, "LMT", false)),
];

fn offset_from_local_datetime(tz: &[TzChange], dt: NaiveDateTime) {
    let date = dt.date();
    let time = dt.time().num_seconds_from_midnight();

    for tz_change in tz {
        match Some(date).cmp(&tz_change.date) {
            Ordering::Less => continue,
            Ordering::Equal => if time < tz_change.time { continue },
            Ordering::Greater => {},
        }
        dbg!(tz_change);
        return;
    }
}

#[test]
fn test_tz_change() {
    use crate::{Utc, Duration};
    let mut dt = Utc::now().naive_local();
    while dt.year() > 1800 {
        eprint!("{}", dt);
        offset_from_local_datetime(EUROPE_AMSTERDAM, dt);
        dt = dt - Duration::days(365);
    }
    panic!();
}