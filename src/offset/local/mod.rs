// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The local (system) time zone.

#[cfg(windows)]
use std::cmp::Ordering;

#[cfg(any(feature = "rkyv", feature = "rkyv-16", feature = "rkyv-32", feature = "rkyv-64"))]
use rkyv::{Archive, Deserialize, Serialize};

use super::fixed::FixedOffset;
use super::{LocalResult, TimeZone};
use crate::{DateTime, NaiveDateTime, Utc};

#[cfg(unix)]
#[path = "unix.rs"]
mod inner;

#[cfg(windows)]
#[path = "windows.rs"]
mod inner;

#[cfg(all(windows, feature = "clock"))]
#[allow(unreachable_pub)]
mod win_bindings;

#[cfg(all(
    not(unix),
    not(windows),
    not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))
))]
mod inner {
    use crate::{FixedOffset, LocalResult, NaiveDateTime};

    pub(super) fn offset_from_utc_datetime(_utc_time: &NaiveDateTime) -> LocalResult<FixedOffset> {
        LocalResult::Single(FixedOffset::east(0).unwrap())
    }

    pub(super) fn offset_from_local_datetime(
        _local_time: &NaiveDateTime,
    ) -> LocalResult<FixedOffset> {
        LocalResult::Single(FixedOffset::east(0).unwrap())
    }
}

#[cfg(all(
    target_arch = "wasm32",
    feature = "wasmbind",
    not(any(target_os = "emscripten", target_os = "wasi"))
))]
mod inner {
    use crate::{Datelike, FixedOffset, LocalResult, NaiveDateTime, Timelike};

    pub(super) fn offset_from_utc_datetime(utc: &NaiveDateTime) -> LocalResult<FixedOffset> {
        let offset = js_sys::Date::from(utc.and_utc()).get_timezone_offset();
        LocalResult::Single(FixedOffset::west((offset as i32) * 60).unwrap())
    }

    pub(super) fn offset_from_local_datetime(local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        let mut year = local.year();
        if year < 100 {
            // The API in `js_sys` does not let us create a `Date` with negative years.
            // And values for years from `0` to `99` map to the years `1900` to `1999`.
            // Shift the value by a multiple of 400 years until it is `>= 100`.
            let shift_cycles = (year - 100).div_euclid(400);
            year -= shift_cycles * 400;
        }
        let js_date = js_sys::Date::new_with_year_month_day_hr_min_sec(
            year as u32,
            local.month0() as i32,
            local.day() as i32,
            local.hour() as i32,
            local.minute() as i32,
            local.second() as i32,
            // ignore milliseconds, our representation of leap seconds may be problematic
        );
        let offset = js_date.get_timezone_offset();
        // We always get a result, even if this time does not exist or is ambiguous.
        LocalResult::Single(FixedOffset::west((offset as i32) * 60).unwrap())
    }
}

#[cfg(unix)]
mod tz_info;

/// The local timescale.
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on the Local struct is the preferred way to construct `DateTime<Local>`
/// instances.
///
/// # Example
///
/// ```
/// use chrono::{Local, DateTime, TimeZone};
///
/// let dt1: DateTime<Local> = Local::now();
/// let dt2: DateTime<Local> = Local.timestamp(0, 0).unwrap();
/// assert!(dt1 >= dt2);
/// ```
#[derive(Copy, Clone, Debug)]
#[cfg_attr(
    any(feature = "rkyv", feature = "rkyv-16", feature = "rkyv-32", feature = "rkyv-64"),
    derive(Archive, Deserialize, Serialize),
    archive(compare(PartialEq)),
    archive_attr(derive(Clone, Copy, Debug))
)]
#[cfg_attr(feature = "rkyv-validation", archive(check_bytes))]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct Local;

impl Local {
    /// Returns a `DateTime<Local>` which corresponds to the current date, time and offset from
    /// UTC.
    ///
    /// See also the similar [`Utc::now()`] which returns `DateTime<Utc>`, i.e. without the local
    /// offset.
    ///
    /// # Example
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// # use chrono::{DateTime, FixedOffset, Local};
    /// // Current local time
    /// let now = Local::now();
    ///
    /// // Current local date
    /// let today = now.date_naive();
    ///
    /// // Current local time, converted to `DateTime<FixedOffset>`
    /// let now_fixed_offset = Local::now().fixed_offset();
    /// // or
    /// let now_fixed_offset: DateTime<FixedOffset> = Local::now().into();
    ///
    /// // Current time in some timezone (let's use +05:00)
    /// // Note that it is usually more efficient to use `Utc::now` for this use case.
    /// let offset = FixedOffset::east(5 * 60 * 60).unwrap();
    /// let now_with_offset = Local::now().with_timezone(&offset);
    /// ```
    pub fn now() -> DateTime<Local> {
        Utc::now().with_timezone(&Local)
    }
}

impl TimeZone for Local {
    type Offset = FixedOffset;

    fn from_offset(_offset: &FixedOffset) -> Local {
        Local
    }

    fn offset_from_local_datetime(&self, local: &NaiveDateTime) -> LocalResult<FixedOffset> {
        inner::offset_from_local_datetime(local)
    }

    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> FixedOffset {
        inner::offset_from_utc_datetime(utc).unwrap()
    }
}

#[cfg(windows)]
#[derive(Copy, Clone, Eq, PartialEq)]
struct Transition {
    transition_utc: NaiveDateTime,
    offset_before: FixedOffset,
    offset_after: FixedOffset,
}

#[cfg(windows)]
impl Transition {
    fn new(
        transition_local: NaiveDateTime,
        offset_before: FixedOffset,
        offset_after: FixedOffset,
    ) -> Transition {
        // It is no problem if the transition time in UTC falls a couple of hours inside the buffer
        // space around the `NaiveDateTime` range (although it is very theoretical to have a
        // transition at midnight around `NaiveDate::(MIN|MAX)`.
        let transition_utc = transition_local.overflowing_sub_offset(offset_before);
        Transition { transition_utc, offset_before, offset_after }
    }
}

#[cfg(windows)]
impl PartialOrd for Transition {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.transition_utc.cmp(&other.transition_utc))
    }
}

#[cfg(windows)]
impl Ord for Transition {
    fn cmp(&self, other: &Self) -> Ordering {
        self.transition_utc.cmp(&other.transition_utc)
    }
}

// Calculate the time in UTC given a local time and transitions.
// `transitions` must be sorted.
#[cfg(windows)]
fn lookup_with_dst_transitions(
    transitions: &[Transition],
    dt: NaiveDateTime,
) -> LocalResult<FixedOffset> {
    for t in transitions.iter() {
        // A transition can result in the wall clock time going forward (creating a gap) or going
        // backward (creating a fold). We are interested in the earliest and latest wall time of the
        // transition, as this are the times between which `dt` does may not exist or is ambiguous.
        //
        // It is no problem if the transition times falls a couple of hours inside the buffer
        // space around the `NaiveDateTime` range (although it is very theoretical to have a
        // transition at midnight around `NaiveDate::(MIN|MAX)`.
        let (offset_min, offset_max) =
            match t.offset_after.local_minus_utc() > t.offset_before.local_minus_utc() {
                true => (t.offset_before, t.offset_after),
                false => (t.offset_after, t.offset_before),
            };
        let wall_earliest = t.transition_utc.overflowing_add_offset(offset_min);
        let wall_latest = t.transition_utc.overflowing_add_offset(offset_max);

        if dt < wall_earliest {
            return LocalResult::Single(t.offset_before);
        } else if dt <= wall_latest {
            return match t.offset_after.local_minus_utc().cmp(&t.offset_before.local_minus_utc()) {
                Ordering::Equal => LocalResult::Single(t.offset_before),
                Ordering::Less => LocalResult::Ambiguous(t.offset_before, t.offset_after),
                Ordering::Greater => {
                    if dt == wall_earliest {
                        LocalResult::Single(t.offset_before)
                    } else if dt == wall_latest {
                        LocalResult::Single(t.offset_after)
                    } else {
                        LocalResult::None
                    }
                }
            };
        }
    }
    LocalResult::Single(transitions.last().unwrap().offset_after)
}

#[cfg(test)]
mod tests {
    use super::Local;
    #[cfg(windows)]
    use crate::offset::local::{lookup_with_dst_transitions, Transition};
    use crate::offset::TimeZone;
    use crate::{Datelike, TimeDelta, Utc};
    #[cfg(windows)]
    use crate::{FixedOffset, LocalResult, NaiveDate, NaiveDateTime};

    #[test]
    fn verify_correct_offsets() {
        let now = Local::now();
        let from_local = Local.from_local_datetime(&now.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&now.naive_utc());

        assert_eq!(now.offset().local_minus_utc(), from_local.offset().local_minus_utc());
        assert_eq!(now.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(now, from_local);
        assert_eq!(now, from_utc);
    }

    #[test]
    fn verify_correct_offsets_distant_past() {
        let distant_past = Local::now() - TimeDelta::days(365 * 500);
        let from_local = Local.from_local_datetime(&distant_past.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&distant_past.naive_utc());

        assert_eq!(distant_past.offset().local_minus_utc(), from_local.offset().local_minus_utc());
        assert_eq!(distant_past.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(distant_past, from_local);
        assert_eq!(distant_past, from_utc);
    }

    #[test]
    fn verify_correct_offsets_distant_future() {
        let distant_future = Local::now() + TimeDelta::days(365 * 35000);
        let from_local = Local.from_local_datetime(&distant_future.naive_local()).unwrap();
        let from_utc = Local.from_utc_datetime(&distant_future.naive_utc());

        assert_eq!(
            distant_future.offset().local_minus_utc(),
            from_local.offset().local_minus_utc()
        );
        assert_eq!(distant_future.offset().local_minus_utc(), from_utc.offset().local_minus_utc());

        assert_eq!(distant_future, from_local);
        assert_eq!(distant_future, from_utc);
    }

    #[test]
    fn test_local_date_sanity_check() {
        // issue #27
        assert_eq!(Local.with_ymd_and_hms(2999, 12, 28, 0, 0, 0).unwrap().day(), 28);
    }

    #[test]
    fn test_leap_second() {
        // issue #123
        let today = Utc::now().date_naive();

        if let Ok(dt) = today.and_hms_milli_opt(15, 2, 59, 1000) {
            let timestr = dt.time().to_string();
            // the OS API may or may not support the leap second,
            // but there are only two sensible options.
            assert!(
                timestr == "15:02:60" || timestr == "15:03:00",
                "unexpected timestr {:?}",
                timestr
            );
        }

        if let Ok(dt) = today.and_hms_milli_opt(15, 2, 3, 1234) {
            let timestr = dt.time().to_string();
            assert!(
                timestr == "15:02:03.234" || timestr == "15:02:04.234",
                "unexpected timestr {:?}",
                timestr
            );
        }
    }

    #[test]
    #[cfg(windows)]
    fn test_lookup_with_dst_transitions() {
        let ymdhms =
            |y, m, d, h, n, s| NaiveDate::from_ymd(y, m, d).unwrap().and_hms(h, n, s).unwrap();

        #[track_caller]
        #[allow(clippy::too_many_arguments)]
        fn compare_lookup(
            transitions: &[Transition],
            y: i32,
            m: u32,
            d: u32,
            h: u32,
            n: u32,
            s: u32,
            result: LocalResult<FixedOffset>,
        ) {
            let dt = NaiveDate::from_ymd(y, m, d).unwrap().and_hms(h, n, s).unwrap();
            assert_eq!(lookup_with_dst_transitions(transitions, dt), result);
        }

        // dst transition before std transition
        // dst offset > std offset
        let std = FixedOffset::east(3 * 60 * 60).unwrap();
        let dst = FixedOffset::east(4 * 60 * 60).unwrap();
        let transitions = [
            Transition::new(ymdhms(2023, 3, 26, 2, 0, 0), std, dst),
            Transition::new(ymdhms(2023, 10, 29, 3, 0, 0), dst, std),
        ];
        compare_lookup(&transitions, 2023, 3, 26, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 3, 26, 2, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 3, 26, 2, 30, 0, LocalResult::None);
        compare_lookup(&transitions, 2023, 3, 26, 3, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 3, 26, 4, 0, 0, LocalResult::Single(dst));

        compare_lookup(&transitions, 2023, 10, 29, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 10, 29, 2, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 10, 29, 2, 30, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 10, 29, 3, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 10, 29, 4, 0, 0, LocalResult::Single(std));

        // std transition before dst transition
        // dst offset > std offset
        let std = FixedOffset::east(-5 * 60 * 60).unwrap();
        let dst = FixedOffset::east(-4 * 60 * 60).unwrap();
        let transitions = [
            Transition::new(ymdhms(2023, 3, 24, 3, 0, 0), dst, std),
            Transition::new(ymdhms(2023, 10, 27, 2, 0, 0), std, dst),
        ];
        compare_lookup(&transitions, 2023, 3, 24, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 3, 24, 2, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 3, 24, 2, 30, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 3, 24, 3, 0, 0, LocalResult::Ambiguous(dst, std));
        compare_lookup(&transitions, 2023, 3, 24, 4, 0, 0, LocalResult::Single(std));

        compare_lookup(&transitions, 2023, 10, 27, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 10, 27, 2, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 10, 27, 2, 30, 0, LocalResult::None);
        compare_lookup(&transitions, 2023, 10, 27, 3, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 10, 27, 4, 0, 0, LocalResult::Single(dst));

        // dst transition before std transition
        // dst offset < std offset
        let std = FixedOffset::east(3 * 60 * 60).unwrap();
        let dst = FixedOffset::east((2 * 60 + 30) * 60).unwrap();
        let transitions = [
            Transition::new(ymdhms(2023, 3, 26, 2, 30, 0), std, dst),
            Transition::new(ymdhms(2023, 10, 29, 2, 0, 0), dst, std),
        ];
        compare_lookup(&transitions, 2023, 3, 26, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 3, 26, 2, 0, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 3, 26, 2, 15, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 3, 26, 2, 30, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 3, 26, 3, 0, 0, LocalResult::Single(dst));

        compare_lookup(&transitions, 2023, 10, 29, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 10, 29, 2, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 10, 29, 2, 15, 0, LocalResult::None);
        compare_lookup(&transitions, 2023, 10, 29, 2, 30, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 10, 29, 3, 0, 0, LocalResult::Single(std));

        // std transition before dst transition
        // dst offset < std offset
        let std = FixedOffset::east(-(4 * 60 + 30) * 60).unwrap();
        let dst = FixedOffset::east(-5 * 60 * 60).unwrap();
        let transitions = [
            Transition::new(ymdhms(2023, 3, 24, 2, 0, 0), dst, std),
            Transition::new(ymdhms(2023, 10, 27, 2, 30, 0), std, dst),
        ];
        compare_lookup(&transitions, 2023, 3, 24, 1, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 3, 24, 2, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 3, 24, 2, 15, 0, LocalResult::None);
        compare_lookup(&transitions, 2023, 3, 24, 2, 30, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 3, 24, 3, 0, 0, LocalResult::Single(std));

        compare_lookup(&transitions, 2023, 10, 27, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 10, 27, 2, 0, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 10, 27, 2, 15, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 10, 27, 2, 30, 0, LocalResult::Ambiguous(std, dst));
        compare_lookup(&transitions, 2023, 10, 27, 3, 0, 0, LocalResult::Single(dst));

        // offset stays the same
        let std = FixedOffset::east(3 * 60 * 60).unwrap();
        let transitions = [
            Transition::new(ymdhms(2023, 3, 26, 2, 0, 0), std, std),
            Transition::new(ymdhms(2023, 10, 29, 3, 0, 0), std, std),
        ];
        compare_lookup(&transitions, 2023, 3, 26, 2, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 10, 29, 3, 0, 0, LocalResult::Single(std));

        // single transition
        let std = FixedOffset::east(3 * 60 * 60).unwrap();
        let dst = FixedOffset::east(4 * 60 * 60).unwrap();
        let transitions = [Transition::new(ymdhms(2023, 3, 26, 2, 0, 0), std, dst)];
        compare_lookup(&transitions, 2023, 3, 26, 1, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 3, 26, 2, 0, 0, LocalResult::Single(std));
        compare_lookup(&transitions, 2023, 3, 26, 2, 30, 0, LocalResult::None);
        compare_lookup(&transitions, 2023, 3, 26, 3, 0, 0, LocalResult::Single(dst));
        compare_lookup(&transitions, 2023, 3, 26, 4, 0, 0, LocalResult::Single(dst));
    }

    #[test]
    #[cfg(windows)]
    fn test_lookup_with_dst_transitions_limits() {
        // Transition beyond UTC year end doesn't panic in year of `NaiveDate::MAX`
        let std = FixedOffset::east(3 * 60 * 60).unwrap();
        let dst = FixedOffset::east(4 * 60 * 60).unwrap();
        let transitions = [
            Transition::new(NaiveDateTime::MAX.with_month(7).unwrap(), std, dst),
            Transition::new(NaiveDateTime::MAX, dst, std),
        ];
        assert_eq!(
            lookup_with_dst_transitions(&transitions, NaiveDateTime::MAX.with_month(3).unwrap()),
            LocalResult::Single(std)
        );
        assert_eq!(
            lookup_with_dst_transitions(&transitions, NaiveDateTime::MAX.with_month(8).unwrap()),
            LocalResult::Single(dst)
        );
        // Doesn't panic with `NaiveDateTime::MAX` as argument (which would be out of range when
        // converted to UTC).
        assert_eq!(
            lookup_with_dst_transitions(&transitions, NaiveDateTime::MAX),
            LocalResult::Ambiguous(dst, std)
        );

        // Transition before UTC year end doesn't panic in year of `NaiveDate::MIN`
        let std = FixedOffset::west(3 * 60 * 60).unwrap();
        let dst = FixedOffset::west(4 * 60 * 60).unwrap();
        let transitions = [
            Transition::new(NaiveDateTime::MIN, std, dst),
            Transition::new(NaiveDateTime::MIN.with_month(6).unwrap(), dst, std),
        ];
        assert_eq!(
            lookup_with_dst_transitions(&transitions, NaiveDateTime::MIN.with_month(3).unwrap()),
            LocalResult::Single(dst)
        );
        assert_eq!(
            lookup_with_dst_transitions(&transitions, NaiveDateTime::MIN.with_month(8).unwrap()),
            LocalResult::Single(std)
        );
        // Doesn't panic with `NaiveDateTime::MIN` as argument (which would be out of range when
        // converted to UTC).
        assert_eq!(
            lookup_with_dst_transitions(&transitions, NaiveDateTime::MIN),
            LocalResult::Ambiguous(std, dst)
        );
    }

    #[test]
    #[cfg(feature = "rkyv-validation")]
    fn test_rkyv_validation() {
        let local = Local;
        // Local is a ZST and serializes to 0 bytes
        let bytes = rkyv::to_bytes::<_, 0>(&local).unwrap();
        assert_eq!(bytes.len(), 0);

        // but is deserialized to an archived variant without a
        // wrapping object
        assert_eq!(rkyv::from_bytes::<Local>(&bytes).unwrap(), super::ArchivedLocal);
    }
}
