// This is a part of Chrono.
// See README.md and LICENSE.txt for details.

//! The UTC (Coordinated Universal Time) time zone.

use core::fmt;
#[cfg(all(
    feature = "now",
    not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))
))]
use std::time::SystemTime;

#[cfg(any(feature = "rkyv", feature = "rkyv-16", feature = "rkyv-32", feature = "rkyv-64"))]
use rkyv::{Archive, Deserialize, Serialize};

use super::{FixedOffset, MappedLocalTime, Offset, TimeZone};
use crate::error::TzError;
use crate::naive::NaiveDateTime;
#[cfg(feature = "now")]
use crate::DateTime;
#[cfg(all(feature = "now", doc))]
use crate::OutOfRange;

/// The UTC time zone. This is the most efficient time zone when you don't need the local time.
/// It is also used as an offset (which is also a dummy type).
///
/// Using the [`TimeZone`](./trait.TimeZone.html) methods
/// on the UTC struct is the preferred way to construct `DateTime<Utc>`
/// instances.
///
/// # Example
///
/// ```
/// use chrono::{DateTime, TimeZone, Utc};
///
/// let dt = DateTime::from_timestamp(61, 0).unwrap();
///
/// assert_eq!(Utc.timestamp(61, 0).unwrap(), dt);
/// assert_eq!(Utc.with_ymd_and_hms(1970, 1, 1, 0, 1, 1).unwrap(), dt);
/// ```
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(
    any(feature = "rkyv", feature = "rkyv-16", feature = "rkyv-32", feature = "rkyv-64"),
    derive(Archive, Deserialize, Serialize),
    archive(compare(PartialEq)),
    archive_attr(derive(Clone, Copy, PartialEq, Eq, Debug, Hash))
)]
#[cfg_attr(feature = "rkyv-validation", archive(check_bytes))]
#[cfg_attr(all(feature = "arbitrary", feature = "std"), derive(arbitrary::Arbitrary))]
pub struct Utc;

#[cfg(feature = "now")]
impl Utc {
    /// Returns a `DateTime<Utc>` which corresponds to the current date and time in UTC.
    ///
    /// See also the similar [`Local::now()`] which returns `DateTime<Local>`, i.e. the local date
    /// and time including offset from UTC.
    ///
    /// [`Local::now()`]: crate::Local::now
    ///
    /// # Example
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// # use chrono::{FixedOffset, Utc};
    /// // Current time in UTC
    /// let now_utc = Utc::now();
    ///
    /// // Current date in UTC
    /// let today_utc = now_utc.date_naive();
    ///
    /// // Current time in some timezone (let's use +05:00)
    /// let offset = FixedOffset::east(5 * 60 * 60).unwrap();
    /// let now_with_offset = Utc::now().with_timezone(&offset);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the system clock is set to a time in the extremely distant past or future, such
    /// that it is out of the range representable by `DateTime<Utc>`. It is assumed that this
    /// crate will no longer be in use by that time.
    #[cfg(not(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    )))]
    #[must_use]
    pub fn now() -> DateTime<Utc> {
        SystemTime::now().try_into().expect(
            "system clock is set to a time extremely far into the past or future; cannot convert",
        )
    }

    /// Returns a `DateTime` which corresponds to the current date and time.
    #[cfg(all(
        target_arch = "wasm32",
        feature = "wasmbind",
        not(any(target_os = "emscripten", target_os = "wasi"))
    ))]
    #[must_use]
    pub fn now() -> DateTime<Utc> {
        let now = js_sys::Date::new_0();
        DateTime::<Utc>::from(now)
    }
}

impl TimeZone for Utc {
    type Offset = Utc;

    fn from_offset(_state: &Utc) -> Utc {
        Utc
    }

    fn offset_from_local_datetime(
        &self,
        _local: NaiveDateTime,
    ) -> Result<MappedLocalTime<Utc>, TzError> {
        Ok(MappedLocalTime::Single(Utc))
    }

    fn offset_from_utc_datetime(&self, _utc: NaiveDateTime) -> Result<Utc, TzError> {
        Ok(Utc)
    }
}

impl Offset for Utc {
    fn fix(&self) -> FixedOffset {
        FixedOffset::east(0).unwrap()
    }
}

impl fmt::Debug for Utc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Z")
    }
}

impl fmt::Display for Utc {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "UTC")
    }
}
