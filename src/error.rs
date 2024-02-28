//! Error type
use core::fmt;

/// Error type for date and time operations.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// A date or datetime does not exist.
    ///
    /// Examples are:
    /// - April 31,
    /// - February 29 in a non-leap year,
    /// - a time that falls in the gap created by moving the clock forward during a DST transition,
    /// - a leap second on a non-minute boundary.
    DoesNotExist,

    /// One or more of the arguments to a function are invalid.
    ///
    /// An example is creating a `NaiveTime` with 25 as the hour value.
    InvalidArgument,

    /// The result, or an intermediate value necessary for calculating a result, would be out of
    /// range.
    ///
    /// An example is a date for the year 500.000, which is out of the range supported by chrono's
    /// types.
    OutOfRange,

    /// Lookup of a local datetime in a timezone failed.
    TzFailure(TzError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::DoesNotExist => write!(f, "date or datetime does not exist"),
            Error::InvalidArgument => write!(f, "invalid parameter"),
            Error::OutOfRange => write!(f, "date outside of the supported range"),
            Error::TzFailure(_) => write!(f, "time zone lookup failure"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::TzFailure(e) => Some(e),
            _ => None,
        }
    }
}

/// Error type for time zone lookups.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum TzError {
    /// Unable to determine the local time zone of the os/platform.
    TimeZoneUnknown,

    /// Error returned by a platform API.
    OsError(OsError),

    /// `TZ` environment variable set to an invalid value.
    InvalidTzString,

    /// Unable to locate an IANA time zone database.
    NoTzdb,

    /// The specified time zone is not found (in the database).
    TimeZoneNotFound,

    /// There is an error when reading/validating the time zone data.
    InvalidTimeZoneData,

    /// The result would be out of range.
    OutOfRange,
}

impl fmt::Display for TzError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            TzError::TimeZoneUnknown => "unable to determine the local time zone",
            TzError::OsError(_) => "platform API error",
            TzError::InvalidTzString => "`TZ` environment variable set to an invalid value",
            TzError::NoTzdb => "unable to locate an IANA time zone database",
            TzError::TimeZoneNotFound => "the specified time zone is not found",
            TzError::InvalidTimeZoneData => "error when reading/validating the time zone data",
            TzError::OutOfRange => "datetime outside of the supported range",
        })
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TzError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            TzError::OsError(os_error) => Some(os_error),
            _ => None,
        }
    }
}

impl From<TzError> for Error {
    fn from(error: TzError) -> Self {
        match error {
            TzError::OutOfRange => Error::OutOfRange,
            e => Error::TzFailure(e),
        }
    }
}

impl From<OsError> for TzError {
    fn from(error: OsError) -> Self {
        TzError::OsError(error)
    }
}

/// Error that originates from the underlying OS/platform APIs.
//
// We encode an `i32` as two `u16`s in order to give this type an alignment of 2.
// This will cause the size of `TzError` to become 6 bytes instead of 8, and `Error` to be 8 bytes
// instead of 12.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct OsError(u16, u16);

impl fmt::Display for OsError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&std::io::Error::from(*self), f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for OsError {}

impl OsError {
    /// Create a new `OsError` with the last OS error.
    pub fn last() -> Self {
        let raw = std::io::Error::last_os_error().raw_os_error().unwrap();
        OsError((raw >> 16) as u16, raw as u16)
    }
}

#[cfg(feature = "std")]
impl From<OsError> for std::io::Error {
    fn from(error: OsError) -> Self {
        let raw = ((error.0 as u32) << 16 | error.1 as u32) as i32;
        std::io::Error::from_raw_os_error(raw)
    }
}
