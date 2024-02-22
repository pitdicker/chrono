//! Error type
use core::fmt;

use crate::offset::TzLookupError;

/// Error type for date and time operations.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// There is not enough information to create a date/time.
    ///
    /// An example is parsing a string with not enough date/time fields, or the result of a
    /// time that is ambiguous during a time zone transition (due to for example DST).
    Ambiguous,

    /// A date or datetime does not exist.
    ///
    /// Examples are:
    /// - April 31,
    /// - February 29 in a non-leap year,
    /// - a time that falls in the gap created by moving the clock forward during a DST transition,
    /// - a leap second on a non-minute boundary.
    DoesNotExist,

    /// Some of the date or time components are not consistent with each other.
    ///
    /// An example is parsing 'Sunday 2023-04-21', while that date is a Friday.
    Inconsistent,

    /// One or more of the arguments to a function are invalid.
    ///
    /// An example is creating a `NaiveTime` with 25 as the hour value.
    InvalidArgument,

    /// Character does not match with the expected format (during parsing).
    ///
    /// Contains the byte index of the character where the input diverges.
    InvalidCharacter(u32),

    /// Value is not allowed by the format (during parsing).
    ///
    /// Examples are a number that is larger or smaller than the defined range, or the name of a
    /// weekday, month or timezone that doesn't match.
    ///
    /// Contains the byte index pointing at the start of the invalid value.
    InvalidValue(u32, u8),

    /// The result, or an intermediate value necessary for calculating a result, would be out of
    /// range.
    ///
    /// An example is a date for the year 500.000, which is out of the range supported by chrono's
    /// types.
    OutOfRange,

    /// All formatting items have been read but there is a remaining input.
    TooLong,

    /// Lookup of a local datetime in a timezone failed.
    TzLookupFailure(TzLookupError),

    /// The format string contains a formatting specifier that is not supported.
    ///
    /// Contains the byte index of the formatting specifier within the format string.
    UnsupportedSpecifier(u32),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Ambiguous => write!(f, "not enough information for a unique date and time"),
            Error::DoesNotExist => write!(f, "date or datetime does not exist"),
            Error::Inconsistent => {
                write!(f, "some of the date or time components are not consistent with each other")
            }
            Error::InvalidArgument => write!(f, "invalid parameter"),
            Error::InvalidCharacter(i) => {
                write!(f, "input doesn't match with the expected format at position {}", i)
            }
            Error::InvalidValue(i, len) => {
                write!(f, "input has a value not allowed by the format at position {} with len {}", i, len)
            }
            Error::OutOfRange => write!(f, "date outside of the supported range"),
            Error::TooLong => write!(f, "trailing input"),
            Error::TzLookupFailure(_) => write!(f, "time zone lookup failure"),
            Error::UnsupportedSpecifier(_) => {
                write!(f, "format string contains a formatting specifier that is not supported")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error  {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::TzLookupFailure(e) => Some(e),
            _ => None,
        }
    }
}

/// Error type for time zone lookups.
#[non_exhaustive]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum TzLookupError {
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

impl fmt::Display for TzLookupError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TzLookupError::TimeZoneUnknown => write!(f, "unable to determine the local time zone"),
            TzLookupError::OsError(_) => write!(f, "platform API error"),
            TzLookupError::InvalidTzString => {
                write!(f, "`TZ` environment variable set to an invalid value")
            }
            TzLookupError::NoTzdb => write!(f, "unable to locate an IANA time zone database"),
            TzLookupError::TimeZoneNotFound => write!(f, "the specified time zone is not found"),
            TzLookupError::InvalidTimeZoneData => {
                write!(f, "error when reading/validating the time zone data")
            }
            TzLookupError::OutOfRange => write!(f, "date or offset outside of the supported range"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TzLookupError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            TzLookupError::OsError(os_error) => Some(os_error),
            _ => None,
        }
    }
}

impl From<TzLookupError> for Error {
    fn from(error: TzLookupError) -> Self {
        Error::TzLookupFailure(error)
    }
}

impl TzLookupError {
    /// TODO
    pub fn last_os_error() -> Self {
        let raw = std::io::Error::last_os_error().raw_os_error().unwrap();
        TzLookupError::OsError(OsError((raw >> 16) as u16, raw as u16))
    }
}

impl From<OsError> for TzLookupError {
    fn from(error: OsError) -> Self {
        TzLookupError::OsError(error)
    }
}

/// Error that originates from the underlying OS/platform APIs.
//
// We encode an `i32` as two `u16`s, in order to give this type an alignment of 2.
// This will cause the size of `TzLookupError` to become 6 bytes instead of 8, and `Error` to be
// 8 bytes instead of 12.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct OsError(u16, u16);

impl fmt::Display for OsError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&std::io::Error::from(*self), f)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for OsError {}

#[cfg(feature = "std")]
impl From<OsError> for std::io::Error {
    fn from(error: OsError) -> Self {
        let raw = ((error.0 as u32) << 16 | error.1 as u32) as i32;
        std::io::Error::from_raw_os_error(raw)
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error as StdError;

    use crate::error::{Error, OsError, TzLookupError};

    #[test]
    fn test_error_size() {
        use core::mem::size_of;
        assert_eq!(size_of::<TzLookupError>(), 6);
        assert_eq!(size_of::<Error>(), 8);
        assert_eq!(size_of::<Option<TzLookupError>>(), 6);
        assert_eq!(size_of::<Option<Error>>(), 8);
    }

    #[test]
    fn test_error_msg() {
        let err = Error::TzLookupFailure(TzLookupError::OsError(OsError(0, 2)));
        println!("Error: {}", err);
        if let Some(err) = err.source() {
            println!("    source: {}", err);
            if let Some(err) = err.source() {
                println!("    source: {}", err);
            }
        }
        panic!();
    }
}
