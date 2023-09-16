use super::scan;
use super::{ParseResult, INVALID, OUT_OF_RANGE};

/// Helper type for parsing decimals (as in an ISO 8601 duration).
#[derive(Copy, Clone)]
struct Decimal {
    base: u64,
    fraction: Option<Fraction>,
}

impl Decimal {
    fn parse(s: &str) -> ParseResult<(&str, Self)> {
        let (s, num) = scan::number(s, 1, usize::MAX)?;
        let (s, frac) = match Fraction::parse(s) {
            Ok((s, frac)) => (s, Some(frac)),
            Err(_) => (s, None),
        };
        let result = Decimal { base: num as u64, fraction: frac };
        Ok((s, result))
    }

    /// Multiplying this `Decimal` with `unit`.
    ///
    /// Returns `None` on out of range.
    fn mul(&self, unit: u64) -> ParseResult<u64> {
        let frac = self.fraction.unwrap_or(Fraction(0)).mul(unit);
        self.base.checked_mul(unit).and_then(|n| n.checked_add(frac)).ok_or(OUT_OF_RANGE)
    }

    /// Returns the result of multiplying this `Decimal` with `unit`.
    ///
    /// Returns two integers to represent the whole number and the fraction as nanos.
    fn mul_with_nanos(&self, unit: u64) -> ParseResult<(u64, u32)> {
        let (whole_from_rounding, fraction_as_nanos) =
            self.fraction.unwrap_or(Fraction(0)).mul_with_nanos(unit);
        let whole = (self.base)
            .checked_mul(unit)
            .and_then(|n| n.checked_add(whole_from_rounding))
            .ok_or(OUT_OF_RANGE)?;
        Ok((whole, fraction_as_nanos as u32))
    }

    /// Returns the value of this `Decimal` if it is an integer, otherwise `None`.
    fn integer(&self) -> ParseResult<u64> {
        match self.fraction {
            None => Ok(self.base),
            _ => Err(INVALID),
        }
    }
}

/// Helper type for parsing fractional numbers.
///
/// The fraction is stored as an integer in the range 0..=10^15.
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
    fn mul(&self, unit: u64) -> u64 {
        assert!(unit <= 3600); // assumption to prevent overflow later.
        (self.0 * unit + POW10[15] / 2) / POW10[15]
    }

    /// Returns the result of multiplying this `Fraction` with `unit`.
    ///
    /// Returns two integers to represent the whole number and the fraction as nanos.
    fn mul_with_nanos(&self, unit: u64) -> (u64, u64) {
        assert!(unit <= 3600); // assumption to prevent overflow later.
        let div = POW10[15 - 9];
        let huge = self.0 * unit + div / 2;
        let whole = huge / POW10[15];
        let fraction_as_nanos = (huge % POW10[15]) / div;
        (whole, fraction_as_nanos)
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
    use super::Fraction;
    use crate::format::INVALID;

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
