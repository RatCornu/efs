//! Errors related to device manipulation.

use alloc::fmt;
use core::error;
use core::fmt::Display;

/// Enumeration of possible errors encountered with device's manipulation.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug, PartialEq, Eq)]
pub enum DevError {
    /// `OutOfBounds(structure, value, (lower_bound, upper_bound))`: the given `struct` has a `value`  not between the given bounds
    OutOfBounds(&'static str, i128, (i128, i128)),
}

impl Display for DevError {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutOfBounds(structure, value, (lower_bound, upper_bound)) => {
                write!(
                    formatter,
                    "Out of Bounds: the {structure} has a value {value} not between the lower bound {lower_bound} and the upper bound {upper_bound}"
                )
            },
        }
    }
}

impl error::Error for DevError {}

impl DevError {
    /// Converts an [`Ext2Error`] into a `static str` in constant time.
    #[inline]
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::OutOfBounds(_, _, _) => "Out of Bounds ",
        }
    }
}
