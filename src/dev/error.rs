//! Errors related to device manipulation.

use alloc::fmt;
use core::error;
use core::fmt::Display;

/// Enumeration of possible errors encountered with device's manipulation.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug, PartialEq, Eq)]
pub enum DevError {
    /// `OutOfBounds(structure, value, (lower_bound, upper_bound))`: the given `struct` has a `value`  not between the given
    /// bounds.
    OutOfBounds(&'static str, i128, (i128, i128)),

    /// An error returned when an operation could not be completed because an “end of file” was reached prematurely.
    ///
    /// This typically means that an operation could only succeed if it read a particular number of bytes but only a smaller number
    /// of bytes could be read.
    UnexpectedEof,

    /// An error returned when an operation could not be completed because a call to [`write`](crate::io::Write::write) returned
    /// `Ok(0)`.
    WriteZero,
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
            Self::UnexpectedEof => write!(
                formatter,
                "Unexpected End of File: an operation could not be completed because an \"end of file\" was reached prematurely"
            ),
            Self::WriteZero => write!(
                formatter,
                "Write Zero: An error returned when an operation could not be completed because a call to write returned Ok(0)"
            ),
        }
    }
}

impl error::Error for DevError {}
