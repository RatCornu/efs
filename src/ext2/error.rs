//! Errors related to Ext2 manipulation.

use core::error;
use core::fmt::{self, Display};

/// Enumeration of possible errors encountered with Ext2's manipulation.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug, PartialEq, Eq)]
pub enum Ext2Error {
    /// A bad magic number has been found during the superblock parsing.
    BadMagic(u16),
}

impl Display for Ext2Error {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadMagic(magic) => write!(formatter, "Bad Magic: {magic} has been found while TODO was expected"),
        }
    }
}

impl error::Error for Ext2Error {}
