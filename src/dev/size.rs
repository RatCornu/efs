//! Utilities to manipulate device's size

use core::cmp::Ordering;

/// Caracterize the size of a device in bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Size(pub u64);

impl PartialEq<u64> for Size {
    #[inline]
    fn eq(&self, other: &u64) -> bool {
        self.0.eq(other)
    }
}

impl PartialOrd<u64> for Size {
    #[inline]
    fn partial_cmp(&self, other: &u64) -> Option<Ordering> {
        self.0.partial_cmp(other)
    }
}

impl From<u64> for Size {
    #[inline]
    fn from(value: u64) -> Self {
        Self(value)
    }
}
