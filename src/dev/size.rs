//! Utilities to manipulate device's size

use core::cmp::Ordering;

use super::sector::Address;

/// Caracterize the size of a device
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Size(pub Address);

impl PartialEq<Address> for Size {
    #[inline]
    fn eq(&self, other: &Address) -> bool {
        self.0.eq(other)
    }
}

impl PartialOrd<Address> for Size {
    #[inline]
    fn partial_cmp(&self, other: &Address) -> Option<Ordering> {
        self.0.partial_cmp(other)
    }
}

impl From<Address> for Size {
    #[inline]
    fn from(value: Address) -> Self {
        Self(value)
    }
}

impl Size {
    /// Returns the length of the device if it exists
    #[inline]
    #[must_use]
    pub const fn len(&self) -> Address {
        self.0
    }
}
