//! Utilities to manipulate device's size

use core::cmp::Ordering;

use super::sector::Address;

/// Caracterize the size of a device
#[derive(Debug, Clone, Copy)]
pub enum Size {
    /// Bounded size with the last address of the device
    Bound(Address),

    /// Unbounded size
    Unbounded,
}

impl PartialEq for Size {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bound(len_self), Self::Bound(len_other)) => len_self == len_other,
            _ => false,
        }
    }
}

impl PartialEq<Address> for Size {
    #[inline]
    fn eq(&self, other: &Address) -> bool {
        match self {
            Self::Bound(address) => address == other,
            Self::Unbounded => false,
        }
    }
}

impl Eq for Size {}

impl PartialOrd for Size {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Self::Bound(self_len), Self::Bound(other_len)) => self_len.partial_cmp(other_len),
            (Self::Unbounded, Self::Unbounded) => None,
            (_, Self::Unbounded) => Some(Ordering::Less),
            (Self::Unbounded, _) => Some(Ordering::Greater),
        }
    }
}

impl PartialOrd<Address> for Size {
    #[inline]
    fn partial_cmp(&self, other: &Address) -> Option<Ordering> {
        match self {
            Self::Bound(len) => len.partial_cmp(other),
            Self::Unbounded => None,
        }
    }
}

impl From<Address> for Size {
    #[inline]
    fn from(value: Address) -> Self {
        Self::Bound(value)
    }
}

impl Size {
    /// Returns the length of the device if it exists
    #[inline]
    #[must_use]
    pub const fn try_len(&self) -> Option<Address> {
        match self {
            Self::Bound(address) => Some(*address),
            Self::Unbounded => None,
        }
    }
}
