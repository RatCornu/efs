//! Utilities to manipulate device's size

use core::cmp::Ordering;

use super::sector::{Address, Sector};

/// Caracterize the size of a device
#[derive(Debug, Clone, Copy)]
pub enum Size<S: Sector> {
    /// Bounded size with the last address of the device
    Bound(Address<S>),

    /// Unbounded size
    Unbounded,
}

impl<S: Sector> PartialEq for Size<S> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bound(len_self), Self::Bound(len_other)) => len_self == len_other,
            _ => false,
        }
    }
}

impl<S: Sector> PartialEq<Address<S>> for Size<S> {
    #[inline]
    fn eq(&self, other: &Address<S>) -> bool {
        match self {
            Self::Bound(address) => address == other,
            Self::Unbounded => false,
        }
    }
}

impl<S: Sector> Eq for Size<S> {}

impl<S: Sector> PartialOrd for Size<S> {
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

impl<S: Sector> From<Address<S>> for Size<S> {
    #[inline]
    fn from(value: Address<S>) -> Self {
        Self::Bound(value)
    }
}

impl<S: Sector> Size<S> {
    /// Returns the length of the device if it exists
    #[inline]
    #[must_use]
    pub const fn try_len(&self) -> Option<Address<S>> {
        match self {
            Self::Bound(address) => Some(*address),
            Self::Unbounded => None,
        }
    }
}
