//! General description of sectors.

use core::fmt::Debug;
use core::iter::Step;
use core::ops::{Add, Mul, Sub};

use derive_more::{Add, Deref, DerefMut, LowerHex, Sub};

/// Address of a physical sector
#[derive(Debug, Clone, Copy, PartialEq, Eq, LowerHex, PartialOrd, Ord, Deref, DerefMut, Add, Sub)]
pub struct Address(usize);

impl Address {
    /// Returns a new [`Address`] from its index.
    ///
    /// This function is equivalent to the [`From<usize>`](struct.Address.html#impl-From<usize>-for-Address) implementation but
    /// with a `const fn`.
    #[inline]
    #[must_use]
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    /// Returns the index of this address, which corresponds to its offset from the start of the device.
    #[inline]
    #[must_use]
    pub const fn index(&self) -> usize {
        self.0
    }
}

impl From<usize> for Address {
    #[inline]
    fn from(index: usize) -> Self {
        Self(index)
    }
}

impl From<Address> for usize {
    #[inline]
    fn from(value: Address) -> Self {
        value.0
    }
}

impl TryFrom<u64> for Address {
    type Error = <usize as TryFrom<u64>>::Error;

    #[inline]
    fn try_from(index: u64) -> Result<Self, Self::Error> {
        Ok(Self::from(TryInto::<usize>::try_into(index)?))
    }
}

impl TryFrom<u32> for Address {
    type Error = <usize as TryFrom<u32>>::Error;

    #[inline]
    fn try_from(index: u32) -> Result<Self, Self::Error> {
        Ok(Self::from(TryInto::<usize>::try_into(index)?))
    }
}

impl Add<usize> for Address {
    type Output = Self;

    #[inline]
    fn add(self, rhs: usize) -> Self::Output {
        Self(*self + rhs)
    }
}

impl Sub<usize> for Address {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: usize) -> Self::Output {
        Self(*self - rhs)
    }
}

impl Mul<usize> for Address {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: usize) -> Self::Output {
        Self(*self * rhs)
    }
}

impl Step for Address {
    #[inline]
    fn steps_between(start: &Self, end: &Self) -> Option<usize> {
        usize::steps_between(start, end)
    }

    #[inline]
    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        usize::forward_checked(*start, count).map(Into::into)
    }

    #[inline]
    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        usize::backward_checked(*start, count).map(Into::into)
    }
}
