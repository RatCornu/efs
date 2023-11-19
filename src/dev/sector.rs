//! General description of sectors.

use core::fmt::{self, Debug, LowerHex};
use core::iter::Step;
use core::marker::PhantomData;
use core::ops::{Add, Sub};

/// General interface for sector sizes that are device-dependant.
pub trait Sector: Clone + Copy + PartialEq + Eq {
    /// Logarithm in base 2 of the sector size.
    const LOG_SIZE: usize;

    /// Size of a sector.
    const SIZE: usize = 1 << Self::LOG_SIZE;

    /// Offset mask of the sector size.
    const OFFSET_MASK: usize = Self::SIZE - 1;
}

/// Size sector of 512 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size512;

impl Sector for Size512 {
    const LOG_SIZE: usize = 9;
}

/// Size sector of 1024 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size1024;

impl Sector for Size1024 {
    const LOG_SIZE: usize = 10;
}

/// Size sector of 2048 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size2048;

impl Sector for Size2048 {
    const LOG_SIZE: usize = 11;
}

/// Size sector of 4096 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size4096;

impl Sector for Size4096 {
    const LOG_SIZE: usize = 12;
}

/// Address of a physical sector
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Address<S: Sector> {
    /// Offset from the start of the device.
    index: usize,

    /// Phantom data to store the sector size.
    _phantom: PhantomData<S>,
}

impl<S: Sector> Debug for Address<S> {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_struct("Address").field("index", &self.index).finish()
    }
}

impl<S: Sector> LowerHex for Address<S> {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:x}:{:x}", self.sector(), self.offset())
    }
}

impl<S: Sector> PartialOrd for Address<S> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.index.partial_cmp(&other.index)
    }
}

impl<S: Sector> Address<S> {
    /// Returns a new [`Address`] with an offset such that `0 <= offset < S::SIZE` and a positive sector.
    ///
    /// # Panics
    ///
    /// This will panic if the given address is below the [`Address`] with sector and offset equal to 0, or if `isize::MAX < sector
    /// <= usize::MAX`.
    #[inline]
    #[must_use]
    pub fn new(sector: usize, offset: isize) -> Self {
        Self {
            index: TryInto::<isize>::try_into(sector << S::LOG_SIZE)
                .expect("The given sector could not be converted in a usize")
                .checked_add(offset)
                .and_then(|addr| addr.try_into().ok())
                .expect("The given address is below the offset 0"),
            _phantom: PhantomData,
        }
    }

    /// Returns the index of this address, which corresponds to its offset from the start of the device.
    #[inline]
    #[must_use]
    pub const fn index(&self) -> usize {
        self.index
    }

    /// Returns the sector containing this address.
    #[inline]
    #[must_use]
    pub const fn sector(&self) -> usize {
        self.index() / S::SIZE
    }

    /// Returns the offset of this address in its sector.
    #[inline]
    #[must_use]
    pub const fn offset(&self) -> usize {
        self.index() % S::SIZE
    }
}

impl<S: Sector> From<usize> for Address<S> {
    #[inline]
    fn from(value: usize) -> Self {
        Self {
            index: value,
            _phantom: PhantomData,
        }
    }
}

impl<S: Sector> TryFrom<u64> for Address<S> {
    type Error = <usize as TryFrom<u64>>::Error;

    #[inline]
    fn try_from(value: u64) -> Result<Self, Self::Error> {
        Ok(Self::from(TryInto::<usize>::try_into(value)?))
    }
}

impl<S: Sector> Add for Address<S> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            index: self.index + rhs.index,
            _phantom: PhantomData,
        }
    }
}

impl<S: Sector> Sub for Address<S> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            index: self
                .index
                .checked_sub(rhs.index)
                .expect("Tried to compute an address with a negative offset"),
            _phantom: PhantomData,
        }
    }
}

impl<S: Sector> Step for Address<S> {
    #[inline]
    fn steps_between(start: &Self, end: &Self) -> Option<usize> {
        (start.sector() <= end.sector()).then_some(end.index() - start.index())
    }

    #[inline]
    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        Some(start + Self::try_from(count).ok()?)
    }

    #[inline]
    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        Some(start - Self::try_from(count).ok()?)
    }
}

#[cfg(test)]
mod test {
    use super::{Sector, Size1024, Size2048, Size4096, Size512};
    use crate::dev::sector::Address;

    #[test]
    fn sizes() {
        assert_eq!(Size512::SIZE, 512);
        assert_eq!(Size1024::SIZE, 1024);
        assert_eq!(Size2048::SIZE, 2048);
        assert_eq!(Size4096::SIZE, 4096);
    }

    #[test]
    fn addresses_manipulation() {
        assert_eq!(Address::<Size4096>::new(1, 0), Address::<Size4096>::new(0, 4096));
        assert_eq!(Address::<Size4096>::new(1, -1000), Address::<Size4096>::new(0, 3096));
        assert_eq!(Address::<Size4096>::new(4, 0), Address::<Size4096>::new(2, 8192));
        assert_eq!(Address::<Size4096>::new(4, -5000), Address::<Size4096>::new(2, 3192));

        let address_1 = Address::<Size4096>::new(1, 1024);
        let address_2 = Address::<Size4096>::new(3, 1024);
        let address_3 = Address::<Size4096>::new(4, 2048);
        assert_eq!(address_1 + address_2, address_3);
        assert_eq!(address_3 - address_1, address_2);

        let address_1 = Address::<Size4096>::new(1, 2048);
        let address_2 = Address::<Size4096>::new(3, 3048);
        let address_3 = Address::<Size4096>::new(5, 1000);
        assert_eq!(address_1 + address_2, address_3);
        assert_eq!(address_3 - address_2, address_1);
    }

    #[test]
    fn indices() {
        assert_eq!(Address::<Size512>::new(2, 0).index(), 1024);
        assert_eq!(Address::<Size512>::new(4, 1000).index(), 3048);
        assert_eq!(Address::<Size1024>::new(4, 1000).index(), 5096);

        assert_eq!(Address::<Size1024>::try_from(5_096_u64).unwrap(), Address::new(4, 1000));
        assert_eq!(Address::<Size512>::from(3_048_usize), Address::new(5, 488));
    }
}
