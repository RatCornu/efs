//! General description of sectors.

use core::cmp::Ordering;
use core::fmt::{self, Debug, Display, LowerHex};
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
    /// Sector in which the address is located.
    sector: usize,

    /// Offset of this address in the sector.
    offset: usize,

    /// Phantom data to store the sector size.
    _phantom: PhantomData<S>,
}

impl<S: Sector> Debug for Address<S> {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Address")
            .field("sector", &self.sector)
            .field("offset", &self.offset)
            .finish()
    }
}

impl<S: Sector> PartialOrd for Address<S> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<S: Sector> Ord for Address<S> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.sector.cmp(&other.sector) {
            Ordering::Equal => {},
            ord @ (Ordering::Less | Ordering::Greater) => return ord,
        }

        match self.offset.cmp(&other.offset) {
            Ordering::Equal => Ordering::Equal,
            ord @ (Ordering::Less | Ordering::Greater) => ord,
        }
    }
}

impl<S: Sector> Display for Address<S> {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}:{}", self.sector, self.offset)
    }
}

impl<S: Sector> LowerHex for Address<S> {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:x}:{:x}", self.sector, self.offset)
    }
}

impl<S: Sector> Address<S> {
    /// Returns a new [`Address`] with an offset such that `0 <= offset < S::SIZE` and a positive sector.
    ///
    /// # Panics
    ///
    /// This will panic if the given address is below the [`Address`] with sector and offset equal to 0.
    #[inline]
    #[must_use]
    pub fn new(sector: usize, offset: isize) -> Self {
        let real_sector = usize::try_from(
            TryInto::<isize>::try_into(sector).expect("Could not convert `sector` to `isize`") + (offset >> S::LOG_SIZE),
        )
        .expect("The given address is below the address with sector and offset equal to 0");
        let real_offset = offset
            // SAFETY: it is checked at compile time that `S::SIZE < usize::MAX`, so as `S::SIZE` is a power of 2, then `S::SIZE <=
            // i32::MAX`
            .rem_euclid(unsafe { S::SIZE.try_into().unwrap_unchecked() })
            .unsigned_abs()
            & S::OFFSET_MASK;

        Self {
            sector: real_sector,
            offset: real_offset,
            _phantom: PhantomData,
        }
    }

    /// Returns the sector containing this address.
    #[inline]
    #[must_use]
    pub const fn sector(&self) -> usize {
        self.sector
    }

    /// Returns the offset of this address in its sector.
    #[inline]
    #[must_use]
    pub const fn offset(&self) -> usize {
        self.offset
    }

    /// Returns the index of this address, which corresponds to its offset from the start of the device.
    #[inline]
    #[must_use]
    pub const fn index(&self) -> usize {
        (self.sector() << S::LOG_SIZE) + self.offset()
    }
}

impl<S: Sector> From<usize> for Address<S> {
    #[inline]
    fn from(value: usize) -> Self {
        Self::new(
            // SAFETY: `S::SIZE` cannot be equal to 0
            unsafe { value.checked_div(S::SIZE).unwrap_unchecked() },
            // SAFETY: `S::SIZE` cannot be equal to 0
            unsafe { value.checked_rem(S::SIZE).unwrap_unchecked() }
                .try_into()
                .unwrap_or_else(|_| unreachable!()),
        )
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
        // SAFETY: `offset` returns a value smaller that `S::SIZE`
        Self::new(self.sector() + rhs.sector(), unsafe { (self.offset() + rhs.offset()).try_into().unwrap_unchecked() })
    }
}

impl<S: Sector> Sub for Address<S> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(
            self.sector() - rhs.sector(),
            // SAFETY: `offset` returns a value smaller that `S::SIZE`
            unsafe { TryInto::<isize>::try_into(self.offset()).unwrap_unchecked() }
            // SAFETY: `offset` returns a value smaller that `S::SIZE`
                - unsafe { TryInto::<isize>::try_into(rhs.offset()).unwrap_unchecked() },
        )
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
