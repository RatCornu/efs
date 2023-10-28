//! General description of sectors.

use core::cmp::Ordering;
use core::fmt::{self, Debug, Display, LowerHex};
use core::iter::Step;
use core::marker::PhantomData;
use core::ops::{Add, Sub};

use super::error::DevError;

/// General interface for sector sizes that are device-dependant.
pub trait Sector: Clone + Copy + PartialEq + Eq {
    /// Logarithm in base 2 of the sector size.
    const LOG_SIZE: u32;

    /// Size of a sector.
    const SIZE: u32 = 1 << Self::LOG_SIZE;

    /// Offset mask of the sector size.
    const OFFSET_MASK: u32 = Self::SIZE - 1;
}

/// Size sector of 512 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size512;

impl Sector for Size512 {
    const LOG_SIZE: u32 = 9;
}

/// Size sector of 1024 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size1024;

impl Sector for Size1024 {
    const LOG_SIZE: u32 = 10;
}

/// Size sector of 2048 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size2048;

impl Sector for Size2048 {
    const LOG_SIZE: u32 = 11;
}

/// Size sector of 4096 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size4096;

impl Sector for Size4096 {
    const LOG_SIZE: u32 = 12;
}

/// Address of a physical sector
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Address<S: Sector> {
    /// Sector in which the address is located.
    sector: u32,

    /// Offset of this address in the sector.
    offset: u32,

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
    /// # Errors
    ///
    /// Returns an [`DevError`] if the given `sector` and the given `offset` does not correspond to a valid address.
    ///
    /// # Panics
    ///
    /// Panics if `S::SIZE` is greater than `i32::MAX`, which is equivalent to `S::LOG_SIZE >= 16`.
    #[inline]
    pub fn new(sector: u32, offset: i32) -> Result<Self, DevError> {
        let real_signed_sector = TryInto::<i32>::try_into(sector)
            .map_err(|_err| DevError::OutOfBounds("sector", sector.into(), (0_i128, 0x1000_i128)))?
            + (offset >> S::LOG_SIZE);
        let real_sector = TryInto::<u32>::try_into(real_signed_sector)
            .map_err(|_err| DevError::OutOfBounds("sector", real_signed_sector.into(), (0_i128, u32::MAX.into())))?;
        let real_offset = offset
            // SAFETY: it is checked at compile time that `S::SIZE < u32::MAX`, so as `S::SIZE` is a power of 2, then `S::SIZE <=
            // i32::MAX`
            .rem_euclid(unsafe { TryInto::<i32>::try_into(S::SIZE).unwrap_unchecked() })
            .unsigned_abs()
            & S::OFFSET_MASK;
        if real_offset >= S::SIZE {
            Err(DevError::OutOfBounds("offset", real_offset.into(), (0_i128, S::SIZE.into())))
        } else {
            Ok(Self {
                sector: real_sector,
                offset: real_offset,
                _phantom: PhantomData,
            })
        }
    }

    /// Returns the sector containing this address.
    #[inline]
    #[must_use]
    pub const fn sector(&self) -> u32 {
        self.sector
    }

    /// Returns the offset of this address in its sector.
    #[inline]
    #[must_use]
    pub const fn offset(&self) -> u32 {
        self.offset
    }

    /// Returns the index of this address, which corresponds to its offset from the start of the device.
    #[inline]
    #[must_use]
    pub const fn index(&self) -> u64 {
        ((self.sector() as u64) << S::LOG_SIZE) + self.offset() as u64
    }
}

impl<S: Sector> TryFrom<u64> for Address<S> {
    type Error = DevError;

    #[inline]
    fn try_from(value: u64) -> Result<Self, Self::Error> {
        Self::new(
            TryInto::<u32>::try_into(value >> S::LOG_SIZE)
                .map_err(|_err| DevError::OutOfBounds("sector", value.into(), (0_i128, u32::MAX.into())))?,
            TryInto::<i32>::try_into(value & u64::from(S::OFFSET_MASK))
                .unwrap_or_else(|_| unreachable!("`S::OFFSET_MASK <= u32::MAX` is checked at compile time")),
        )
    }
}

impl<S: Sector> TryFrom<usize> for Address<S> {
    type Error = DevError;

    #[inline]
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        Self::new(
            TryInto::<u32>::try_into(value >> S::LOG_SIZE).map_err(|_err| {
                DevError::OutOfBounds("sector", value.try_into().unwrap_or_else(|_| unreachable!()), (0_i128, u32::MAX.into()))
            })?,
            TryInto::<i32>::try_into(value & usize::try_from(S::OFFSET_MASK).unwrap_or_else(|_| unreachable!()))
                .unwrap_or_else(|_| unreachable!("`S::OFFSET_MASK <= u32::MAX` is checked at compile time")),
        )
    }
}

impl<S: Sector> Add for Address<S> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(
            self.sector() + rhs.sector(),
            TryInto::<i32>::try_into(self.offset() + rhs.offset()).expect("offset addition overflows"),
        )
        .expect("addresses addition overflows")
    }
}

impl<S: Sector> Sub for Address<S> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(
            self.sector() - rhs.sector(),
            TryInto::<i32>::try_into(self.offset()).expect("Could not cast offset to an i32")
                - TryInto::<i32>::try_into(rhs.offset()).expect("Could not cast offset to an i32"),
        )
        .expect("offset substraction overflows")
    }
}

impl<S: Sector> Step for Address<S> {
    #[inline]
    fn steps_between(start: &Self, end: &Self) -> Option<usize> {
        (start.sector() <= end.sector()).then_some((end.sector() - start.sector()) as usize)
    }

    #[inline]
    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        ((start.sector() as usize) < (S::SIZE as usize - count))
            .then(|| Self::new(start.sector() + TryInto::<u32>::try_into(count).ok()?, 0).ok())
            .flatten()
    }

    #[inline]
    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        ((start.sector() as usize) >= count)
            .then(|| Self::new(start.sector() - TryInto::<u32>::try_into(count).ok()?, 0).ok())
            .flatten()
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
        assert_eq!(Address::<Size4096>::new(1, 0).unwrap(), Address::<Size4096>::new(0, 4096).unwrap());
        assert_eq!(Address::<Size4096>::new(1, -1000).unwrap(), Address::<Size4096>::new(0, 3096).unwrap());
        assert_eq!(Address::<Size4096>::new(4, 0).unwrap(), Address::<Size4096>::new(2, 8192).unwrap());
        assert_eq!(Address::<Size4096>::new(4, -5000).unwrap(), Address::<Size4096>::new(2, 3192).unwrap());

        let address_1 = Address::<Size4096>::new(1, 1024).unwrap();
        let address_2 = Address::<Size4096>::new(3, 1024).unwrap();
        let address_3 = Address::<Size4096>::new(4, 2048).unwrap();
        assert_eq!(address_1 + address_2, address_3);
        assert_eq!(address_3 - address_1, address_2);

        let address_1 = Address::<Size4096>::new(1, 2048).unwrap();
        let address_2 = Address::<Size4096>::new(3, 3048).unwrap();
        let address_3 = Address::<Size4096>::new(5, 1000).unwrap();
        assert_eq!(address_1 + address_2, address_3);
        assert_eq!(address_3 - address_2, address_1);
    }

    #[test]
    fn indices() {
        assert_eq!(Address::<Size512>::new(2, 0).unwrap().index(), 1024);
        assert_eq!(Address::<Size512>::new(4, 1000).unwrap().index(), 3048);
        assert_eq!(Address::<Size1024>::new(4, 1000).unwrap().index(), 5096);

        assert_eq!(Address::<Size1024>::try_from(5_096_u64).unwrap(), Address::new(4, 1000).unwrap());
        assert_eq!(Address::<Size512>::try_from(3_048_usize).unwrap(), Address::new(5, 488).unwrap());
    }
}
