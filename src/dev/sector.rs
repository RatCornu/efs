//! General description of sectors.

use core::fmt::{self, Debug};
use core::marker::PhantomData;

use super::error::DevError;

/// General interface for sector sizes that are device-dependant.
pub trait Size: Clone + Copy + PartialEq + Eq {
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

impl Size for Size512 {
    const LOG_SIZE: u32 = 9;
}

/// Size sector of 1024 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size1024;

impl Size for Size1024 {
    const LOG_SIZE: u32 = 10;
}

/// Size sector of 2048 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size2048;

impl Size for Size2048 {
    const LOG_SIZE: u32 = 11;
}

/// Size sector of 4096 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Size4096;

impl Size for Size4096 {
    const LOG_SIZE: u32 = 12;
}

/// Address of a physical sector
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Address<S: Size> {
    /// Sector in which the address is located.
    sector: u32,

    /// Offset of this address in the sector.
    offset: u32,

    /// Phantom data to store the sector size.
    _phantom: PhantomData<S>,
}

impl<S: Size> Debug for Address<S> {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Address")
            .field("sector", &self.sector)
            .field("offset", &self.offset)
            .finish()
    }
}

impl<S: Size> Address<S> {
    /// Returns a new [`Address`] with an offset such that `0 <= offset < S::SIZE`
    ///
    /// # Errors
    ///
    /// Returns an [`Error`](anyhow::Error)
    #[inline]
    pub fn new(sector: u32, offset: i32) -> Result<Self, DevError> {
        let real_signed_sector = TryInto::<i32>::try_into(sector)
            .map_err(|_err| DevError::OutOfBounds("sector", sector.into(), (0_i128, 0x1000_i128)))?
            + (offset >> S::LOG_SIZE);
        let real_sector = TryInto::<u32>::try_into(real_signed_sector)
            .map_err(|_err| DevError::OutOfBounds("sector", real_signed_sector.into(), (0_i128, u32::MAX.into())))?;
        let real_offset = offset.unsigned_abs() & S::OFFSET_MASK;
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
}

#[cfg(test)]
mod test {
    use super::{Size, Size1024, Size2048, Size4096, Size512};

    #[test]
    fn sizes() {
        assert_eq!(Size512::SIZE, 512);
        assert_eq!(Size1024::SIZE, 1024);
        assert_eq!(Size2048::SIZE, 2048);
        assert_eq!(Size4096::SIZE, 4096);
    }
}
