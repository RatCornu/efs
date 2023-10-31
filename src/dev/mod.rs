//! Everything related to the devices

use alloc::borrow::{Cow, ToOwned};
use alloc::vec::Vec;
use core::cell::RefCell;
use core::mem;
use core::ops::Range;
use core::ptr::{addr_of, slice_from_raw_parts};
use std::fs::File;
use std::io::{Read, Seek, Write};

use self::sector::{Address, Sector};
use self::size::Size;
use crate::dev::error::DevError;
use crate::error::Error;

pub mod error;
pub mod sector;
pub mod size;

/// Slice of a device, filled with objects of type `T`.
#[derive(Debug, Clone)]
pub struct Slice<'mem, T: Clone, S: Sector> {
    /// Elements of the slice.
    inner: Cow<'mem, [T]>,

    /// Starting address of the slice
    starting_addr: Address<S>,
}

impl<'mem, T: Clone, S: Sector> AsRef<[T]> for Slice<'mem, T, S> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        &self.inner
    }
}

impl<'mem, T: Clone, S: Sector> AsMut<[T]> for Slice<'mem, T, S> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self.inner.to_mut().as_mut()
    }
}

impl<'mem, T: Clone, S: Sector> Slice<'mem, T, S> {
    /// Creates a new [`Slice`].
    #[inline]
    #[must_use]
    pub const fn new(inner: &'mem [T], starting_addr: Address<S>) -> Self {
        Self {
            inner: Cow::Borrowed(inner),
            starting_addr,
        }
    }

    /// Creates a new [`Slice`] from [`ToOwned::Owned`] objects.
    #[inline]
    #[must_use]
    pub const fn new_owned(inner: <[T] as ToOwned>::Owned, starting_addr: Address<S>) -> Self {
        Self {
            inner: Cow::Owned(inner),
            starting_addr,
        }
    }

    /// Returns the starting address of the slice.
    #[inline]
    #[must_use]
    pub const fn addr(&self) -> Address<S> {
        self.starting_addr
    }
}

impl<'mem, S: Sector> Slice<'mem, u8, S> {
    /// Returns the content of this slice as an object `T`.
    ///
    /// # Safety
    ///
    /// Must ensure that an instance of `T` is located at the begining of the slice and that the length of the slice is greater than
    /// the memory size of `T`.
    ///
    /// # Panics
    ///
    /// Panics if the starting address cannot be read.
    #[inline]
    #[must_use]
    pub unsafe fn cast<T: Copy>(&self) -> T {
        assert!(
            self.inner.len() >= mem::size_of::<T>(),
            "The length of the device slice is not great enough to contain an object T"
        );
        mem::transmute_copy(self.inner.as_ptr().as_ref().expect("Could not read the pointer of the slice"))
    }

    /// Creates a [`Slice`] from any [`Copy`] object
    #[inline]
    pub fn from<T: Copy>(object: T, starting_addr: Address<S>) -> Self {
        let len = mem::size_of::<T>();
        let ptr = addr_of!(object).cast::<u8>();
        // SAFETY: the pointer is well-formed since it has been created above
        let inner_opt = unsafe { slice_from_raw_parts(ptr, len).as_ref::<'mem>() };
        // SAFETY: `inner_opt` cannot be `None` as `ptr` contains data and the call to `slice_from_raw_parts` should not return a
        // null pointer
        Self::new(unsafe { inner_opt.unwrap_unchecked() }, starting_addr)
    }
}

/// General interface for devices containing a file system.
pub trait Device<'mem, T: Clone, S: Sector, E: core::error::Error> {
    /// Error type associated with the device.
    type Error: Into<Error<E>>;

    /// [`Size`] description of this device.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the size of the device cannot be determined.
    fn size(&self) -> Result<Size<S>, Self::Error>;

    /// Returns a [`Slice`]
    ///
    /// # Errors
    ///
    /// A
    fn slice(&'mem self, addr_range: Range<Address<S>>) -> Result<Slice<'mem, T, S>, Self::Error>;

    /// Writes the [`Slice`] onto the device.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`](Device::Error) if the write could not be completed.
    fn commit(&mut self, slice: Slice<'_, T, S>) -> Result<(), Self::Error>;
}

#[cfg(not(no_std))]
impl<'mem, S: Sector> Device<'mem, u8, S, std::io::Error> for RefCell<File> {
    type Error = Error<std::io::Error>;

    #[inline]
    fn size(&self) -> Result<Size<S>, Self::Error> {
        let metadata = self.borrow().metadata().map_err(Error::Other)?;
        let size = TryInto::<Address<S>>::try_into(metadata.len()).map_err(Error::Device)?;
        Ok(size.into())
    }

    #[inline]
    fn slice(&'mem self, addr_range: Range<Address<S>>) -> Result<Slice<'mem, u8, S>, Self::Error> {
        let starting_addr = addr_range.start;
        let len = TryInto::<usize>::try_into((addr_range.end - addr_range.start).index()).map_err(|_err| {
            Error::Device(DevError::OutOfBounds(
                "addr range",
                i128::from((addr_range.end - addr_range.start).index()),
                (0, usize::MAX as i128),
            ))
        })?;
        let mut slice = Vec::<u8>::with_capacity(len);
        let mut file = self.borrow_mut();
        file.seek(std::io::SeekFrom::Start(starting_addr.index()))
            .and_then(|_| file.read_exact(&mut slice))
            .map_err(Error::Other)?;
        Ok(Slice::new_owned(slice, starting_addr))
    }

    #[inline]
    fn commit(&mut self, slice: Slice<'_, u8, S>) -> Result<(), Self::Error> {
        let mut file = self.borrow_mut();
        file.seek(std::io::SeekFrom::Start(slice.addr().index()))
            .and_then(|_| file.write_all(slice.as_ref()))
            .map_err(Error::Other)
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn device_buffer() {
        todo!()
    }
}
