//! Everything related to the devices

use alloc::borrow::Cow;
use core::error::Error;
use core::mem;

use self::sector::{Address, Sector};
use self::size::Size;

pub mod error;
pub mod sector;
pub mod size;

/// Slice of a device, filled with objects of type `T`.
#[derive(Debug, Clone)]
pub struct Slice<'mem, T: Clone, S: Sector> {
    /// Elements of the slice.
    inner: Cow<'mem, [T]>,

    /// Starting address of the slice.
    start_index: Address<S>,
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
    pub const fn new(inner: &'mem [T], start_index: Address<S>) -> Self {
        Self {
            inner: Cow::Borrowed(inner),
            start_index,
        }
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
    pub unsafe fn cast<T: Copy>(&self) -> (T, Address<S>) {
        assert!(self.inner.len() >= mem::size_of::<T>(), "");
        (mem::transmute_copy(self.inner.as_ptr().as_ref().expect("Could not read the pointer of the slice")), self.start_index)
    }
}

/// General interface for devices containing a file system.
pub trait Device<S: Sector> {
    /// Error type associated with the device.
    type Error: Error;

    /// [`Size`] description of this device.
    fn size(&self) -> Size<S>;
}
