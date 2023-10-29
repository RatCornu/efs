//! Everything related to the devices

use alloc::borrow::Cow;
use core::error::Error;
use core::mem;
use core::ptr::{addr_of, slice_from_raw_parts};

use self::sector::Sector;
use self::size::Size;

pub mod error;
pub mod sector;
pub mod size;

/// Slice of a device, filled with objects of type `T`.
#[derive(Debug, Clone)]
pub struct Slice<'mem, T: Clone> {
    /// Elements of the slice.
    inner: Cow<'mem, [T]>,
}

impl<'mem, T: Clone> AsRef<[T]> for Slice<'mem, T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        &self.inner
    }
}

impl<'mem, T: Clone> AsMut<[T]> for Slice<'mem, T> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self.inner.to_mut().as_mut()
    }
}

impl<'mem, T: Clone> Slice<'mem, T> {
    /// Creates a new [`Slice`].
    #[inline]
    #[must_use]
    pub const fn new(inner: &'mem [T]) -> Self {
        Self {
            inner: Cow::Borrowed(inner),
        }
    }
}

impl<'mem> Slice<'mem, u8> {
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

    /// A
    #[inline]
    pub fn from<T: Copy>(object: &'mem T) -> Self {
        let len = mem::size_of::<T>();
        let ptr = addr_of!(*object).cast::<u8>();
        // SAFETY:
        let inner_opt = unsafe { slice_from_raw_parts(ptr, len).as_ref() };
        // SAFETY:
        Self::new(unsafe { inner_opt.unwrap_unchecked() })
    }
}

/// General interface for devices containing a file system.
pub trait Device<T: Copy, S: Sector> {
    /// Error type associated with the device.
    type Error: Error;

    /// [`Size`] description of this device.
    fn size(&self) -> Size<S>;
}
