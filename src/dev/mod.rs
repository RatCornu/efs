//! Everything related to the devices

use alloc::borrow::{Cow, ToOwned};
use alloc::boxed::Box;
use alloc::slice;
use alloc::vec::Vec;
use core::cell::RefCell;
use core::iter::Step;
use core::mem::{size_of, transmute_copy};
use core::ops::{Deref, DerefMut, Range};
use core::ptr::{addr_of, slice_from_raw_parts};
#[cfg(any(feature = "std", test))]
use std::fs::File;
#[cfg(any(feature = "std", test))]
use std::io::ErrorKind;

use self::sector::Address;
use self::size::Size;
use crate::dev::error::DevError;
use crate::error::Error;
use crate::io::{Base, Read, Seek, SeekFrom, Write};

pub mod celled;
pub mod error;
pub mod sector;
pub mod size;

/// Slice of a device, filled with objects of type `T`.
#[derive(Debug, Clone)]
pub struct Slice<'mem, T: Clone> {
    /// Elements of the slice.
    inner: Cow<'mem, [T]>,

    /// Starting address of the slice.
    starting_addr: Address,
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

impl<'mem, T: Clone> Deref for Slice<'mem, T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'mem, T: Clone> DerefMut for Slice<'mem, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut()
    }
}

impl<'mem, T: Clone> Slice<'mem, T> {
    /// Creates a new [`Slice`].
    #[inline]
    #[must_use]
    pub const fn new(inner: &'mem [T], starting_addr: Address) -> Self {
        Self {
            inner: Cow::Borrowed(inner),
            starting_addr,
        }
    }

    /// Creates a new [`Slice`] from [`ToOwned::Owned`] objects.
    #[inline]
    #[must_use]
    pub const fn new_owned(inner: <[T] as ToOwned>::Owned, starting_addr: Address) -> Self {
        Self {
            inner: Cow::Owned(inner),
            starting_addr,
        }
    }

    /// Returns the starting address of the slice.
    #[inline]
    #[must_use]
    pub const fn addr(&self) -> Address {
        self.starting_addr
    }

    /// Checks whether the slice has been mutated or not.
    #[inline]
    #[must_use]
    pub const fn is_mutated(&self) -> bool {
        match self.inner {
            Cow::Borrowed(_) => false,
            Cow::Owned(_) => true,
        }
    }

    /// Commits the write operations onto the slice and returns a [`Commit`]ed object.
    #[inline]
    #[must_use]
    pub fn commit(self) -> Commit<T> {
        Commit::new(self.inner.into_owned(), self.starting_addr)
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
        assert!(self.inner.len() >= size_of::<T>(), "The length of the device slice is not great enough to contain an object T");
        transmute_copy(self.inner.as_ptr().as_ref().expect("Could not read the pointer of the slice"))
    }

    /// Creates a [`Slice`] from any [`Copy`] object
    #[inline]
    pub fn from<T: Copy>(object: T, starting_addr: Address) -> Self {
        let len = size_of::<T>();
        let ptr = addr_of!(object).cast::<u8>();
        // SAFETY: the pointer is well-formed since it has been created above
        let inner_opt = unsafe { slice_from_raw_parts(ptr, len).as_ref::<'mem>() };
        // SAFETY: `inner_opt` cannot be `None` as `ptr` contains data and the call to `slice_from_raw_parts` should not return a
        // null pointer
        Self::new(unsafe { inner_opt.unwrap_unchecked() }, starting_addr)
    }
}

/// Commited slice of a device, filled with objects of type `T`.
#[derive(Debug, Clone)]
pub struct Commit<T: Clone> {
    /// Elements of the commit.
    inner: Vec<T>,

    /// Starting address of the slice.
    starting_addr: Address,
}

impl<T: Clone> Commit<T> {
    /// Creates a new [`Commit`] instance.
    #[inline]
    #[must_use]
    pub fn new(inner: Vec<T>, starting_addr: Address) -> Self {
        Self {
            inner,
            starting_addr,
        }
    }

    /// Returns the starting address of the commit.
    #[inline]
    #[must_use]
    pub const fn addr(&self) -> Address {
        self.starting_addr
    }
}

impl<T: Clone> AsRef<[T]> for Commit<T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        &self.inner
    }
}

impl<T: Clone> AsMut<[T]> for Commit<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self.inner.as_mut()
    }
}

/// General interface for devices containing a file system.
pub trait Device<T: Copy, E: core::error::Error> {
    /// [`Size`] description of this device.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the size of the device cannot be determined.
    fn size(&self) -> Size;

    /// Returns a [`Slice`] with elements of this device.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the read could not be completed.
    fn slice(&self, addr_range: Range<Address>) -> Result<Slice<'_, T>, Error<E>>;

    /// Writes the [`Commit`] onto the device.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the write could not be completed.
    fn commit(&mut self, commit: Commit<T>) -> Result<(), Error<E>>;

    /// Read an element of type `O` on the device starting at the address `starting_addr`.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the read tries to go out of the device's bounds or if [`Device::slice`] failed.
    ///
    /// # Safety
    ///
    /// Must verifies the safety conditions of [`core::ptr::read`].
    #[inline]
    unsafe fn read_at<O: Copy>(&self, starting_addr: Address) -> Result<O, Error<E>> {
        let length = size_of::<O>();
        let range = starting_addr
            ..Address::forward_checked(starting_addr, length).ok_or(Error::Device(DevError::OutOfBounds(
                "address",
                i128::try_from(starting_addr.index() + length).unwrap_unchecked(),
                (0, self.size().0.into()),
            )))?;
        let slice = self.slice(range)?;
        let ptr = slice.inner.as_ptr();
        Ok(ptr.cast::<O>().read())
    }

    /// Writes an element of type `O` on the device starting at the address `starting_addr`.
    ///
    /// Beware, the `object` **must be the owned `O` object and not a borrow**, otherwise the pointer to the object will be copied,
    /// and not the object itself.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the read tries to go out of the device's bounds or if [`Device::slice`] or [`Device::commit`]
    /// failed.
    ///
    /// # Safety
    ///
    /// Must ensure that `size_of::<O>() % size_of::<T>() == 0`.
    #[inline]
    unsafe fn write_at<O: Copy>(&mut self, starting_addr: Address, object: O) -> Result<(), Error<E>> {
        let length = size_of::<O>();
        assert_eq!(
            length % size_of::<T>(),
            0,
            "Cannot write an element whose memory size is not divisible by the memory size of the elements of the device"
        );
        assert!(length > 0, "Cannot write a 0-byte object on a device");
        let object_slice = slice::from_raw_parts(addr_of!(object).cast::<T>(), length / size_of::<T>());

        let range = starting_addr
            ..Address::forward_checked(starting_addr, length).ok_or(Error::Device(DevError::OutOfBounds(
                "address",
                i128::try_from(starting_addr.index() + length).unwrap_unchecked(),
                (0, self.size().0.into()),
            )))?;
        let mut device_slice = self.slice(range)?;
        let buffer = device_slice
            .get_mut(..)
            .unwrap_or_else(|| unreachable!("It is always possible to take all the elements of a slice"));
        buffer.copy_from_slice(object_slice);

        let commit = device_slice.commit();
        self.commit(commit).map_err(Into::into)
    }
}

/// Generic implementation of the [`Device`] trait.
macro_rules! impl_device {
    ($volume:ty) => {
        impl<T: Copy, E: core::error::Error> Device<T, E> for $volume {
            #[inline]
            fn size(&self) -> Size {
                Size(self.len() as u64)
            }

            #[inline]
            fn slice(&self, addr_range: Range<Address>) -> Result<Slice<'_, T>, Error<E>> {
                if Device::<T, E>::size(self) >= usize::from(addr_range.end) as u64 {
                    let addr_start = addr_range.start;
                    // SAFETY: it is not possible to manipulate addresses with a higher bit number than the device's
                    let range = unsafe { usize::try_from(addr_range.start.index()).unwrap_unchecked() }..unsafe {
                        usize::try_from(addr_range.end.index()).unwrap_unchecked()
                    };
                    // SAFETY: it is checked above that the wanted elements exist
                    Ok(Slice::new(unsafe { <Self as AsRef<[T]>>::as_ref(self).get_unchecked(range) }, addr_start))
                } else {
                    Err(Error::Device(DevError::OutOfBounds(
                        "address",
                        // SAFETY: it is assumed that `usize` can always be converted to `i128`
                        unsafe { addr_range.end.index().try_into().unwrap_unchecked() },
                        (0, <Self as Device<T, E>>::size(self).0.into()),
                    )))
                }
            }

            #[inline]
            fn commit(&mut self, commit: Commit<T>) -> Result<(), Error<E>> {
                // SAFETY: it is safe to assume that the given `slice` as a length smaller than `usize::MAX`
                let addr_start = unsafe { usize::try_from(commit.addr().index()).unwrap_unchecked() };
                let addr_end = addr_start + commit.as_ref().len();

                // SAFETY: it is safe to assume that `usize::MAX < i128::MAX`
                let self_len = unsafe { self.len().try_into().unwrap_unchecked() };

                let dest = &mut <Self as AsMut<[T]>>::as_mut(self).get_mut(addr_start..addr_end).ok_or_else(|| {
                    // SAFETY: `usize::MAX <= i128::MAX`
                    Error::Device(DevError::OutOfBounds(
                        "address",
                        // SAFETY: `usize::MAX <= i128::MAX`
                        unsafe { addr_end.try_into().unwrap_unchecked() },
                        (0, self_len),
                    ))
                })?;
                dest.clone_from_slice(&commit.as_ref());
                Ok(())
            }
        }
    };
}

impl_device!(&mut [T]);
impl_device!(Vec<T>);
impl_device!(Box<[T]>);

impl<E: core::error::Error, T: Base<Error = E> + Read + Write + Seek> Device<u8, E> for RefCell<T> {
    #[inline]
    fn size(&self) -> Size {
        let mut device = self.borrow_mut();
        let offset = device.seek(SeekFrom::End(0)).expect("Could not seek the device at its end");
        let size = device
            .seek(SeekFrom::Start(offset))
            .expect("Could not seek the device at its original offset");
        Size(size)
    }

    #[inline]
    fn slice(&self, addr_range: Range<Address>) -> Result<Slice<'_, u8>, Error<E>> {
        let starting_addr = addr_range.start;
        let len = TryInto::<usize>::try_into((addr_range.end - addr_range.start).index()).map_err(|_err| {
            Error::Device(DevError::OutOfBounds(
                "addr range",
                // SAFETY: `usize::MAX <= i128::MAX`
                unsafe { i128::try_from((addr_range.end - addr_range.start).index()).unwrap_unchecked() },
                (0, i128::MAX),
            ))
        })?;

        let mut slice = alloc::vec![0; len];
        let mut device = self.borrow_mut();
        device
            .seek(SeekFrom::Start(starting_addr.index().try_into().expect("Could not convert `usize` to `u64`")))
            .and_then(|_| device.read_exact(&mut slice))?;

        Ok(Slice::new_owned(slice, starting_addr))
    }

    #[inline]
    fn commit(&mut self, commit: Commit<u8>) -> Result<(), Error<E>> {
        let mut device = self.borrow_mut();

        let offset = device.seek(SeekFrom::Start(commit.addr().index().try_into().expect("Could not convert `usize` to `u64`")))?;
        device.write_all(commit.as_ref())?;
        device.seek(SeekFrom::Start(offset))?;

        Ok(())
    }
}

#[cfg(any(feature = "std", test))]
impl<E: core::error::Error> Device<u8, E> for RefCell<File> {
    #[inline]
    fn size(&self) -> Size {
        let metadata = self.borrow().metadata().expect("Could not read the file");
        Size(metadata.len())
    }

    #[inline]
    fn slice(&self, addr_range: Range<Address>) -> Result<Slice<'_, u8>, Error<E>> {
        use std::io::{Read, Seek};

        let starting_addr = addr_range.start;
        let len = TryInto::<usize>::try_into((addr_range.end - addr_range.start).index()).map_err(|_err| {
            Error::Device(DevError::OutOfBounds(
                "addr range",
                // SAFETY: `usize::MAX <= i128::MAX`
                unsafe { i128::try_from((addr_range.end - addr_range.start).index()).unwrap_unchecked() },
                (0, i128::MAX),
            ))
        })?;
        let mut slice = alloc::vec![0; len];
        let mut file = self.borrow_mut();
        match file
            .seek(std::io::SeekFrom::Start(starting_addr.index().try_into().expect("Could not convert `usize` to `u64`")))
            .and_then(|_| file.read_exact(&mut slice))
        {
            Ok(()) => Ok(Slice::new_owned(slice, starting_addr)),
            Err(err) => {
                if err.kind() == ErrorKind::UnexpectedEof {
                    Err(Error::Device(DevError::OutOfBounds(
                        "address",
                        // SAFETY: `usize::MAX <= i128::MAX`
                        unsafe { i128::try_from(usize::from(starting_addr + len)).unwrap_unchecked() },
                        (0, Device::<u8, E>::size(self).0.into()),
                    )))
                } else {
                    Err(Error::IO(err))
                }
            },
        }
    }

    #[inline]
    fn commit(&mut self, commit: Commit<u8>) -> Result<(), Error<E>> {
        use std::io::{Seek, Write};

        let mut file = self.borrow_mut();
        match file.seek(std::io::SeekFrom::Start(commit.addr().index().try_into().expect("Could not convert `usize` to `u64`"))) {
            Ok(offset) => {
                file.write_all(commit.as_ref()).expect("Could not write on the given file");
                file.seek(std::io::SeekFrom::Start(offset)).expect("Could not seek on the given file");
            },
            Err(err) => panic!("{err}: Could not seek on the given file"),
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use alloc::string::String;
    use alloc::vec;
    use core::cell::RefCell;
    use core::fmt::Display;
    use core::mem::size_of;
    use core::ptr::addr_of;
    use core::slice;
    use std::fs::{self, OpenOptions};

    use crate::dev::sector::Address;
    use crate::dev::Device;

    #[derive(Debug)]
    struct Error;

    impl Display for Error {
        fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(formatter, "")
        }
    }

    impl core::error::Error for Error {}

    #[test]
    fn device_generic_read() {
        let mut device = vec![0_usize; 1024];
        let mut slice = Device::<usize, std::io::Error>::slice(
            &device,
            Address::try_from(256_u64).unwrap()..Address::try_from(512_u64).unwrap(),
        )
        .unwrap();
        slice.iter_mut().for_each(|element| *element = 1);

        let commit = slice.commit();

        assert!(Device::<usize, std::io::Error>::commit(&mut device, commit).is_ok());

        for (idx, &x) in device.iter().enumerate() {
            assert_eq!(x, usize::from((256..512).contains(&idx)));
        }
    }

    #[allow(clippy::missing_asserts_for_indexing)]
    #[test]
    fn device_file_write() {
        fs::copy("./tests/dev/device_file_1.txt", "./tests/dev/device_file_1_copy.txt").unwrap();

        let mut file_1 = RefCell::new(
            OpenOptions::new()
                .read(true)
                .write(true)
                .open("./tests/dev/device_file_1_copy.txt")
                .unwrap(),
        );

        let mut slice = Device::<u8, Error>::slice(&file_1, Address::new(0)..Address::new(13)).unwrap();

        let word = slice.get_mut(6..=10).unwrap();
        word[0] = b'e';
        word[1] = b'a';
        word[2] = b'r';
        word[3] = b't';
        word[4] = b'h';

        let commit = slice.commit();
        Device::<u8, Error>::commit(&mut file_1, commit).unwrap();

        drop(file_1);

        let file_1 = String::from_utf8(fs::read("./tests/dev/device_file_1_copy.txt").unwrap()).unwrap();
        let file_2 = String::from_utf8(fs::read("./tests/dev/device_file_2.txt").unwrap()).unwrap();

        assert_eq!(file_1, file_2);

        fs::remove_file("./tests/dev/device_file_1_copy.txt").unwrap();
    }

    #[test]
    fn device_generic_read_at() {
        const OFFSET: usize = 123;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct Test {
            nb_1: u16,
            nb_2: u8,
            nb_3: usize,
            nb_4: u128,
        }

        let test = Test {
            nb_1: 0xabcd,
            nb_2: 0x99,
            nb_3: 0x1234,
            nb_4: 0x1234_5678_90ab_cdef,
        };
        let test_bytes = unsafe { slice::from_raw_parts(addr_of!(test).cast::<u8>(), size_of::<Test>()) };

        let mut device = vec![0_u8; 1024];
        let mut slice = Device::<u8, std::io::Error>::slice(
            &device,
            Address::try_from(OFFSET).unwrap()..Address::try_from(OFFSET + size_of::<Test>()).unwrap(),
        )
        .unwrap();
        let buffer = slice.get_mut(..).unwrap();
        buffer.clone_from_slice(test_bytes);

        let commit = slice.commit();
        Device::<u8, std::io::Error>::commit(&mut device, commit).unwrap();

        let read_test =
            unsafe { Device::<u8, std::io::Error>::read_at::<Test>(&device, Address::try_from(OFFSET).unwrap()).unwrap() };
        assert_eq!(test, read_test);
    }

    #[test]
    fn device_generic_write_at() {
        const OFFSET: u64 = 123;

        #[repr(C)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct Test {
            nb_1: u16,
            nb_2: u8,
            nb_3: usize,
            nb_4: u128,
        }

        let test = Test {
            nb_1: 0xabcd,
            nb_2: 0x99,
            nb_3: 0x1234,
            nb_4: 0x1234_5678_90ab_cdef,
        };
        let test_bytes = unsafe { slice::from_raw_parts(addr_of!(test).cast::<u8>(), size_of::<Test>()) };

        let mut device = vec![0_u8; 1024];
        unsafe {
            Device::<u8, std::io::Error>::write_at(&mut device, Address::try_from(OFFSET).unwrap(), test).unwrap();
        };

        let slice = Device::<u8, std::io::Error>::slice(
            &device,
            Address::try_from(OFFSET).unwrap()..Address::try_from(OFFSET + size_of::<Test>() as u64).unwrap(),
        )
        .unwrap();

        assert_eq!(test_bytes, slice.as_ref());
    }
}
