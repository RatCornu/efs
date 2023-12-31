//! General traits for I/O interfaces.

use crate::error::Error;

/// Allows for reading bytes from a source.
///
/// See [`std::io::Read`] for more information: this trait is a `no_std` based variant.
pub trait Read<E: core::error::Error> {
    /// Pull some bytes from this source into the specified buffer, returning how many bytes were read.
    ///
    /// If the returned number is 0, the reader is considered as ended.
    ///
    /// On a [`Seek`]able reader, a call to this function should increase the offset by the amount of bytes read.
    ///
    /// See [`read`](https://docs.rs/no_std_io/latest/no_std_io/io/trait.Read.html#tymethod.read) for more information.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error<E>>;
}

impl<E: core::error::Error, S: Read<E>> Read<E> for &mut S {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error<E>> {
        (**self).read(buf)
    }
}

/// Allows for writing bytes to a destination.
///
/// See [`std::io::Write`] for more information: this trait is a `no_std` based variant.
pub trait Write<E: core::error::Error> {
    /// Write a buffer into this writer, returning how many bytes were written.
    ///
    /// If the returned number is 0, either the writer is ended or cannot add any more bytes at its end.
    ///
    /// On a [`Seek`]able writer, a call to this function should increase the offset by the amount of bytes read.
    ///
    /// See [`write`](https://docs.rs/no_std_io/latest/no_std_io/io/trait.Write.html#tymethod.write) for more information.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be written.
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error<E>>;

    /// Flush this output stream, ensuring that all intermediately buffered contents reach their destination.
    ///
    /// See [`flush`](https://docs.rs/no_std_io/latest/no_std_io/io/trait.Write.html#tymethod.flush) for more information.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    fn flush(&mut self) -> Result<(), Error<E>>;
}

impl<E: core::error::Error, S: Write<E>> Write<E> for &mut S {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error<E>> {
        (**self).write(buf)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Error<E>> {
        (**self).flush()
    }
}

/// Enumeration of possible methods to seek within an I/O object.
///
/// See [`std::io::SeekFrom`] for more information.
#[derive(Debug, Clone, Copy)]
pub enum SeekFrom {
    /// Sets the offset to the provided number of bytes.
    Start(u64),

    /// Sets the offset to the size of this object plus the specified number of bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it’s an error to seek before byte 0.
    End(i64),

    /// Sets the offset to the current position plus the specified number of bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it’s an error to seek before byte 0.
    Current(i64),
}

/// Provides a cursor which can be moved within a stream of bytes.
///
/// See [`std::io::Seek`] for more information: this trait is a `no_std` based variant.
pub trait Seek<E: core::error::Error> {
    /// Seek to an offset, in bytes, in a stream.
    ///
    /// See [`seek`](https://docs.rs/no_std_io/latest/no_std_io/io/trait.Seek.html#tymethod.seek) for more information.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Error<E>>;
}

impl<E: core::error::Error, S: Seek<E>> Seek<E> for &mut S {
    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Error<E>> {
        (**self).seek(pos)
    }
}
