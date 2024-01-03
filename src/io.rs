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

#[cfg(feature = "std")]
impl<E: core::error::Error, S: std::io::Read> Read<E> for S {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error<E>> {
        std::io::Read::read(self, buf).map_err(|err| Error::IO(err))
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

#[cfg(feature = "std")]
impl<E: core::error::Error, S: std::io::Write> Write<E> for S {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error<E>> {
        std::io::Write::write(self, buf).map_err(|err| Error::IO(err))
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Error<E>> {
        std::io::Write::flush(self).map_err(|err| Error::IO(err))
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

#[cfg(feature = "std")]
impl From<std::io::SeekFrom> for SeekFrom {
    #[inline]
    fn from(value: std::io::SeekFrom) -> Self {
        match value {
            std::io::SeekFrom::Start(value) => Self::Start(value),
            std::io::SeekFrom::End(value) => Self::End(value),
            std::io::SeekFrom::Current(value) => Self::Current(value),
        }
    }
}

#[cfg(feature = "std")]
impl From<SeekFrom> for std::io::SeekFrom {
    #[inline]
    fn from(value: SeekFrom) -> Self {
        match value {
            SeekFrom::Start(value) => Self::Start(value),
            SeekFrom::End(value) => Self::End(value),
            SeekFrom::Current(value) => Self::Current(value),
        }
    }
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

#[cfg(feature = "std")]
impl<E: core::error::Error, S: std::io::Seek> Seek<E> for S {
    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Error<E>> {
        std::io::Seek::seek(self, pos.into()).map_err(|err| Error::IO(err))
    }
}
