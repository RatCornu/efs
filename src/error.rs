//! Interface for `efs` possible errors

use core::error;
use core::fmt::{self, Display};

use no_std_io::io;

use crate::dev::error::DevError;
use crate::fs::FsError;
use crate::path::PathError;

/// Enumeration of possible sources of error
#[allow(clippy::error_impl_error)]
#[derive(Debug)]
pub enum Error<E: error::Error> {
    /// Device error
    Device(DevError),

    /// Filesystem error
    Fs(FsError),

    /// I/O error
    IO(io::Error),

    /// Path error
    Path(PathError),

    /// Error comming from another source (e.g filesystem implementation)
    Other(E),
}

impl<E: error::Error> Display for Error<E> {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Device(device_error) => write!(formatter, "Device Error: {device_error}"),
            Self::Fs(fs_error) => write!(formatter, "Filesystem Error: {fs_error}"),
            Self::IO(io_error) => write!(formatter, "I/O Error: {io_error:?}"),
            Self::Path(path_error) => write!(formatter, "Path Error: {path_error}"),
            Self::Other(other_error) => write!(formatter, "{other_error}"),
        }
    }
}

impl<E: error::Error> error::Error for Error<E> {}

impl<E: error::Error> From<io::Error> for Error<E> {
    #[inline]
    fn from(value: io::Error) -> Self {
        Self::IO(value)
    }
}
