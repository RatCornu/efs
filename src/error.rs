//! Interface for `efs` possible errors

use core::error;
use core::fmt::{self, Display};

use crate::dev::error::DevError;
use crate::fs::error::FsError;
use crate::path::PathError;

/// Enumeration of possible sources of error
#[allow(clippy::error_impl_error)]
#[derive(Debug)] // TODO: use thiserror to simplify error usage
pub enum Error<E: core::error::Error> {
    /// Device error
    Device(DevError),

    /// Filesystem error
    Fs(FsError<E>),

    /// Path error
    Path(PathError),

    /// Standard I/O error
    #[cfg(any(feature = "std", test))]
    IO(std::io::Error),
}

impl<E: core::error::Error> Display for Error<E> {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Device(device_error) => write!(formatter, "Device Error: {device_error}"),
            Self::Fs(fs_error) => write!(formatter, "Filesystem Error: {fs_error}"),
            Self::Path(path_error) => write!(formatter, "Path Error: {path_error}"),
            #[cfg(any(feature = "std", test))]
            Self::IO(io_error) => write!(formatter, "I/O Error: {io_error}"),
        }
    }
}

impl<E: core::error::Error> error::Error for Error<E> {}

impl<E: core::error::Error> From<E> for Error<E> {
    #[inline]
    fn from(value: E) -> Self {
        Self::Fs(FsError::Implementation(value))
    }
}
