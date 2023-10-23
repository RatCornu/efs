//! Interface for `efs` possible errors

use core::error;
use core::fmt::{self, Display};

use no_std_io::io;

use crate::fs::FsError;
use crate::path::PathError;

/// Enumeration of possible sources of error
#[allow(clippy::error_impl_error)]
#[derive(Debug)]
pub enum Error {
    /// I/O error
    IO(io::ErrorKind),

    /// Path error
    Path(PathError),

    /// Filesystem error
    Fs(FsError),
}

impl Display for Error {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IO(io_error) => write!(formatter, "I/O Error: {io_error:?}"),
            Self::Path(path_error) => write!(formatter, "Path Error: {path_error}"),
            Self::Fs(fs_error) => write!(formatter, "Filesystem Error: {fs_error}"),
        }
    }
}

impl error::Error for Error {}
