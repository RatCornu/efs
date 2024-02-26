//! Errors related to filesystems manipulation.

use alloc::string::String;
use core::fmt;
use core::fmt::Display;

use crate::file::Type;

/// Enumeration of possible errors encountered with [`FileSystem`](super::FileSystem)s' manipulation.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub enum FsError<E: core::error::Error> {
    /// Indicates that the given [`File`](crate::file::File) already exist in the given directory.
    EntryAlreadyExist(String),

    /// Indicates that the given [`Path`](crate::path::Path) is too long to be resolved.
    NameTooLong(String),

    /// Indicates that the given filename is not a [`Directory`](crate::file::Directory).
    NotDir(String),

    /// Indicates that the given filename is an symbolic link pointing at an empty string.
    NoEnt(String),

    /// Indicates that the given filename has not been found.
    NotFound(String),

    /// Indicates that a loop has been encountered during the given path resolution.
    Loop(String),

    /// Indicates that this error is coming from the filesystem's implementation.
    Implementation(E),

    /// Tried to assign a wrong type to a file.
    ///
    /// `WrongFileType(expected, given)`
    WrongFileType(Type, Type),
}

impl<E: core::error::Error> Display for FsError<E> {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EntryAlreadyExist(file) => write!(formatter, "Entry Already Exist: \"{file}\" already exist in given directory"),
            Self::Loop(path) => write!(formatter, "Loop: a loop has been encountered during the resolution of \"{path}\""),
            Self::NameTooLong(path) => write!(formatter, "Name too long: \"{path}\" is too long to be resolved"),
            Self::NotDir(filename) => write!(formatter, "Not a Directory: \"{filename}\" is not a directory"),
            Self::NoEnt(filename) => write!(formatter, "No entry: \"{filename}\" is an symbolic link pointing at an empty string"),
            Self::NotFound(filename) => write!(formatter, "Not found: \"{filename}\" has not been found"),
            Self::Implementation(err) => write!(formatter, "{err}"),
            Self::WrongFileType(expected, given) => {
                write!(formatter, "Wrong File Type: {expected:?} file type expected, {given:?} given")
            },
        }
    }
}

impl<E: core::error::Error> core::error::Error for FsError<E> {}
