//! Errors related to Ext2 manipulation.

use core::error;
use core::fmt::{self, Display};

use super::superblock::EXT2_SIGNATURE;
use crate::file::Type;

/// Enumeration of possible errors encountered with Ext2's manipulation.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug, PartialEq, Eq)]
pub enum Ext2Error {
    /// A bad file type has been found during the parsing of the inode with the given inode number.
    BadFileType(u16),

    /// A bad magic number has been found during the superblock parsing.
    ///
    /// See [this table](https://wiki.osdev.org/Ext2#Base_Superblock_Fields) for reference.
    BadMagic(u16),

    /// A ill-formed C-string has been found during a name parsing.
    BadString,

    /// Given code does not correspond to a valid file system state.
    ///
    /// See [this table](https://wiki.osdev.org/Ext2#File_System_States) for reference.
    InvalidState(u16),

    /// Given code does not correspond to a valid error handling method.
    ///
    /// See [this table](https://wiki.osdev.org/Ext2#Error_Handling_Methods) for reference.
    InvalidErrorHandlingMethod(u16),

    /// Given code does not correspond to a valid compression algorithm.
    ///
    /// See [this table](https://www.nongnu.org/ext2-doc/ext2.html#s-algo-bitmap) for reference.
    InvalidCompressionAlgorithm(u32),

    /// Tried to access an extended field in a basic superblock.
    NoExtendedFields,

    /// Tried to access a non-existing block group.
    NonExistingBlockGroup(u32),

    /// Tried to access a non-existing inode.
    NonExistingInode(u32),

    /// Tried to assign a wrong type to a file.
    WrongFileType(Type, Type),
}

impl Display for Ext2Error {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadFileType(mode) => {
                write!(formatter, "Bad File Type: an inode contain the mode {mode}, which does not correspond to a valid file type")
            },
            Self::BadMagic(magic) => write!(formatter, "Bad Magic: {magic} has been found while {EXT2_SIGNATURE} was expected"),
            Self::BadString => write!(formatter, "Bad String: a ill-formed C-string has been found"),
            Self::InvalidState(state) => write!(formatter, "Invalid State: {state} has been found while 1 or 2 was expected"),
            Self::InvalidErrorHandlingMethod(method) => {
                write!(formatter, "Invalid Error Handling Method: {method} was found while 1, 2 or 3 was expected")
            },
            Self::InvalidCompressionAlgorithm(id) => {
                write!(formatter, "Invalid Compression Algorithm: {id} was found while 0, 1, 2, 3 or 4 was expected")
            },
            Self::NoExtendedFields => write!(
                formatter,
                "No Extend Field: tried to access an extended field in a superblock that only contains basic fields"
            ),
            Self::NonExistingBlockGroup(nth) => {
                write!(formatter, "Non Existing Block Group: tried to access the {nth} block group which does not exist")
            },
            Self::NonExistingInode(nth) => {
                write!(formatter, "Non Existing Inode: tried to access the {nth} inode which does not exist")
            },
            Self::WrongFileType(expected, given) => {
                write!(formatter, "Wrong File Type: {expected:?} file type expected, {given:?} given")
            },
        }
    }
}

impl error::Error for Ext2Error {}

impl Ext2Error {
    /// Converts an [`Ext2Error`] into a `static str` in constant time.
    #[inline]
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::BadFileType(_) => "Bad File Type",
            Self::BadMagic(_) => "Bad Magic",
            Self::BadString => "Bad String",
            Self::InvalidState(_) => "Invalid State",
            Self::InvalidErrorHandlingMethod(_) => "Invalid Error Hanling Method",
            Self::InvalidCompressionAlgorithm(_) => "Invalid Compression Algorithm",
            Self::NoExtendedFields => "No Extended Fields",
            Self::NonExistingBlockGroup(_) => "Non Existing Block Group",
            Self::NonExistingInode(_) => "Non Existing Inode",
            Self::WrongFileType(_, _) => "Wrong File Type",
        }
    }
}
