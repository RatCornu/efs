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

    /// Tried to set as free a block already free.
    BlockAlreadyFree(u32),

    /// Tried to set as used a block already in use.
    BlockAlreadyInUse(u32),

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

    /// Tried to access a non-existing block.
    NonExistingBlock(u32),

    /// Tried to access a non-existing inode.
    NonExistingInode(u32),

    /// Requested more free blocks than currently available.
    NotEnoughFreeBlocks(u32, u32),

    /// Tried to access a byte which is out of bounds.
    OutOfBounds(i128),

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
            Self::BlockAlreadyFree(nth) => {
                write!(formatter, "Block Already Free: tried to set the {nth} block free while already being free")
            },
            Self::BlockAlreadyInUse(nth) => {
                write!(formatter, "Block Already in Use: tried to set the {nth} block in use while already being used")
            },
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
            Self::NonExistingBlock(nth) => {
                write!(formatter, "Non Existing Block: tried to access the {nth} block which does not exist")
            },
            Self::NonExistingInode(nth) => {
                write!(formatter, "Non Existing Inode: tried to access the {nth} inode which does not exist")
            },
            Self::NotEnoughFreeBlocks(requested, available) => {
                write!(formatter, "Not Enough Free Blocks: requested {requested} free blocks while only {available} are available")
            },
            Self::OutOfBounds(byte) => {
                write!(formatter, "Out of Bounds: tried to access the {byte}th byte which is out of bounds")
            },
            Self::WrongFileType(expected, given) => {
                write!(formatter, "Wrong File Type: {expected:?} file type expected, {given:?} given")
            },
        }
    }
}

impl error::Error for Ext2Error {}
