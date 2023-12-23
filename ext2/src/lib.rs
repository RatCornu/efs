//! Implementation of the Second Extended Filesystem (ext2fs) filesystem.
//!
//! See [its Wikipedia page](https://fr.wikipedia.org/wiki/Ext2), [its OSDev page](https://wiki.osdev.org/Ext2), and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html) for more information.

#![cfg_attr(all(not(test), not(feature = "std")), no_std)]
#![deny(
    clippy::complexity,
    clippy::correctness,
    clippy::nursery,
    clippy::pedantic,
    clippy::perf,
    clippy::restriction,
    clippy::style,
    missing_docs
)]
#![allow(
    clippy::absolute_paths,
    clippy::arithmetic_side_effects,
    clippy::as_conversions,
    clippy::blanket_clippy_restriction_lints,
    clippy::else_if_without_else,
    clippy::exhaustive_enums,
    clippy::exhaustive_structs,
    clippy::expect_used,
    clippy::implicit_return,
    clippy::integer_division,
    clippy::match_same_arms,
    clippy::match_wildcard_for_single_variants,
    clippy::missing_trait_methods,
    clippy::mod_module_files,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::pattern_type_mismatch,
    clippy::question_mark_used,
    clippy::separated_literal_suffix,
    clippy::shadow_reuse,
    clippy::shadow_unrelated,
    clippy::todo,
    clippy::unreachable,
    clippy::use_debug,
    clippy::unwrap_in_result,
    clippy::wildcard_in_or_patterns,
    const_item_mutation
)]
#![cfg_attr(
    test,
    allow(
        clippy::assertions_on_result_states,
        clippy::collection_is_never_read,
        clippy::enum_glob_use,
        clippy::indexing_slicing,
        clippy::non_ascii_literal,
        clippy::too_many_lines,
        clippy::undocumented_unsafe_blocks,
        clippy::unwrap_used,
        clippy::wildcard_imports
    )
)]
#![feature(error_in_core)]

extern crate alloc;
extern crate core;
#[cfg(feature = "std")]
extern crate std;

use alloc::rc::Rc;
use core::cell::RefCell;

use base::dev::Device;
use base::error::Error;
use base::file::{Type, TypeWithFile};
use base::fs::error::FsError;
use derive_more::{Deref, DerefMut};

use self::error::Ext2Error;
use self::file::{Directory, File, Regular, SymbolicLink};
use self::inode::Inode;
use self::superblock::Superblock;

pub mod block_group;
pub mod directory;
pub mod error;
pub mod file;
pub mod inode;
pub mod superblock;

/// Type alias for celled objects.
#[derive(Deref, DerefMut)]
pub struct Celled<T>(Rc<RefCell<T>>);

impl<T> Clone for Celled<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl<T> Celled<T> {
    /// Creates a new celled object.
    #[inline]
    pub fn new(obj: T) -> Self {
        Self(Rc::new(RefCell::new(obj)))
    }
}

/// Type alias to reduce complexity in functions' types.
#[allow(clippy::module_name_repetitions)]
pub type Ext2TypeWithFile<Dev> = TypeWithFile<Regular<Dev>, SymbolicLink<Dev>, File<Dev>, Directory<Dev>>;

/// Main interface for devices containing an ext2 filesystem.
#[derive(Clone)]
pub struct Ext2<Dev: Device<u8, Ext2Error>> {
    /// Device number of the device containing the ext2 filesystem.
    device_id: u32,

    /// Device containing the ext2 filesystem.
    device: Celled<Dev>,

    /// Superblock of the filesystem.
    superblock: Superblock,
}

impl<Dev: Device<u8, Ext2Error>> Ext2<Dev> {
    /// Creates a new [`Ext2`] object from the given device that should contain an ext2 filesystem and a given device ID.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the device could not be read of if no ext2 filesystem is found on this device.
    #[inline]
    pub fn new(device: Dev, device_id: u32) -> Result<Self, Error<Ext2Error>> {
        let celled_device = Celled::new(device);
        let superblock = Superblock::parse(&celled_device)?;
        Ok(Self {
            device: celled_device,
            device_id,
            superblock,
        })
    }

    /// Returns the [`Superblock`] of this filesystem.
    #[inline]
    #[must_use]
    pub const fn superblock(&self) -> &Superblock {
        &self.superblock
    }

    /// Returns the [`Inode`] with the given number.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Inode::parse`].
    #[inline]
    pub fn inode(&self, inode_number: u32) -> Result<Inode, Error<Ext2Error>> {
        Inode::parse(&self.device, &self.superblock, inode_number)
    }
}

impl<Dev: Device<u8, Ext2Error>> Celled<Ext2<Dev>> {
    /// Returns a [`File`](crate::file::File) directly read on this filesystem.
    ///
    /// # Errors
    ///
    /// Returns an [`BadFileType`](Ext2Error::BadFileType) if the type of the file pointed by the given inode is ill-formed.
    ///
    /// Otherwise, returns the same errors as [`Inode::parse`].
    #[inline]
    pub fn file(&self, inode_number: u32) -> Result<Ext2TypeWithFile<Dev>, Error<Ext2Error>> {
        let filesystem = self.borrow();
        let inode = filesystem.inode(inode_number)?;
        match inode.file_type().map_err(|err| Error::Fs(FsError::Implementation(err)))? {
            Type::Regular => Ok(TypeWithFile::Regular(Regular::new(&self.clone(), inode_number)?)),
            Type::Directory => Ok(TypeWithFile::Directory(Directory::new(&self.clone(), inode_number)?)),
            Type::SymbolicLink => Ok(TypeWithFile::SymbolicLink(SymbolicLink::new(&self.clone(), inode_number)?)),
            Type::Fifo | Type::CharacterDevice | Type::BlockDevice | Type::Socket | Type::Other => unreachable!(
                "The only type of files in ext2's filesystems that are written on the device are the regular files, the directories and the symbolic links"
            ),
        }
    }
}

#[cfg(test)]
mod test {
    use core::cell::RefCell;
    use std::fs::File;

    use base::file::Type;

    use super::inode::ROOT_DIRECTORY_INODE;
    use super::Ext2;

    #[test]
    fn base_fs() {
        let device = RefCell::new(File::options().read(true).write(true).open("./tests//base.ext2").unwrap());
        let ext2 = Ext2::new(device, 0).unwrap();
        let root = ext2.inode(ROOT_DIRECTORY_INODE).unwrap();
        assert_eq!(root.file_type().unwrap(), Type::Directory);
    }
}
