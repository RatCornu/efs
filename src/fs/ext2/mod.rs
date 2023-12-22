//! Implementation of the Second Extended Filesystem (ext2fs) filesystem.
//!
//! See [its Wikipedia page](https://fr.wikipedia.org/wiki/Ext2), [its OSDev page](https://wiki.osdev.org/Ext2), and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html) for more information.

use alloc::rc::Rc;
use core::cell::RefCell;

use derive_more::{Deref, DerefMut};

use self::error::Ext2Error;
use self::file::{Directory, File, Regular, SymbolicLink};
use self::inode::Inode;
use self::superblock::Superblock;
use super::error::FsError;
use crate::dev::Device;
use crate::error::Error;
use crate::file::{Type, TypeWithFile};

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

/// TODO
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

    /// TODO
    ///
    /// # Errors
    ///
    /// TODO
    #[inline]
    pub fn file(&self, inode_number: u32) -> Result<Ext2TypeWithFile<Dev>, Error<Ext2Error>> {
        let inode = self.inode(inode_number)?;
        match inode.file_type().map_err(|err| Error::Fs(FsError::Implementation(err)))? {
            Type::Regular => todo!(),
            Type::Directory => todo!(),
            Type::SymbolicLink => todo!(),
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

    use super::inode::ROOT_DIRECTORY_INODE;
    use super::Ext2;
    use crate::file::Type;

    #[test]
    fn base_fs() {
        let device = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let ext2 = Ext2::new(device, 0).unwrap();
        let root = ext2.inode(ROOT_DIRECTORY_INODE).unwrap();
        assert_eq!(root.file_type().unwrap(), Type::Directory);
    }
}
