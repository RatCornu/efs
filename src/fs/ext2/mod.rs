//! Implementation of the Second Extended Filesystem (ext2fs) filesystem.
//!
//! See [its Wikipedia page](https://fr.wikipedia.org/wiki/Ext2), [its OSDev page](https://wiki.osdev.org/Ext2), and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html) for more information.

use alloc::vec;
use alloc::vec::Vec;
use core::mem::size_of;

use self::block::Block;
use self::block_group::BlockGroupDescriptor;
use self::error::Ext2Error;
use self::file::{Directory, File, Regular, SymbolicLink};
use self::inode::Inode;
use self::superblock::{Superblock, SUPERBLOCK_START_BYTE};
use crate::dev::celled::Celled;
use crate::dev::sector::Address;
use crate::dev::Device;
use crate::error::Error;
use crate::file::{Type, TypeWithFile};
use crate::fs::error::FsError;

pub mod block;
pub mod block_group;
pub mod directory;
pub mod error;
pub mod file;
pub mod inode;
pub mod superblock;

/// Type alias to reduce complexity in functions' types.
#[allow(clippy::module_name_repetitions)]
pub type Ext2TypeWithFile<Dev> = TypeWithFile<Ext2Error, Regular<Dev>, SymbolicLink<Dev>, File<Dev>, Directory<Dev>>;

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

    /// Updates the inner [`Superblock`].
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the device cannot be read.
    fn update_inner_superblock(&mut self) -> Result<(), Error<Ext2Error>> {
        self.superblock = Superblock::parse(&self.device)?;
        Ok(())
    }

    /// Sets the device's superblock to the given object.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the device cannot be written.
    ///
    /// # Safety
    ///
    /// Must ensure that the given superblock is coherent with the current state of the filesystem.
    unsafe fn set_superblock(&mut self, superblock: &Superblock) -> Result<(), Error<Ext2Error>> {
        self.update_inner_superblock()?;
        let mut device = self.device.borrow_mut();

        device.write_at(Address::new(SUPERBLOCK_START_BYTE), superblock.base())?;

        if let Some(extended) = superblock.extended_fields() {
            device.write_at(Address::new(SUPERBLOCK_START_BYTE + size_of::<superblock::Base>()), extended)?;
        }

        Ok(())
    }

    /// Sets the counter of free blocks in the superblock.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the device cannot be written.
    ///
    /// # Safety
    ///
    /// Must ensure that the given `value` corresponds to the real count of free blocks in the filesystem.
    unsafe fn set_free_blocks(&mut self, value: u32) -> Result<(), Error<Ext2Error>> {
        let mut superblock = self.superblock().clone();
        superblock.base_mut().free_blocks_count = value;

        self.set_superblock(&superblock)
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

    /// Returns a [`Vec`] containing the block numbers of `n` free blocks.
    ///
    /// # Errors
    ///
    /// Returns an [`NotEnoughFreeBlocks`](Ext2Error::NotEnoughFreeBlocks) error if requested more free blocks than available.
    ///
    /// Returns an [`Error`] if the device cannot be read.
    #[inline]
    pub fn free_blocks(&self, n: u32) -> Result<Vec<u32>, Error<Ext2Error>> {
        if n == 0 {
            return Ok(vec![]);
        }

        let fs = self.borrow();

        if n > fs.superblock().base().free_blocks_count {
            return Err(Error::Fs(FsError::Implementation(Ext2Error::NotEnoughFreeBlocks(
                n,
                fs.superblock().base().free_blocks_count,
            ))));
        }

        let mut free_blocks = Vec::new();

        for block_group_count in 0_u32..fs.superblock().base().block_group_count() {
            let block_group_descriptor = BlockGroupDescriptor::parse(&fs.device, fs.superblock(), block_group_count)?;
            let mut block_group_bitmap_block = Block::new(self.clone(), block_group_descriptor.block_bitmap);
            let block_group_bitmap = block_group_bitmap_block.read_all()?;
            for (index, eight_blocks_bitmap) in block_group_bitmap.iter().enumerate() {
                // SAFETY: a block size is usually at most thousands of bytes, which is smaller than `u32::MAX`
                let index = unsafe { u32::try_from(index).unwrap_unchecked() };
                for bit in 0_u32..8_u32 {
                    if (eight_blocks_bitmap >> bit) & 0x01 == 0x00 {
                        free_blocks.push(block_group_count * fs.superblock().base().blocks_per_group + index * 8 + bit);
                        // SAFETY: free_blocks.len() is smaller than n  which is a u32 (not equal to 0xFFFF)
                        if unsafe { u32::try_from(free_blocks.len()).unwrap_unchecked() } == n {
                            return Ok(free_blocks);
                        }
                    }
                }
            }
        }

        // SAFETY: free_blocks.len() is smaller than n  which is a u32 (not equal to 0xFFFF)
        Err(Error::Fs(FsError::Implementation(Ext2Error::NotEnoughFreeBlocks(n, unsafe {
            free_blocks.len().try_into().unwrap_unchecked()
        }))))
    }
}

#[cfg(test)]
mod test {
    use core::cell::RefCell;
    use std::fs::File;

    use itertools::Itertools;

    use super::inode::ROOT_DIRECTORY_INODE;
    use super::Ext2;
    use crate::dev::celled::Celled;
    use crate::file::Type;

    #[test]
    fn base_fs() {
        let device = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let ext2 = Ext2::new(device, 0).unwrap();
        let root = ext2.inode(ROOT_DIRECTORY_INODE).unwrap();
        assert_eq!(root.file_type().unwrap(), Type::Directory);
    }

    #[test]
    fn free_blocks() {
        let device = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let ext2 = Ext2::new(device, 0).unwrap();
        let fs = Celled::new(ext2);
        let free_blocks = fs.free_blocks(1_024).unwrap();

        assert!(free_blocks.iter().all_unique());
    }
}
