//! Implementation of the Second Extended Filesystem (ext2fs) filesystem.
//!
//! See [its Wikipedia page](https://fr.wikipedia.org/wiki/Ext2), [its kernel.org page](https://www.kernel.org/doc/html/latest/filesystems/ext2.html), [its OSDev page](https://wiki.osdev.org/Ext2), and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html) for more information.

use alloc::vec;
use alloc::vec::Vec;
use core::mem::size_of;

use self::block_group::BlockGroupDescriptor;
use self::error::Ext2Error;
use self::file::{Directory, Regular, SymbolicLink};
use self::inode::{Inode, ROOT_DIRECTORY_INODE};
use self::superblock::{Superblock, SUPERBLOCK_START_BYTE};
use super::FileSystem;
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
pub mod indirection;
pub mod inode;
pub mod superblock;

/// Type alias to reduce complexity in functions' types.
#[allow(clippy::module_name_repetitions)]
pub type Ext2TypeWithFile<Dev> = TypeWithFile<Directory<Dev>>;

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

    /// Creates a new [`Ext2`] object from the given celled device that should contain an ext2 filesystem and a given device ID.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the device could not be read of if no ext2 filesystem is found on this device.
    #[inline]
    pub fn new_celled(celled_device: Celled<Dev>, device_id: u32) -> Result<Self, Error<Ext2Error>> {
        let superblock = Superblock::parse(&celled_device)?;
        Ok(Self {
            device_id,
            device: celled_device,
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

        device.write_at(Address::new(SUPERBLOCK_START_BYTE), *superblock.base())?;

        if let Some(extended) = superblock.extended_fields() {
            device.write_at(Address::new(SUPERBLOCK_START_BYTE + size_of::<superblock::Base>()), *extended)?;
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

    /// Returns the block bitmap for the given block group.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`BlockGroupDescriptor::parse`](block_group/struct.BlockGroupDescriptor.html#method.parse).
    #[inline]
    pub fn get_block_bitmap(&self, block_group_number: u32) -> Result<Vec<u8>, Error<Ext2Error>> {
        let superblock = self.superblock();

        let block_group_descriptor = BlockGroupDescriptor::parse(&self.device, superblock, block_group_number)?;
        let starting_addr = Address::new((block_group_descriptor.block_bitmap * superblock.block_size()) as usize);

        Ok(self
            .device
            .borrow()
            .slice(starting_addr..starting_addr + (superblock.base().blocks_per_group / 8) as usize)?
            .as_ref()
            .to_vec())
    }

    /// Sets the block bitmap for the given block group as the given bitmap.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`BlockGroupDescriptor::parse`](block_group/struct.BlockGroupDescriptor.html#method.parse).
    ///
    /// # Panics
    ///
    /// This will panic if `block_bitmap.len() == superblock.blocks_per_group` is false.
    ///
    /// # Safety
    ///
    /// Must ensure that the given `block_bitmap` is coherent with the current filesystem's state.
    unsafe fn set_block_bitmap(&self, block_group_number: u32, block_bitmap: &[u8]) -> Result<(), Error<Ext2Error>> {
        let superblock = self.superblock();

        let block_group_descriptor = BlockGroupDescriptor::parse(&self.device, superblock, block_group_number)?;
        let starting_addr = Address::new((block_group_descriptor.block_bitmap * superblock.block_size()) as usize);

        let mut device = self.device.borrow_mut();
        let mut slice = device.slice(starting_addr..starting_addr + (superblock.base().blocks_per_group / 8) as usize)?;
        slice.clone_from_slice(block_bitmap);
        let commit = slice.commit();
        device.commit(commit)?;

        Ok(())
    }

    /// Returns a [`Vec`] containing the block numbers of `n` free blocks.
    ///
    /// Looks for free blocks starting at the block group `start_block_group`.
    ///
    /// # Errors
    ///
    /// Returns an [`NotEnoughFreeBlocks`](Ext2Error::NotEnoughFreeBlocks) error if requested more free blocks than available.
    ///
    /// Returns an [`Error`] if the device cannot be read.
    #[inline]
    pub fn free_blocks_offset(&self, n: u32, start_block_group: u32) -> Result<Vec<u32>, Error<Ext2Error>> {
        if n == 0 {
            return Ok(vec![]);
        }

        if n > self.superblock().base().free_blocks_count {
            return Err(Error::Fs(FsError::Implementation(Ext2Error::NotEnoughFreeBlocks(
                n,
                self.superblock().base().free_blocks_count,
            ))));
        }

        let total_block_group_count = self.superblock().base().block_group_count();

        let mut free_blocks = Vec::new();

        for mut block_group_count in 0_u32..total_block_group_count {
            block_group_count = (block_group_count + start_block_group) % total_block_group_count;

            let block_group_descriptor = BlockGroupDescriptor::parse(&self.device, self.superblock(), block_group_count)?;
            if block_group_descriptor.free_blocks_count > 0 {
                let bitmap = self.get_block_bitmap(block_group_count)?;
                for (index, byte) in bitmap.into_iter().enumerate() {
                    // SAFETY: a block size is usually at most thousands of bytes, which is smaller than `u32::MAX`
                    let index = unsafe { u32::try_from(index).unwrap_unchecked() };

                    if byte != u8::MAX {
                        for bit in 0_u32..8 {
                            if (byte >> bit) & 1 == 0 {
                                free_blocks.push(block_group_count * self.superblock().base().blocks_per_group + index * 8 + bit);

                                if free_blocks.len() as u64 == u64::from(n) {
                                    return Ok(free_blocks);
                                }
                            }
                        }
                    }
                }
            }
        }

        // SAFETY: free_blocks.len() is smaller than n  which is a u32
        Err(Error::Fs(FsError::Implementation(Ext2Error::NotEnoughFreeBlocks(n, unsafe {
            free_blocks.len().try_into().unwrap_unchecked()
        }))))
    }

    /// Returns a [`Vec`] containing the block numbers of `n` free blocks.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`free_blocks_offset`](struct.Celled.html#method.free_blocks_offset).
    #[inline]
    pub fn free_blocks(&self, n: u32) -> Result<Vec<u32>, Error<Ext2Error>> {
        self.free_blocks_offset(n, 0)
    }

    /// Sets all the given `blocs` as `usage` in their bitmap, and updates the block group descriptors and the superblock
    /// accordingly.
    ///
    /// # Errors
    ///
    /// Returns an [`BlockAlreadyInUse`](Ext2Error::BlockAlreadyInUse) error if it tries to allocate a block that was already in
    /// use.
    ///
    /// Returns an [`BlockAlreadyFree`](Ext2Error::BlockAlreadyFree) error if it tries to deallocate a block that was already free.
    ///
    /// Returns an [`NonExistingBlock`](Ext2Error::NonExistingBlock) error if a given block does not exist.
    ///
    /// Otherwise, returns the same errors as [`get_block_bitmap`](struct.Ext2.html#method.get_block_bitmap).
    #[inline]
    fn locate_blocks(&mut self, blocks: &[u32], usage: bool) -> Result<(), Error<Ext2Error>> {
        /// Updates the block group bitmap and the free block count in the descriptor.
        ///
        /// # Errors
        ///
        /// Returns an [`Error`] if the device cannot be written.
        ///
        /// # Safety
        ///
        /// Must ensure that the `number_blocks_changed_in_group` is coherent with the given `bitmap`.
        unsafe fn update_block_group<Dev: Device<u8, Ext2Error>>(
            ext2: &Ext2<Dev>,
            block_group_number: u32,
            number_blocks_changed_in_group: u16,
            bitmap: &[u8],
            usage: bool,
        ) -> Result<(), Error<Ext2Error>> {
            ext2.set_block_bitmap(block_group_number, bitmap)?;

            let mut new_block_group_descriptor = BlockGroupDescriptor::parse(&ext2.device, ext2.superblock(), block_group_number)?;

            if usage {
                new_block_group_descriptor.free_blocks_count -= number_blocks_changed_in_group;
                ext2.device.borrow_mut().write_at(
                    BlockGroupDescriptor::starting_addr(ext2.superblock(), block_group_number)?,
                    new_block_group_descriptor,
                )
            } else {
                new_block_group_descriptor.free_blocks_count += number_blocks_changed_in_group;
                ext2.device.borrow_mut().write_at(
                    BlockGroupDescriptor::starting_addr(ext2.superblock(), block_group_number)?,
                    new_block_group_descriptor,
                )
            }
        }

        let block_opt = blocks.first();

        let mut number_blocks_changed_in_group = 0_u16;
        // SAFETY: the total number of blocks in the filesystem is a u32
        let total_number_blocks_changed = unsafe { u32::try_from(blocks.len()).unwrap_unchecked() };

        if let Some(block) = block_opt {
            let mut block_group_number = block / self.superblock().base().blocks_per_group;
            let mut bitmap = self.get_block_bitmap(block / self.superblock().base().blocks_per_group)?;

            for block in blocks {
                if block / self.superblock().base().blocks_per_group != block_group_number {
                    // SAFETY: the state of the filesystem stays coherent within this function
                    unsafe {
                        update_block_group(self, block_group_number, number_blocks_changed_in_group, &bitmap, usage)?;
                    };

                    number_blocks_changed_in_group = 0;

                    block_group_number = block / self.superblock().base().blocks_per_group;
                    bitmap = self.get_block_bitmap(block_group_number)?;
                }

                number_blocks_changed_in_group += 1;

                let group_index = block % self.superblock().base().blocks_per_group;
                let bitmap_index = group_index / 8;
                let bitmap_offset = group_index % 8;

                let Some(byte) = bitmap.get_mut(bitmap_index as usize) else {
                    return Err(Error::Fs(FsError::Implementation(Ext2Error::NonExistingBlock(*block))));
                };

                if usage && *byte >> bitmap_offset & 1 == 1 {
                    return Err(Error::Fs(FsError::Implementation(Ext2Error::BlockAlreadyInUse(*block))));
                } else if !usage && *byte >> bitmap_offset & 1 == 0 {
                    return Err(Error::Fs(FsError::Implementation(Ext2Error::BlockAlreadyFree(*block))));
                }

                *byte ^= 1 << bitmap_offset;
            }

            // SAFETY: the state of the filesystem stays coherent within this function
            unsafe {
                update_block_group(self, block_group_number, number_blocks_changed_in_group, &bitmap, usage)?;
            };
        }

        if usage {
            // SAFETY: the total number of free blocks is the one before minus the total number of allocated blocks
            unsafe {
                self.set_free_blocks(self.superblock().base().free_blocks_count - total_number_blocks_changed)?;
            };
        } else {
            // SAFETY: the total number of free blocks is the one before plus the total number of deallocated blocks
            unsafe {
                self.set_free_blocks(self.superblock().base().free_blocks_count + total_number_blocks_changed)?;
            };
        }

        Ok(())
    }

    /// Sets all the given `blocs` as "used".
    ///
    /// # Errors
    ///
    /// Returns an [`BlockAlreadyInUse`](Ext2Error::BlockAlreadyInUse) error if the given block was already in use.
    ///
    /// Otherwise, returns the same errors as [`get_block_bitmap`](struct.Ext2.html#method.get_block_bitmap).
    #[inline]
    pub fn allocate_blocks(&mut self, blocks: &[u32]) -> Result<(), Error<Ext2Error>> {
        self.locate_blocks(blocks, true)
    }

    /// Sets all the given `blocs` as "free".
    ///
    /// # Errors
    ///
    /// Returns an [`BlockAlreadyFree`](Ext2Error::BlockAlreadyFree) error if the given block was already in use.
    ///
    /// Otherwise, returns the same errors as [`get_block_bitmap`](struct.Ext2.html#method.get_block_bitmap).
    #[inline]
    pub fn deallocate_blocks(&mut self, blocks: &[u32]) -> Result<(), Error<Ext2Error>> {
        self.locate_blocks(blocks, false)
    }

    /// Finds an unused inode number, writes an empty inode, sets the usage of this inode as `true` and returns the inode number.
    ///
    /// # Errors
    ///
    /// Returns a [`NotEnoughInodes`](Ext2Error::NotEnoughInodes) if no inode is currently available.
    ///
    /// Returns an [`Error`] if the device cannot be read or written.
    #[inline]
    pub fn allocate_inode(&mut self) -> Result<u32, Error<Ext2Error>> {
        todo!()
    }

    /// Sets the usage of this inode as `false` and deallocates every block used by this inode.
    ///
    /// # Errors
    ///
    /// Returns a [`InodeAlreadyFree`](Ext2Error::InodeAlreadyFree) if the given inode is already free.
    ///
    /// Returns an [`Error`] if the device cannot be read or written.
    #[inline]
    pub fn deallocate_inode(&mut self, inode_number: u32) -> Result<(), Error<Ext2Error>> {
        todo!()
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
        match inode.file_type()? {
            Type::Regular => Ok(TypeWithFile::Regular(Regular::new(&self.clone(), inode_number)?)),
            Type::Directory => Ok(TypeWithFile::Directory(Directory::new(&self.clone(), inode_number)?)),
            Type::SymbolicLink => Ok(TypeWithFile::SymbolicLink(SymbolicLink::new(&self.clone(), inode_number)?)),
            Type::Fifo | Type::CharacterDevice | Type::BlockDevice | Type::Socket | Type::Other => unreachable!(
                "The only type of files in ext2's filesystems that are written on the device are the regular files, the directories and the symbolic links"
            ),
        }
    }
}

impl<Dev: Device<u8, Ext2Error>> FileSystem<Directory<Dev>> for Celled<Ext2<Dev>> {
    #[inline]
    fn root(&self) -> Result<Directory<Dev>, Error<<Directory<Dev> as crate::file::File>::Error>> {
        self.file(ROOT_DIRECTORY_INODE).and_then(|root| match root {
            TypeWithFile::Directory(root_dir) => Ok(root_dir),
            TypeWithFile::Regular(_) | TypeWithFile::SymbolicLink(_) | TypeWithFile::Other(_) => {
                Err(Error::Fs(FsError::WrongFileType(Type::Directory, root.into())))
            },
        })
    }

    #[inline]
    fn double_slash_root(&self) -> Result<Directory<Dev>, Error<<Directory<Dev> as crate::file::File>::Error>> {
        self.root()
    }
}

#[cfg(test)]
mod test {
    use core::cell::RefCell;
    use std::fs::{self, File};

    use itertools::Itertools;

    use super::inode::ROOT_DIRECTORY_INODE;
    use super::Ext2;
    use crate::dev::celled::Celled;
    use crate::file::{Directory, Type, TypeWithFile};
    use crate::fs::ext2::block::Block;
    use crate::io::Read;
    use crate::path::UnixStr;

    #[test]
    fn base_fs() {
        let device = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let ext2 = Ext2::new(device, 0).unwrap();
        let root = ext2.inode(ROOT_DIRECTORY_INODE).unwrap();
        assert_eq!(root.file_type().unwrap(), Type::Directory);
    }

    #[test]
    fn fetch_file() {
        let device = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(device, 0).unwrap());

        let TypeWithFile::Directory(root) = ext2.file(ROOT_DIRECTORY_INODE).unwrap() else { panic!() };
        let Some(TypeWithFile::Regular(mut big_file)) = root.entry(UnixStr::new("big_file").unwrap()).unwrap() else { panic!() };

        let mut buf = [0_u8; 1024];
        big_file.read(&mut buf).unwrap();
        assert_eq!(buf.into_iter().all_equal_value(), Ok(1));
    }

    #[test]
    fn get_bitmap() {
        let device = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let ext2 = Ext2::new(device, 0).unwrap();

        assert_eq!(ext2.get_block_bitmap(0).unwrap().len() * 8, ext2.superblock().base().blocks_per_group as usize);
    }

    #[test]
    fn free_block_numbers() {
        let device = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let ext2 = Ext2::new(device, 0).unwrap();
        let free_blocks = ext2.free_blocks(1_024).unwrap();
        let superblock = ext2.superblock().clone();
        let bitmap = ext2.get_block_bitmap(0).unwrap();
        let fs = Celled::new(ext2);

        assert!(free_blocks.iter().all_unique());

        for block in free_blocks {
            assert!(Block::new(fs.clone(), block).is_free(&superblock, &bitmap), "{block}");
        }
    }

    #[test]
    fn free_block_amount() {
        let device = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let ext2 = Ext2::new(device, 0).unwrap();

        for i in 1_u32..1_024 {
            assert_eq!(ext2.free_blocks(i).unwrap().len(), i as usize, "{i}");
        }
    }

    #[test]
    fn free_block_small_allocation_deallocation() {
        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_free_block_small_allocation_deallocation.ext2",
        )
        .unwrap();

        let device = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_free_block_small_allocation_deallocation.ext2")
                .unwrap(),
        );
        let mut ext2 = Ext2::new(device, 0).unwrap();

        let free_blocks = ext2.free_blocks(1_024).unwrap();
        ext2.allocate_blocks(&free_blocks).unwrap();

        let fs = Celled::new(ext2);

        let superblock = fs.borrow().superblock().clone();
        for block in &free_blocks {
            let bitmap = fs.borrow().get_block_bitmap(block / superblock.base().blocks_per_group).unwrap();
            assert!(Block::new(fs.clone(), *block).is_used(&superblock, &bitmap), "Allocation: {block}");
        }

        fs.borrow_mut().deallocate_blocks(&free_blocks).unwrap();

        for block in &free_blocks {
            let bitmap = fs.borrow().get_block_bitmap(block / superblock.base().blocks_per_group).unwrap();
            assert!(Block::new(fs.clone(), *block).is_free(&superblock, &bitmap), "Deallocation: {block}");
        }

        fs::remove_file("./tests/fs/ext2/io_operations_copy_free_block_small_allocation_deallocation.ext2").unwrap();
    }

    #[test]
    fn free_block_big_allocation_deallocation() {
        fs::copy(
            "./tests/fs/ext2/io_operations.ext2",
            "./tests/fs/ext2/io_operations_copy_free_block_big_allocation_deallocation.ext2",
        )
        .unwrap();

        let device = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_free_block_big_allocation_deallocation.ext2")
                .unwrap(),
        );
        let mut ext2 = Ext2::new(device, 0).unwrap();

        let free_blocks = ext2.free_blocks(20_000).unwrap();
        ext2.allocate_blocks(&free_blocks).unwrap();

        let fs = Celled::new(ext2);

        let superblock = fs.borrow().superblock().clone();
        for block in &free_blocks {
            let bitmap = fs.borrow().get_block_bitmap(block / superblock.base().blocks_per_group).unwrap();
            assert!(
                Block::new(fs.clone(), *block).is_used(&superblock, &bitmap),
                "Allocation: {block} ({})",
                block / superblock.base().blocks_per_group
            );
        }

        fs.borrow_mut().deallocate_blocks(&free_blocks).unwrap();

        for block in &free_blocks {
            let bitmap = fs.borrow().get_block_bitmap(block / superblock.base().blocks_per_group).unwrap();
            assert!(Block::new(fs.clone(), *block).is_free(&superblock, &bitmap), "Deallocation: {block}");
        }

        fs::remove_file("./tests/fs/ext2/io_operations_copy_free_block_big_allocation_deallocation.ext2").unwrap();
    }
}
