//! Interface to manipulate blocks.
//!
//! A block is a contiguous part of the disk space. For a given filesystem, all the blocks have the same size, indicated in the
//! [`Superblock`](super::superblock::Superblock).
//!
//! See [the OSDev wiki](https://wiki.osdev.org/Ext2#What_is_a_Block.3F) for more information.

use alloc::vec;
use alloc::vec::Vec;

use super::error::Ext2Error;
use super::Ext2;
use crate::dev::celled::Celled;
use crate::dev::sector::Address;
use crate::dev::Device;
use crate::error::Error;
use crate::fs::error::FsError;
use crate::fs::ext2::block_group::BlockGroupDescriptor;
use crate::io::{Read, Seek, SeekFrom, Write};

/// An ext2 block.
#[derive(Clone)]
pub struct Block<Dev: Device<u8, Ext2Error>> {
    /// Block number.
    number: u32,

    /// Ext2 object associated with the device containing this block.
    filesystem: Celled<Ext2<Dev>>,

    /// Offset for the I/O operations.
    io_offset: u32,
}

impl<Dev: Device<u8, Ext2Error>> Block<Dev> {
    /// Returns a [`Block`] from its number and an [`Ext2`] instance.
    #[inline]
    #[must_use]
    pub const fn new(filesystem: Celled<Ext2<Dev>>, number: u32) -> Self {
        Self {
            number,
            filesystem,
            io_offset: 0,
        }
    }

    /// Returns the containing block group of this block.
    #[inline]
    #[must_use]
    pub fn block_group(&self) -> u32 {
        self.number / self.filesystem.borrow().superblock().base().blocks_per_group
    }

    /// Returns the offset of this block in its containing block group.
    #[inline]
    #[must_use]
    pub fn group_index(&self) -> u32 {
        self.number % self.filesystem.borrow().superblock().base().blocks_per_group
    }

    /// Reads all the content from this block and returns it in a vector.
    ///
    /// The offset for the I/O operations is reset at 0 at the end of this function.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the device cannot be read.
    #[inline]
    pub fn read_all(&mut self) -> Result<Vec<u8>, Error<Ext2Error>> {
        let block_size = self.filesystem.borrow().superblock().block_size();
        let mut buffer = vec![0_u8; block_size as usize];
        self.seek(SeekFrom::Start(0))?;
        self.read(&mut buffer)?;
        self.seek(SeekFrom::Start(0))?;
        Ok(buffer)
    }

    /// Returns whether this block is currently free or not.
    ///
    /// As this operation needs to read directly from the given device, it is quite costly in computational time.
    ///
    /// # Errors
    ///
    /// Returns a [`Error`] if the device cannot be read.
    #[inline]
    pub fn is_free(&self) -> Result<bool, Error<Ext2Error>> {
        let fs = self.filesystem.borrow();

        let block_group = self.block_group();
        let block_group_descriptor = BlockGroupDescriptor::parse(&fs.device, fs.superblock(), block_group)?;
        let mut block_group_descriptor_bitmap_block = Self::new(self.filesystem.clone(), block_group_descriptor.block_bitmap);

        let bitmap_index = u64::from(self.group_index());
        let byte_index = bitmap_index / 8;
        let byte_offset = bitmap_index % 8;

        let mut buffer = [0_u8];
        block_group_descriptor_bitmap_block.seek(SeekFrom::Start(byte_index))?;
        block_group_descriptor_bitmap_block.read(&mut buffer)?;

        Ok((buffer[0] >> byte_offset) & 1 == 0)
    }

    /// Returns whether this block is currently used or not.
    ///
    /// As this operation needs to read directly from the given device, it is quite costly in computational time.
    ///
    /// # Errors
    ///
    /// Returns a [`Error`] if the device cannot be read.
    #[inline]
    pub fn is_used(&self) -> Result<bool, Error<Ext2Error>> {
        self.is_free().map(|is_free| !is_free)
    }

    /// Sets the current block usage in the block bitmap, and updates the superblock accordingly.
    ///
    /// # Errors
    ///
    /// Returns an [`BlockAlreadyInUse`](Ext2Error::BlockAlreadyInUse) error if the given block was already in use.
    ///
    /// Returns an [`BlockAlreadyFree`](Ext2Error::BlockAlreadyFree) error if the given block was already free.
    ///
    /// Otherwise, returns an [`Error`] if the device cannot be written.
    fn set_usage(&mut self, used: bool) -> Result<(), Error<Ext2Error>> {
        let fs = self.filesystem.borrow();

        let block_group = self.block_group();
        let block_group_descriptor = BlockGroupDescriptor::parse(&fs.device, fs.superblock(), block_group)?;
        let mut block_group_descriptor_bitmap_block = Self::new(self.filesystem.clone(), block_group_descriptor.block_bitmap);
        let bitmap_index = self.group_index();

        let byte_index = bitmap_index / 8;
        let byte_offset = bitmap_index % 8;

        let mut buffer = [0_u8];

        block_group_descriptor_bitmap_block.seek(SeekFrom::Start(u64::from(byte_index)))?;
        block_group_descriptor_bitmap_block.read(&mut buffer)?;

        if (buffer[0] >> byte_offset) & 1 == 1 && used {
            Err(Ext2Error::BlockAlreadyInUse(self.number).into())
        } else if (buffer[0] >> byte_offset) & 1 == 0 && !used {
            Err(Ext2Error::BlockAlreadyFree(self.number).into())
        } else {
            buffer[0] ^= 1 << byte_offset;
            block_group_descriptor_bitmap_block.seek(SeekFrom::Current(-1_i64))?;
            block_group_descriptor_bitmap_block.write(&buffer)?;
            Ok(())
        }
    }

    /// Sets the current block as free in the block bitmap, and updates the superblock accordingly.
    ///
    /// # Errors
    ///
    /// Returns an [`BlockAlreadyFree`](Ext2Error::BlockAlreadyFree) error if the given block was already free.
    ///
    /// Otherwise, returns an [`Error`] if the device cannot be written.
    #[inline]
    pub fn set_free(&mut self) -> Result<(), Error<Ext2Error>> {
        self.set_usage(false)?;
        let mut fs = self.filesystem.borrow_mut();
        let current_free_blocks = fs.superblock().base().free_blocks_count;

        // SAFETY:  Assuming that the superblock was initially correct, the number of free blocks increased by 1
        unsafe { fs.set_free_blocks(current_free_blocks + 1) }?;

        Ok(())
    }

    /// Sets the current block as used in the block bitmap, and updates the superblock accordingly.
    ///
    /// # Errors
    ///
    /// Returns an [`BlockAlreadyInUse`](Ext2Error::BlockAlreadyInUse) error if the given block was already in use.
    ///
    /// Otherwise, returns an [`Error`] if the device cannot be written.
    #[inline]
    pub fn set_used(&mut self) -> Result<(), Error<Ext2Error>> {
        self.set_usage(true)?;

        let mut fs = self.filesystem.borrow_mut();
        let current_free_blocks = fs.superblock().base().free_blocks_count;

        // SAFETY:  Assuming that the superblock was initially correct, the number of free blocks increased by 1
        unsafe { fs.set_free_blocks(current_free_blocks - 1) }?;

        Ok(())
    }
}

impl<Dev: Device<u8, Ext2Error>> From<Block<Dev>> for u32 {
    #[inline]
    fn from(block: Block<Dev>) -> Self {
        block.number
    }
}

impl<Dev: Device<u8, Ext2Error>> Read<Ext2Error> for Block<Dev> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error<Ext2Error>> {
        let fs = self.filesystem.borrow();
        let device = fs.device.borrow();

        let length = ((fs.superblock().block_size() - self.io_offset) as usize).min(buf.len());
        let starting_addr = Address::new((self.number * fs.superblock().block_size() + self.io_offset) as usize);
        let slice = device.slice(starting_addr..starting_addr + length)?;
        buf.clone_from_slice(slice.as_ref());

        // SAFETY: `length <= block_size << u32::MAX`
        self.io_offset += unsafe { u32::try_from(length).unwrap_unchecked() };

        Ok(length)
    }
}

impl<Dev: Device<u8, Ext2Error>> Write<Ext2Error> for Block<Dev> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error<Ext2Error>> {
        let fs = self.filesystem.borrow();
        let mut device = fs.device.borrow_mut();

        let length = ((fs.superblock().block_size() - self.io_offset) as usize).min(buf.len());
        let starting_addr = Address::new((self.number * fs.superblock().block_size() + self.io_offset) as usize);
        let mut slice = device.slice(starting_addr..starting_addr + length)?;
        slice.clone_from_slice(buf);
        let commit = slice.commit();
        device.commit(commit)?;

        // SAFETY: `length <= block_size < u32::MAX`
        self.io_offset += unsafe { u32::try_from(length).unwrap_unchecked() };

        Ok(length)
    }

    #[inline]
    fn flush(&mut self) -> Result<(), Error<Ext2Error>> {
        Ok(())
    }
}

impl<Dev: Device<u8, Ext2Error>> Seek<Ext2Error> for Block<Dev> {
    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Error<Ext2Error>> {
        let fs = self.filesystem.borrow();

        let block_size = i64::from(fs.superblock().block_size());
        let previous_offset = self.io_offset;
        match pos {
            SeekFrom::Start(offset) => {
                self.io_offset = u32::try_from(offset).map_err(|_err| Ext2Error::OutOfBounds(offset.into()))?;
            },
            SeekFrom::End(back_offset) => {
                self.io_offset = TryInto::<u32>::try_into(block_size - back_offset)
                    .map_err(|_err| Ext2Error::OutOfBounds(i128::from(block_size - back_offset)))?;
            },
            SeekFrom::Current(add_offset) => {
                self.io_offset = (i64::from(previous_offset) + add_offset)
                    .try_into()
                    .map_err(|_err| Ext2Error::OutOfBounds(i128::from(i64::from(previous_offset) + add_offset)))?;
            },
        };

        if self.io_offset >= fs.superblock().block_size() {
            Err(Error::Fs(FsError::Implementation(Ext2Error::OutOfBounds(self.io_offset.into()))))
        } else {
            Ok(previous_offset.into())
        }
    }
}

#[cfg(test)]
mod test {
    use alloc::vec;
    use core::cell::RefCell;
    use std::fs::{self, File};

    use crate::dev::celled::Celled;
    use crate::dev::sector::Address;
    use crate::dev::Device;
    use crate::fs::ext2::block::Block;
    use crate::fs::ext2::error::Ext2Error;
    use crate::fs::ext2::superblock::Superblock;
    use crate::fs::ext2::Ext2;
    use crate::io::{Read, Seek, SeekFrom, Write};

    #[test]
    fn block_read() {
        const BLOCK_NUMBER: u32 = 2;

        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/io_operations.ext2").unwrap());
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();

        let block_starting_addr = Address::new((BLOCK_NUMBER * superblock.block_size()).try_into().unwrap());
        let slice = <RefCell<File> as Device<u8, Ext2Error>>::slice(
            &celled_file.borrow(),
            block_starting_addr + 123..block_starting_addr + 123 + 59,
        )
        .unwrap()
        .commit();

        let ext2 = Celled::new(Ext2::new_celled(celled_file, 0).unwrap());
        let mut block = Block::new(ext2, BLOCK_NUMBER);
        block.seek(SeekFrom::Start(123)).unwrap();
        let mut buffer_auto = [0_u8; 59];
        block.read(&mut buffer_auto).unwrap();

        assert_eq!(buffer_auto, slice.as_ref());
    }

    #[test]
    fn block_write() {
        const BLOCK_NUMBER: u32 = 10_234;

        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_copy_block_write.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_block_write.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let fs = ext2.borrow();

        let mut block = Block::new(ext2.clone(), BLOCK_NUMBER);
        let mut buffer = vec![0_u8; usize::try_from(fs.superblock().block_size()).unwrap() - 123];
        buffer[..59].copy_from_slice(&[1_u8; 59]);
        block.seek(SeekFrom::Start(123)).unwrap();
        block.write(&buffer).unwrap();

        let mut start = vec![0_u8; 123];
        start.append(&mut buffer);
        assert_eq!(block.read_all().unwrap(), start);

        fs::remove_file("./tests/fs/ext2/io_operations_copy_block_write.ext2").unwrap();
    }

    #[test]
    fn block_set_free() {
        // This block should not be free
        const BLOCK_NUMBER: u32 = 9;

        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_copy_block_set_free.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_block_set_free.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());

        let mut block = Block::new(ext2, BLOCK_NUMBER);

        assert!(block.is_used().unwrap());

        block.set_free().unwrap();

        assert!(block.is_free().unwrap());

        fs::remove_file("./tests/fs/ext2/io_operations_copy_block_set_free.ext2").unwrap();
    }

    #[test]
    fn block_set_used() {
        // This block should not be used
        const BLOCK_NUMBER: u32 = 1234;

        fs::copy("./tests/fs/ext2/io_operations.ext2", "./tests/fs/ext2/io_operations_copy_block_set_used.ext2").unwrap();

        let file = RefCell::new(
            File::options()
                .read(true)
                .write(true)
                .open("./tests/fs/ext2/io_operations_copy_block_set_used.ext2")
                .unwrap(),
        );
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());

        let mut block = Block::new(ext2, BLOCK_NUMBER);

        assert!(block.is_free().unwrap());

        block.set_used().unwrap();

        assert!(block.is_used().unwrap());

        fs::remove_file("./tests/fs/ext2/io_operations_copy_block_set_used.ext2").unwrap();
    }
}
