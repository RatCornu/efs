//! Interface with ext2's block group descriptors and block group descriptor table.
//!
//! See the [OSdev wiki](https://wiki.osdev.org/Ext2#Block_Group_Descriptor_Table) and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html) for more informations.

use super::error::Ext2Error;
use super::superblock::Superblock;
use crate::dev::sector::Address;
use crate::dev::Device;
use crate::error::Error;
use crate::fs::error::FsError;
use crate::fs::ext2::superblock::{SUPERBLOCK_SIZE, SUPERBLOCK_START_BYTE};

/// Size in bytes of a block group descriptor with reserved bytes.
pub const BLOCK_GROUP_DESCRIPTOR_SIZE: usize = 32;

/// Block group descriptor.
///
/// Contains information regarding where important data structures for that block group are located.
#[repr(packed)]
#[derive(Debug, Clone, Copy)]
#[allow(clippy::module_name_repetitions)]
pub struct BlockGroupDescriptor {
    /// Block address of block usage bitmap.
    pub block_bitmap: u32,

    /// Block address of inode usage bitmap.
    pub inode_bitmap: u32,

    /// Starting block address of inode table.
    pub inode_table: u32,

    /// Number of unallocated blocks in groupµ.
    pub free_blocks_count: u16,

    /// Number of unallocated inodes in group.
    pub free_inodes_count: u16,

    /// Number of directories in group.
    pub used_dirs_count: u16,

    /// Used for padding the structure on a 32bit boundary.
    #[doc(hidden)]
    pub pad: u16,

    /// Reserved space for future revisions.
    #[doc(hidden)]
    pub reserved: [u8; 12],
}

impl BlockGroupDescriptor {
    /// Returns the starting address of the `n`th block group descriptor (starting at 0).
    ///
    /// # Errors
    ///
    /// Returns an [`NonExistingBlockGroup`](Ext2Error::NonExistingBlockGroup) if `n` is greater than the block group count of this
    /// device.
    #[inline]
    pub const fn starting_addr(superblock: &Superblock, n: u32) -> Result<Address, Error<Ext2Error>> {
        let block_group_count = superblock.block_group_count();
        if block_group_count <= n {
            return Err(Error::Fs(FsError::Implementation(Ext2Error::NonExistingBlockGroup(n))));
        };

        let superblock_end_address = SUPERBLOCK_START_BYTE + SUPERBLOCK_SIZE;
        Ok(Address::new(
            superblock_end_address + if superblock_end_address % (superblock.block_size() as usize) == 0 { 0 } else { 1 },
        ))
    }

    /// Parse the `n`th block group descriptor from the given device (starting at 0).
    ///
    /// # Errors
    ///
    /// Returns an [`NonExistingBlockGroup`](Ext2Error::NonExistingBlockGroup) if `n` is greater than the block group count of this
    /// device.
    ///
    /// Returns an [`Error`] if the device could not be read.
    #[inline]
    pub fn parse<D: Device<u8, Ext2Error>>(device: &D, superblock: &Superblock, n: u32) -> Result<Self, Error<Ext2Error>> {
        let table_start_address = Self::starting_addr(superblock, n)?;

        let block_group_descriptor_address = table_start_address + (n as usize * BLOCK_GROUP_DESCRIPTOR_SIZE);
        // SAFETY: all the possible failures are catched in the resulting error
        unsafe { device.read_at::<Self>(block_group_descriptor_address) }
    }
}

#[cfg(test)]
mod test {
    use core::cell::RefCell;
    use core::mem::size_of;
    use std::fs::File;

    use crate::fs::ext2::block_group::{BlockGroupDescriptor, BLOCK_GROUP_DESCRIPTOR_SIZE};
    use crate::fs::ext2::superblock::Superblock;

    #[test]
    fn struct_size() {
        assert_eq!(size_of::<BlockGroupDescriptor>(), BLOCK_GROUP_DESCRIPTOR_SIZE);
    }

    #[test]
    fn parse_first_block_group_descriptor() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let superblock = Superblock::parse(&file).unwrap();
        assert!(BlockGroupDescriptor::parse(&file, &superblock, 0).is_ok());

        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let superblock = Superblock::parse(&file).unwrap();
        assert!(BlockGroupDescriptor::parse(&file, &superblock, 0).is_ok());
    }

    #[test]
    fn failed_parse() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let superblock = Superblock::parse(&file).unwrap();
        assert!(BlockGroupDescriptor::parse(&file, &superblock, superblock.block_group_count()).is_err());

        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let superblock = Superblock::parse(&file).unwrap();
        assert!(BlockGroupDescriptor::parse(&file, &superblock, superblock.block_group_count()).is_err());
    }
}
