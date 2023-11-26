//! Interface with ext2's inodes.
//!
//! See the [OSdev wiki](https://wiki.osdev.org/Ext2#Inodes) and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html#inode-table) for more informations.

use bitflags::bitflags;

use super::block_group::BlockGroupDescriptor;
use super::error::Ext2Error;
use super::superblock::Superblock;
use crate::dev::sector::{Address, Sector};
use crate::dev::Device;
use crate::error::Error;
use crate::fs::error::FsError;

/// Reserved bad block inode number.
pub const BAD_BLOCKS_INODE: u32 = 1;

/// Reserved root directory inode number.
pub const ROOT_DIRECTORY_INODE: u32 = 2;

/// Reserved ACL index inode number.
pub const ACL_INDEX_INODE: u32 = 3;

/// Reserved ACL index inode number.
pub const ACL_DATA_INODE: u32 = 4;

/// Reserved boot loader inode number.
pub const BOOT_LOADER_INODE: u32 = 5;

/// Reserved undeleted directory inode number.
pub const UNDELETED_DIRECTORY_INODE: u32 = 6;

/// Inode.
///
/// **Inode addresses start at 1.**
#[repr(packed)]
#[derive(Debug, Clone, Copy)]
pub struct Inode {
    /// Type and Permissions.
    pub mode: u16,

    /// User ID.
    pub uid: u16,

    /// Lower 32 bits of size in bytes.
    pub size: u32,

    /// Last Access Time (in POSIX time).
    pub atime: u32,

    /// Creation Time (in POSIX time).
    pub ctime: u32,

    /// Last Modification time (in POSIX time).
    pub mtime: u32,

    /// Deletion time (in POSIX time).
    pub dtime: u32,

    /// Group ID.
    pub gid: u16,

    /// Count of hard links (directory entries) to this inode. When this reaches 0, the data blocks are marked as unallocated.
    pub links_count: u16,

    /// Count of disk sectors (not Ext2 blocks) in use by this inode, not counting the actual inode structure nor directory entries
    /// linking to the inode.
    pub blocks: u32,

    /// Flags.
    pub flags: u32,

    /// Operating System Specific value #1.
    pub osd1: u32,

    /// Direct Block Pointer 0.
    pub dbp00: u32,

    /// Direct Block Pointer 1.
    pub dbp01: u32,

    /// Direct Block Pointer 2.
    pub dbp02: u32,

    /// Direct Block Pointer 3.
    pub dbp03: u32,

    /// Direct Block Pointer 4.
    pub dbp04: u32,

    /// Direct Block Pointer 5.
    pub dbp05: u32,

    /// Direct Block Pointer 6.
    pub dbp06: u32,

    /// Direct Block Pointer 7.
    pub dbp07: u32,

    /// Direct Block Pointer 8.
    pub dbp08: u32,

    /// Direct Block Pointer 9.
    pub dbp09: u32,

    /// Direct Block Pointer 10.
    pub dbp10: u32,

    /// Direct Block Pointer 11.
    pub dbp11: u32,

    /// Singly Indirect Block Pointer (Points to a block that is a list of block pointers to data).
    pub singly_indirect_block_pointer: u32,

    /// Doubly Indirect Block Pointer (Points to a block that is a list of block pointers to Singly Indirect Blocks).
    pub doubly_indirect_block_pointer: u32,

    /// Triply Indirect Block Pointer (Points to a block that is a list of block pointers to Doubly Indirect Blocks).
    pub triply_indirect_block_pointer: u32,

    /// Generation number (Primarily used for NFS).
    pub generation: u32,

    /// In Ext2 version 0, this field is reserved. In version >= 1, Extended attribute block (File ACL).
    pub file_acl: u32,

    /// In Ext2 version 0, this field is reserved. In version >= 1, Upper 32 bits of file size (if feature bit set) if it's a file,
    /// Directory ACL if it's a directory
    pub dir_acl: u32,

    /// Block address of fragment
    pub faddr: u32,

    /// Operating System Specific value #2
    pub osd2: [u8; 12],
}

bitflags! {
    /// Indicators of the inode type and permissions
    ///
    /// The type indicator occupies the top hex digit (bits 15 to 12).
    ///
    /// The permission indicator occupies the bottom 12 bits.
    #[derive(Debug)]
    pub struct TypePermissions: u16 {
        // Types

        /// FIFO
        const FIFO              =   0x1000;

        /// Character device
        const CHARACTER_DEVICE  =   0x2000;

        /// Directory
        const DIRECTORY         =   0x4000;

        /// Block device
        const BLOCK_DEVICE      =   0x6000;

        /// Regular file
        const REGULAR_FILE      =   0x8000;

        /// Symbolic link
        const SYMBOLIC_LINK     =   0xA000;

        /// Unix socket
        const SOCKET            =   0xC000;



        // Permissions

        /// Other - execute permission
        const OTHER_X           =   0x0001;

        /// Other - write permission
        const OTHER_W           =   0x0002;

        /// Other - read permission
        const OTHER_R           =   0x0004;

        /// Group - execute permission
        const GROUP_X           =   0x0008;

        /// Group - write permission
        const GROUP_W           =   0x0010;

        /// Group - read permission
        const GROUP_R           =   0x0020;

        /// User - execute permission
        const USER_X            =   0x0040;

        /// User - write permission
        const USER_W            =   0x0080;

        /// User - read permission
        const USER_R            =   0x0100;

        /// Sticky bit
        const STICKY            =   0x0200;

        /// Set group ID
        const SET_GROUP_ID      =   0x0400;

        /// Set user ID
        const SET_USER_ID       =   0x0800;
    }
}

bitflags! {
    /// Inode Flags
    #[derive(Debug)]
    pub struct Flags: u32 {
        /// Secure deletion (not used)
        const SECURE_DELETION                       =   0x0000_0001;

        /// Keep a copy of data when deleted (not used)
        const DELETION_KEEP_DATA_COPY               =   0x0000_0002;

        /// File compression (not used)
        const FILE_COMPRESSION                      =   0x0000_0004;

        /// Synchronous updates—new data is written immediately to disk
        const SYNCHRONOUS_UPDATES                   =   0x0000_0008;

        /// Immutable file (content cannot be changed)
        const IMMUTABLE_FILE                        =   0x0000_0010;

        /// Append only
        const APPEND_ONLY                           =   0x0000_0020;

        /// File is not included in `dump` command
        const DUMP_EXCLUDED                         =   0x0000_0040;

        /// Last accessed time should not updated
        const LAST_ACCESSED_TIME_UPDATE_DISABLE     =   0x0000_0080;

        /// Hash indexed directory
        const HASHED_INDEXED_DIR                    =   0x0001_0000;

        /// AFS directory
        const AFS_DIR                               =   0x0002_0000;

        /// Journal file data
        const JOURNAL_FILE_DATA                     =   0x0004_0000;

        /// Reserved for ext2 library
        const RESERVED                              =   0x8000_0000;
    }
}

impl Inode {
    /// Returns the block group of the `n`th inode.
    ///
    /// See the [OSdev wiki](https://wiki.osdev.org/Ext2#Determining_which_Block_Group_contains_an_Inode) for more informations.
    #[inline]
    #[must_use]
    pub const fn block_group(superblock: &Superblock, n: u32) -> u32 {
        (n - 1) / superblock.base().inodes_per_group
    }

    /// Returns the index of the `n`th inode in its block group.
    ///
    /// See the [OSdev wiki](https://wiki.osdev.org/Ext2#Finding_an_inode_inside_of_a_Block_Group) for more informations.
    #[inline]
    #[must_use]
    pub const fn group_index(superblock: &Superblock, n: u32) -> u32 {
        (n - 1) % superblock.base().inodes_per_group
    }

    /// Returns the index of the block containing the `n`th inode.
    ///
    /// See the [OSdev wiki](https://wiki.osdev.org/Ext2#Finding_an_inode_inside_of_a_Block_Group) for more informations.
    #[inline]
    #[must_use]
    pub const fn containing_block(superblock: &Superblock, n: u32) -> u32 {
        n * superblock.inode_size() as u32 / superblock.block_size()
    }

    /// Returns the complete size of the data pointed by this inode.
    #[inline]
    #[must_use]
    pub const fn data_size(&self) -> u64 {
        self.size as u64 & ((self.dir_acl as u64) << 32_u64)
    }

    /// Parses the `n`th inode from the given device (starting at **1**).
    ///
    /// # Errors
    ///
    /// Returns an [`NonExistingBlockGroup`](Ext2Error::NonExistingBlockGroup) if `n` is greater than the block group count of this
    /// device.
    ///
    /// Returns an [`Error`] if the device could not be read.
    #[inline]
    pub fn parse<S: Sector, D: Device<u8, S, Ext2Error>>(
        device: &D,
        superblock: &Superblock,
        n: u32,
    ) -> Result<Self, Error<Ext2Error>> {
        let base = superblock.base();
        if base.inodes_count < n || n == 0 {
            return Err(Error::Fs(FsError::Implementation(Ext2Error::NonExistingInode(n))));
        };

        let block_group = Self::block_group(superblock, n);
        let block_group_descriptor = BlockGroupDescriptor::parse(device, superblock, block_group)?;
        let inode_table_starting_block = block_group_descriptor.inode_table;
        let index = Self::group_index(superblock, n);

        // SAFETY: it is assumed that `u16::MAX <= usize::MAX`
        let starting_addr = unsafe {
            Address::<S>::try_from(
                inode_table_starting_block * superblock.block_size() + index * u32::from(superblock.inode_size()),
            )
            .unwrap_unchecked()
        };
        // SAFETY: all the possible failures are catched in the resulting error
        unsafe { device.read_at::<Self>(starting_addr) }
    }
}

#[cfg(test)]
mod test {
    use core::cell::RefCell;
    use core::mem::size_of;
    use std::fs::File;

    use crate::dev::sector::Size4096;
    use crate::fs::ext2::inode::{Inode, ROOT_DIRECTORY_INODE};
    use crate::fs::ext2::superblock::Superblock;

    #[test]
    fn struct_size() {
        assert_eq!(size_of::<Inode>(), 128);
    }

    #[test]
    fn parse_root() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let superblock = Superblock::parse::<Size4096, _>(&file).unwrap();
        assert!(Inode::parse::<Size4096, _>(&file, &superblock, ROOT_DIRECTORY_INODE).is_ok());

        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let superblock = Superblock::parse::<Size4096, _>(&file).unwrap();
        assert!(Inode::parse::<Size4096, _>(&file, &superblock, ROOT_DIRECTORY_INODE).is_ok());
    }
}
