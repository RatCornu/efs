//! Interface with ext2's inodes.
//!
//! See the [OSdev wiki](https://wiki.osdev.org/Ext2#Inodes) and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html#inode-table) for more information.

use alloc::vec::Vec;
use core::mem::size_of;
use core::slice::from_raw_parts;

use bitflags::bitflags;
use itertools::Itertools;

use super::block_group::BlockGroupDescriptor;
use super::error::Ext2Error;
use super::indirection::IndirectedBlocks;
use super::superblock::{OperatingSystem, Superblock};
use super::Celled;
use crate::dev::sector::Address;
use crate::dev::Device;
use crate::error::Error;
use crate::file::Type;
use crate::fs::error::FsError;

/// Number of direct block pointers in an inode.
pub const DIRECT_BLOCK_POINTER_COUNT: u32 = 12;

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

    /// Indicates the amount of blocks reserved for the associated file data. This includes both currently in used
    /// and currently reserved blocks in case the file grows in size.
    ///
    ///  Since this value represents 512-byte blocks and not file system blocks, this value should not be directly used as an index
    /// to the i_block array. Rather, the maximum index of the i_block array should be computed from `i_blocks /
    /// ((1024<<s_log_block_size)/512)`, or once simplified, `i_blocks/(2<<s_log_block_size)`.
    pub blocks: u32,

    /// Flags.
    pub flags: u32,

    /// Operating System Specific value #1.
    pub osd1: u32,

    /// Direct Block Pointers.
    pub direct_block_pointers: [u32; 12],

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

impl PartialEq for Inode {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        let self_direct_block_pointers = self.direct_block_pointers;
        let other_direct_block_pointers = other.direct_block_pointers;
        self.mode == other.mode
            && self.uid == other.uid
            && self.size == other.size
            && self.gid == other.gid
            && self.links_count == other.links_count
            && self.blocks == other.blocks
            && self.flags == other.flags
            && self.osd1 == other.osd1
            && self_direct_block_pointers == other_direct_block_pointers
            && self.singly_indirect_block_pointer == other.singly_indirect_block_pointer
            && self.doubly_indirect_block_pointer == other.doubly_indirect_block_pointer
            && self.triply_indirect_block_pointer == other.triply_indirect_block_pointer
            && self.generation == other.generation
            && self.file_acl == other.file_acl
            && self.dir_acl == other.dir_acl
            && self.faddr == other.faddr
            && self.osd2 == other.osd2
    }
}

impl Eq for Inode {}

bitflags! {
    /// Indicators of the inode type and permissions.
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

/// OS dependant structure corresponding to [`osd2`](struct.Inode.html#structfield.osd2) field in [`Inode`]
#[derive(Debug, Clone, Copy)]
pub enum Osd2 {
    /// Fields for Hurd systems.
    Hurd {
        /// Fragment number.
        ///
        /// Always 0 GNU HURD since fragments are not supported. Obsolete with Ext4.
        frag: u8,

        /// Fragment size
        ///
        /// Always 0 in GNU HURD since fragments are not supported. Obsolete with Ext4.
        fsize: u8,

        /// High 16bit of the 32bit mode.
        mode_high: u16,

        /// High 16bit of [user id](struct.Inode.html#structfield.uid).
        uid_high: u16,

        /// High 16bit of [group id](struct.Inode.html#structfield.gid).
        gid_high: u16,

        /// Assigned file author.
        ///
        /// If this value is set to -1, the POSIX [user id](struct.Inode.html#structfield.uid) will be used.
        author: u32,
    },

    /// Fields for Linux systems.
    Linux {
        /// Fragment number.
        ///
        /// Always 0 in Linux since fragments are not supported.
        frag: u8,

        /// Fragment size.
        ///
        /// Always 0 in Linux since fragments are not supported.
        fsize: u8,

        /// High 16bit of [user id](struct.Inode.html#structfield.uid).
        uid_high: u16,

        /// High 16bit of [group id](struct.Inode.html#structfield.gid).
        gid_high: u16,
    },

    /// Fields for Masix systems.
    Masix {
        /// Fragment number.
        ///
        /// Always 0 in Masix as framgents are not supported. Obsolete with Ext4.
        frag: u8,

        /// Fragment size.
        ///
        /// Always 0 in Masix as fragments are not supported. Obsolete with Ext4.
        fsize: u8,
    },

    /// Fields for other systems.
    Other([u8; 12]),
}

impl Osd2 {
    /// Get the [`Osd2`] fields from the bytes obtained in the [`Inode`] structure.
    #[inline]
    #[must_use]
    pub const fn from_bytes(bytes: [u8; 12], os: OperatingSystem) -> Self {
        match os {
            OperatingSystem::Linux => Self::Linux {
                frag: bytes[0],
                fsize: bytes[1],
                uid_high: ((bytes[4] as u16) << 8_usize) + bytes[5] as u16,
                gid_high: ((bytes[6] as u16) << 8_usize) + bytes[7] as u16,
            },
            OperatingSystem::GnuHurd => Self::Hurd {
                frag: bytes[0],
                fsize: bytes[1],
                mode_high: ((bytes[2] as u16) << 8_usize) + bytes[3] as u16,
                uid_high: ((bytes[4] as u16) << 8_usize) + bytes[5] as u16,
                gid_high: ((bytes[6] as u16) << 8_usize) + bytes[7] as u16,
                author: ((bytes[8] as u32) << 24_usize)
                    + ((bytes[9] as u32) << 16_usize)
                    + ((bytes[10] as u32) << 8_usize)
                    + bytes[11] as u32,
            },
            OperatingSystem::Masix => Self::Masix {
                frag: bytes[0],
                fsize: bytes[1],
            },
            OperatingSystem::FreeBSD | OperatingSystem::OtherLites | OperatingSystem::Other(_) => Self::Other(bytes),
        }
    }
}

impl Inode {
    /// Returns the block group of the `n`th inode.
    ///
    /// See the [OSdev wiki](https://wiki.osdev.org/Ext2#Determining_which_Block_Group_contains_an_Inode) for more information.
    #[inline]
    #[must_use]
    pub const fn block_group(superblock: &Superblock, n: u32) -> u32 {
        (n - 1) / superblock.base().inodes_per_group
    }

    /// Returns the index of the `n`th inode in its block group.
    ///
    /// See the [OSdev wiki](https://wiki.osdev.org/Ext2#Finding_an_inode_inside_of_a_Block_Group) for more information.
    #[inline]
    #[must_use]
    pub const fn group_index(superblock: &Superblock, n: u32) -> u32 {
        (n - 1) % superblock.base().inodes_per_group
    }

    /// Returns the index of the block containing the `n`th inode.
    ///
    /// See the [OSdev wiki](https://wiki.osdev.org/Ext2#Finding_an_inode_inside_of_a_Block_Group) for more information.
    #[inline]
    #[must_use]
    pub const fn containing_block(superblock: &Superblock, n: u32) -> u32 {
        n * superblock.inode_size() as u32 / superblock.block_size()
    }

    /// Returns the type and the permissions of this inode.
    #[inline]
    #[must_use]
    pub const fn type_permissions(&self) -> TypePermissions {
        TypePermissions::from_bits_truncate(self.mode)
    }

    /// Returns the type of the file pointed by this inode.
    ///
    /// # Errors
    ///
    /// Returns an [`BadFileType`](Ext2Error::BadFileType) if the inode does not contain a valid file type.
    #[inline]
    pub const fn file_type(&self) -> Result<Type, Ext2Error> {
        let types_permissions = self.type_permissions();
        if types_permissions.contains(TypePermissions::SYMBOLIC_LINK) {
            Ok(Type::SymbolicLink)
        } else if types_permissions.contains(TypePermissions::REGULAR_FILE) {
            Ok(Type::Regular)
        } else if types_permissions.contains(TypePermissions::DIRECTORY) {
            Ok(Type::Directory)
        } else if types_permissions.contains(TypePermissions::FIFO) {
            Ok(Type::Fifo)
        } else if types_permissions.contains(TypePermissions::CHARACTER_DEVICE) {
            Ok(Type::CharacterDevice)
        } else if types_permissions.contains(TypePermissions::BLOCK_DEVICE) {
            Ok(Type::BlockDevice)
        } else if types_permissions.contains(TypePermissions::SOCKET) {
            Ok(Type::Socket)
        } else {
            Err(Ext2Error::BadFileType(types_permissions.bits()))
        }
    }

    /// Returns the complete size of the data pointed by this inode.
    #[inline]
    #[must_use]
    pub const fn data_size(&self) -> u64 {
        // self.size as u64 + ((self.dir_acl as u64) << 32_u64)
        if TypePermissions::contains(&self.type_permissions(), TypePermissions::DIRECTORY) {
            self.size as u64
        } else {
            self.size as u64 + ((self.dir_acl as u64) << 32_u64)
        }
    }

    /// Returns the starting address of the `n`th inode.
    ///
    /// # Errors
    ///
    /// Returns an [`NonExistingBlockGroup`](Ext2Error::NonExistingBlockGroup) if `n` is greater than the block group count of this
    /// device.
    ///
    /// Otherwise, returns an [`Error`] if the device cannot be read.
    #[inline]
    pub fn starting_addr<D: Device<u8, Ext2Error>>(
        celled_device: &Celled<D>,
        superblock: &Superblock,
        n: u32,
    ) -> Result<Address, Error<Ext2Error>> {
        let base = superblock.base();
        if base.inodes_count < n || n == 0 {
            return Err(Error::Fs(FsError::Implementation(Ext2Error::NonExistingInode(n))));
        };

        let block_group = Self::block_group(superblock, n);
        let block_group_descriptor = BlockGroupDescriptor::parse(celled_device, superblock, block_group)?;

        let inode_table_starting_block = block_group_descriptor.inode_table;
        let index = Self::group_index(superblock, n);

        // SAFETY: it is assumed that `u16::MAX <= usize::MAX`
        Ok(unsafe {
            Address::try_from(inode_table_starting_block * superblock.block_size() + index * u32::from(superblock.inode_size()))
                .unwrap_unchecked()
        })
    }

    /// Parses the `n`th inode from the given device (starting at **1**).
    ///
    /// # Errors
    ///
    /// Returns an [`NonExistingBlockGroup`](Ext2Error::NonExistingBlockGroup) if `n` is greater than the block group count of this
    /// device.
    ///
    /// Returns an [`BadFileType`](Ext2Error::BadFileType) if the inode with the given inode number does not contains a valid file
    /// type.
    ///
    /// Returns an [`Error`] if the device could not be read.
    #[inline]
    pub fn parse<D: Device<u8, Ext2Error>>(
        celled_device: &Celled<D>,
        superblock: &Superblock,
        n: u32,
    ) -> Result<Self, Error<Ext2Error>> {
        let starting_addr = Self::starting_addr(celled_device, superblock, n)?;
        let device = celled_device.borrow();

        // SAFETY: all the possible failures are catched in the resulting error
        let inode = unsafe { device.read_at::<Self>(starting_addr) }?;

        match inode.file_type() {
            Ok(_) => Ok(inode),
            Err(err) => Err(Error::Fs(FsError::Implementation(err))),
        }
    }

    /// Returns the [`Osd2`] structure given by the [`Inode`] and the [`Superblock`] structures.
    #[inline]
    #[must_use]
    pub const fn osd2(&self, superblock: &Superblock) -> Osd2 {
        let os = superblock.creator_operating_system();
        Osd2::from_bytes(self.osd2, os)
    }

    /// Returns the complete list of block numbers containing this inode's data (indirect blocks are not considered).
    ///
    /// # Errors
    ///
    /// Returns a [`Error`] if the device cannot be read.
    #[inline]
    pub fn data_blocks<D: Device<u8, Ext2Error>>(
        &self,
        celled_device: &Celled<D>,
        superblock: &Superblock,
    ) -> Result<IndirectedBlocks<DIRECT_BLOCK_POINTER_COUNT>, Error<Ext2Error>> {
        /// Returns the list of block addresses contained in the given indirect block.
        #[allow(clippy::cast_ptr_alignment)]
        fn read_indirect_block<D: Device<u8, Ext2Error>>(
            celled_device: &Celled<D>,
            superblock: &Superblock,
            block_number: u32,
        ) -> Result<Vec<u32>, Error<Ext2Error>> {
            let device = celled_device.borrow();

            let block_address = Address::from((block_number * superblock.block_size()) as usize);
            let slice = device.slice(block_address..block_address + superblock.block_size() as usize)?;
            let byte_array = slice.as_ref();
            let address_array =
                // SAFETY: casting n `u8` to `u32` with n a multiple of 4 (as the block size is a power of 2, generally above 512)
                unsafe { from_raw_parts::<u32>(byte_array.as_ptr().cast::<u32>(), byte_array.len() / size_of::<u32>()) };
            Ok(address_array.iter().filter(|&block_number| (*block_number != 0)).copied().collect_vec())
        }

        let direct_block_pointers = self
            .direct_block_pointers
            .into_iter()
            .filter(|block_number| *block_number != 0)
            .collect_vec();
        let singly_indirect_block_pointer = self.singly_indirect_block_pointer;
        let doubly_indirect_block_pointer = self.doubly_indirect_block_pointer;
        let triply_indirect_block_pointer = self.triply_indirect_block_pointer;

        let mut singly_indirect_blocks = Vec::new();
        let mut doubly_indirect_blocks = Vec::new();
        let mut triply_indirect_blocks = Vec::new();

        if singly_indirect_block_pointer == 0 {
            return Ok(IndirectedBlocks::new(
                superblock.block_size() / 4,
                direct_block_pointers,
                (singly_indirect_block_pointer, singly_indirect_blocks),
                (doubly_indirect_block_pointer, doubly_indirect_blocks),
                (triply_indirect_block_pointer, triply_indirect_blocks),
            ));
        }

        singly_indirect_blocks.append(&mut read_indirect_block(celled_device, superblock, singly_indirect_block_pointer)?);

        if doubly_indirect_block_pointer == 0 {
            return Ok(IndirectedBlocks::new(
                superblock.block_size() / 4,
                direct_block_pointers,
                (singly_indirect_block_pointer, singly_indirect_blocks),
                (doubly_indirect_block_pointer, doubly_indirect_blocks),
                (triply_indirect_block_pointer, triply_indirect_blocks),
            ));
        }

        let singly_indirect_block_pointers = read_indirect_block(celled_device, superblock, doubly_indirect_block_pointer)?;

        for block_pointer in singly_indirect_block_pointers {
            if block_pointer == 0 {
                return Ok(IndirectedBlocks::new(
                    superblock.block_size() / 4,
                    direct_block_pointers,
                    (singly_indirect_block_pointer, singly_indirect_blocks),
                    (doubly_indirect_block_pointer, doubly_indirect_blocks),
                    (triply_indirect_block_pointer, triply_indirect_blocks),
                ));
            }

            doubly_indirect_blocks.push((block_pointer, read_indirect_block(celled_device, superblock, block_pointer)?));
        }

        if triply_indirect_block_pointer == 0 {
            return Ok(IndirectedBlocks::new(
                superblock.block_size() / 4,
                direct_block_pointers,
                (singly_indirect_block_pointer, singly_indirect_blocks),
                (doubly_indirect_block_pointer, doubly_indirect_blocks),
                (triply_indirect_block_pointer, triply_indirect_blocks),
            ));
        }

        let doubly_indirect_block_pointers = read_indirect_block(celled_device, superblock, triply_indirect_block_pointer)?;

        for block_pointer_pointer in doubly_indirect_block_pointers {
            if block_pointer_pointer == 0 {
                return Ok(IndirectedBlocks::new(
                    superblock.block_size() / 4,
                    direct_block_pointers,
                    (singly_indirect_block_pointer, singly_indirect_blocks),
                    (doubly_indirect_block_pointer, doubly_indirect_blocks),
                    (triply_indirect_block_pointer, triply_indirect_blocks),
                ));
            }

            let mut dib = Vec::new();

            let singly_indirect_block_pointers = read_indirect_block(celled_device, superblock, block_pointer_pointer)?;

            for block_pointer in singly_indirect_block_pointers {
                if block_pointer == 0 {
                    return Ok(IndirectedBlocks::new(
                        superblock.block_size() / 4,
                        direct_block_pointers,
                        (singly_indirect_block_pointer, singly_indirect_blocks),
                        (doubly_indirect_block_pointer, doubly_indirect_blocks),
                        (triply_indirect_block_pointer, triply_indirect_blocks),
                    ));
                }

                dib.push((block_pointer, read_indirect_block(celled_device, superblock, block_pointer)?));
            }

            triply_indirect_blocks.push((block_pointer_pointer, dib));
        }

        Ok(IndirectedBlocks::new(
            superblock.block_size() / 4,
            direct_block_pointers,
            (singly_indirect_block_pointer, singly_indirect_blocks),
            (doubly_indirect_block_pointer, doubly_indirect_blocks),
            (triply_indirect_block_pointer, triply_indirect_blocks),
        ))
    }

    /// Reads the content of this inode starting at the given `offset`, returning it in the given `buffer`. Returns the number of
    /// bytes read.
    ///
    /// If the size of the buffer is greater than the inode data size, it will fill the start of the buffer and will leave the end
    /// untouch.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the device could not be read.
    #[inline]
    pub fn read_data<D: Device<u8, Ext2Error>>(
        &self,
        celled_device: &Celled<D>,
        superblock: &Superblock,
        buffer: &mut [u8],
        mut offset: u64,
    ) -> Result<usize, Error<Ext2Error>> {
        let data_blocks = self.data_blocks(celled_device, superblock)?;
        let blocks = data_blocks.flatten();

        let device = celled_device.borrow();
        let buffer_length = buffer.len();

        let mut read_bytes = 0_usize;
        for block_number in blocks {
            if read_bytes as u64 == self.data_size() || read_bytes == buffer_length {
                break;
            }

            if offset == 0 {
                let count = (superblock.block_size() as usize).min(buffer_length - read_bytes);
                let block_addr = Address::from((block_number * superblock.block_size()) as usize);
                let slice = device.slice(block_addr..block_addr + count)?;

                // SAFETY: buffer contains at least `block_size.min(remaining_bytes_count)` since `remaining_bytes_count <=
                // buffer_length`
                let block_buffer = unsafe { buffer.get_mut(read_bytes..read_bytes + count).unwrap_unchecked() };
                block_buffer.clone_from_slice(slice.as_ref());

                read_bytes += count;
            } else if offset >= u64::from(superblock.block_size()) {
                offset -= u64::from(superblock.block_size());
            } else {
                let data_count = (superblock.block_size() as usize).min(buffer_length - read_bytes);
                // SAFETY: `offset < superblock.block_size()` and `superblock.block_size()` is generally around few KB, which is
                // fine when `usize > u8`.
                let offset_usize = unsafe { usize::try_from(offset).unwrap_unchecked() };
                match data_count.checked_sub(offset_usize) {
                    None => read_bytes = buffer_length,
                    Some(count) => {
                        let block_addr = Address::from((block_number * superblock.block_size()) as usize);
                        let slice = device.slice(block_addr + offset_usize..block_addr + offset_usize + count)?;

                        // SAFETY: buffer contains at least `block_size.min(remaining_bytes_count)` since `remaining_bytes_count <=
                        // buffer_length`
                        let block_buffer = unsafe { buffer.get_mut(read_bytes..read_bytes + count).unwrap_unchecked() };
                        block_buffer.clone_from_slice(slice.as_ref());

                        read_bytes += count;
                    },
                }
                offset = 0;
            }
        }

        Ok(read_bytes)
    }
}

#[cfg(test)]
mod test {
    use core::cell::RefCell;
    use core::mem::size_of;
    use std::fs::File;

    use crate::dev::Device;
    use crate::fs::ext2::error::Ext2Error;
    use crate::fs::ext2::inode::{Inode, ROOT_DIRECTORY_INODE};
    use crate::fs::ext2::superblock::Superblock;
    use crate::fs::ext2::Celled;

    #[test]
    fn struct_size() {
        assert_eq!(size_of::<Inode>(), 128);
    }

    #[test]
    fn parse_root() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();
        assert!(Inode::parse(&celled_file, &superblock, ROOT_DIRECTORY_INODE).is_ok());

        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();
        assert!(Inode::parse(&celled_file, &superblock, ROOT_DIRECTORY_INODE).is_ok());
    }

    #[test]
    fn failed_parse() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();
        assert!(Inode::parse(&celled_file, &superblock, 0).is_err());

        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();
        assert!(Inode::parse(&celled_file, &superblock, superblock.base().inodes_count + 1).is_err());
    }

    #[test]
    fn starting_addr() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/base.ext2").unwrap());
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();

        let root_auto = Inode::parse(&celled_file, &superblock, ROOT_DIRECTORY_INODE).unwrap();

        let starting_addr = Inode::starting_addr(&celled_file, &superblock, ROOT_DIRECTORY_INODE).unwrap();

        let root_manual =
            unsafe { <RefCell<File> as Device<u8, Ext2Error>>::read_at::<Inode>(&celled_file.borrow(), starting_addr).unwrap() };

        assert_eq!(root_auto, root_manual);
    }
}
