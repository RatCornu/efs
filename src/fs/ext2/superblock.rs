//! Interface with the ext2's superblock.
//!
//! See the [OSdev wiki](https://wiki.osdev.org/Ext2#Superblock) for more informations.

use super::error::Ext2Error;

/// Ext2 signature, used to help confirm the presence of an Ext2 volume.
pub const EXT2_SIGNATURE: u16 = 0xef53;

/// Starting byte of the superblock in a Ext2 storage device.
pub const SUPERBLOCK_START_BYTE: usize = 1024;

/// Superblock of the Ext2 filesystem.
///
/// This implementation contains also the extended fields described [here](https://wiki.osdev.org/Ext2#Extended_Superblock_Fields).
#[repr(packed)]
#[derive(Debug)]
pub struct Superblock {
    /// Total number of inodes in file system
    pub total_inodes: u32,

    /// Total number of blocks in file system
    pub total_blocks: u32,

    /// Number of blocks reserved for superuser (see offset 80)
    pub number_blocks_superuser_reserved: u32,

    /// Total number of unallocated blocks
    pub total_unallocated_blocks: u32,

    /// Total number of unallocated inodes
    pub total_unallocated_inodes: u32,

    /// Block number of the block containing the superblock (also the starting block number, NOT always zero.)
    pub superblock_block_number: u32,

    /// log2 (block size) - 10. (In other words, the number to shift 1,024 to the left by to obtain the block size)
    pub shifted_block_size: u32,

    /// log2 (fragment size) - 10. (In other words, the number to shift 1,024 to the left by to obtain the fragment size)
    pub shifted_fragment_size: u32,

    /// Number of blocks in each block group
    pub blocks_per_group: u32,

    /// Number of fragments in each block group
    pub fragments_per_group: u32,

    /// Number of inodes in each block group
    pub inodes_per_group: u32,

    /// Last mount time (in POSIX time)
    pub last_mount_time: u32,

    /// Last written time (in POSIX time)
    pub last_written_time: u32,

    /// Number of times the volume has been mounted since its last consistency check (fsck)
    pub nb_volumes_mounted_since_fsck: u16,

    /// Number of mounts allowed before a consistency check (fsck) must be done
    pub nb_mounts_before_fsck: u16,

    /// Ext2 signature (0xef53), used to help confirm the presence of Ext2 on a volume
    pub ext2_signature: u16,

    /// File system state
    pub file_system_state: u16,

    /// What to do when an error is detected
    pub error_handling_method: u16,

    /// Minor portion of version (combine with Major portion below to construct full version field)
    pub version_minor: u16,

    /// POSIX time of last consistency check (fsck)
    pub time_last_fsck: u32,

    /// Interval (in POSIX time) between forced consistency checks (fsck)
    pub interval_forced_fsck: u32,

    /// Operating system ID from which the filesystem on this volume was created
    pub os_id: u32,

    /// Major portion of version (combine with Minor portion above to construct full version field)
    pub version_major: u32,

    /// User ID that can use reserved blocks
    pub reserved_blocks_user_id: u16,

    /// Group ID that can use reserved blocks
    pub reserved_blocks_group_id: u16,

    /// First non-reserved inode in file system. (In versions < 1.0, this is fixed as 11)
    pub first_non_reserved_inode: u32,

    /// Size of each inode structure in bytes. (In versions < 1.0, this is fixed as 128)
    pub inode_byte_size: u16,

    /// Block group that this superblock is part of (if backup copy)
    pub superblock_block_number_backup_copy: u16,

    /// Optional features present (features that are not required to read or write, but usually result in a performance increase)
    pub optional_features: u32,

    /// Required features present (features that are required to be supported to read or write)
    pub required_features: u32,

    /// Features that if not supported, the volume must be mounted read-only
    pub forced_read_only_features: u32,

    /// File system ID (what is output by blkid)
    pub file_system_id: u128,

    /// Volume name (C-style string: characters terminated by a 0 byte)
    pub volume_name: [u8; 16],

    /// Path volume was last mounted to (C-style string: characters terminated by a 0 byte)
    pub path_last_mount: [u8; 64],

    /// Compression algorithms used (see Required features above)
    pub compression_algorithms: u32,

    /// Number of blocks to preallocate for files
    pub preallocated_blocks_per_file: u8,

    /// Number of blocks to preallocate for directories
    pub preallocated_blocks_per_dir: u8,

    /// (Unused)
    pub _unused: u16,

    /// Journal ID (same style as the File system ID above)
    pub journal_id: u128,

    /// Journal inode
    pub journal_inode: u32,

    /// Journal device
    pub journal_device: u32,

    /// Head of orphan inode list
    pub head_orphan_node_list: u32,
}

impl Superblock {
    /// Returns the number of block groups.
    ///
    /// It is equal to the round up of the total number of blocks divided by the number of blocks per block group.
    #[inline]
    #[must_use]
    pub const fn total_block_groups(&self) -> usize {
        self.total_blocks.div_ceil(self.blocks_per_group) as usize
    }

    /// Returns the size of a block in the filesystem described by this superblock.
    #[inline]
    #[must_use]
    pub const fn block_size(&self) -> usize {
        1024 << self.shifted_block_size
    }
}

/// File System States.
///
/// See the [OSdev wiki](https://wiki.osdev.org/Ext2#File_System_States) for more informations.
#[repr(u16)]
#[derive(Debug)]
pub enum State {
    /// File system is clean.
    Clean = 0x0001,

    /// File system has errors.
    Errors = 0x0002,
}

impl TryFrom<u16> for State {
    type Error = Ext2Error;

    #[inline]
    fn try_from(value: u16) -> Result<Self, Self::Error> {
        match value {
            0x0001 => Ok(Self::Clean),
            0x0002 => Ok(Self::Errors),
            _ => Err(Ext2Error::InvlidState(value)),
        }
    }
}

impl From<State> for u16 {
    #[inline]
    fn from(value: State) -> Self {
        value as Self
    }
}

/// Error Handling Methods.
///
/// See the [OSdev wiki](https://wiki.osdev.org/Ext2#Error_Handling_Methods) for more informations.
#[repr(u16)]
#[derive(Debug)]
pub enum ErrorsHandling {
    /// Ignore the error (continue on).
    Ignore = 0x0001,

    /// Remount file system as read-only.
    Remount = 0x0002,

    /// Kernel panic.
    Panic = 0x03,
}

impl TryFrom<u16> for ErrorsHandling {
    type Error = Ext2Error;

    #[inline]
    fn try_from(value: u16) -> Result<Self, Self::Error> {
        match value {
            0x0001 => Ok(Self::Ignore),
            0x0002 => Ok(Self::Remount),
            0x0003 => Ok(Self::Panic),
            _ => Err(Ext2Error::InvalidErrorHandlingMethod(value)),
        }
    }
}

impl From<ErrorsHandling> for u16 {
    #[inline]
    fn from(value: ErrorsHandling) -> Self {
        value as Self
    }
}
