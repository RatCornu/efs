//! Implementation of the Second Extended Filesystem (ext2fs) filesystem.
//!
//! See [its Wikipedia page](https://fr.wikipedia.org/wiki/Ext2), [its OSDev page](https://wiki.osdev.org/Ext2), and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html) for more information.

use core::cell::RefCell;

use self::error::Ext2Error;
use self::superblock::Superblock;
use crate::dev::Device;
use crate::error::Error;

pub mod block_group;
pub mod directory;
pub mod error;
pub mod file;
pub mod inode;
pub mod superblock;

/// Type alias for celled objects.
pub type Celled<'dev, T> = &'dev RefCell<T>;

/// Main interface for devices containing an ext2 filesystem.
pub struct Ext2<D: Device<u8, Ext2Error>> {
    /// Device number of the device containing the ext2 filesystem.
    device_id: u32,

    /// Device containing the ext2 filesystem.
    device: RefCell<D>,

    /// Superblock of the filesystem.
    superblock: Superblock,
}

impl<D: Device<u8, Ext2Error>> Ext2<D> {
    /// Creates a new [`Ext2`] object from the given device that should contain an ext2 filesystem and a given device ID.
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the device could not be read of if no ext2 filesystem is found on this device.
    #[inline]
    pub fn new(device: D, device_id: u32) -> Result<Self, Error<Ext2Error>> {
        let celled_device = RefCell::new(device);
        let superblock = Superblock::parse(&celled_device)?;
        Ok(Self {
            device: celled_device,
            device_id,
            superblock,
        })
    }
}
