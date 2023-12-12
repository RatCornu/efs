//! Interface to manipulate UNIX files on an ext2 filesystem.

use alloc::rc::Rc;
use core::cell::RefCell;
use core::fmt::Debug;

use no_std_io::io::{Read, Seek, SeekFrom};

use super::error::Ext2Error;
use super::inode::Inode;
use super::Ext2;
use crate::dev::Device;
use crate::error::Error;
use crate::file::{self, Stat};
use crate::fs::error::FsError;
use crate::types::{Blkcnt, Blksize, Dev, Gid, Ino, Mode, Nlink, Off, Time, Timespec, Uid};

/// General file implementation.
#[derive(Clone)]
pub struct File<D: Device<u8, Ext2Error>> {
    /// Ext2 object associated with the device containing this file.
    filesystem: Rc<RefCell<Ext2<D>>>,

    /// Inode number of the inode corresponding to the file.
    inode_number: u32,

    /// Inode corresponding to the file.
    inode: Inode,
}

impl<D: Device<u8, Ext2Error>> Debug for File<D> {
    #[inline]
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("File")
            .field("device_id", &self.filesystem.borrow().device_id)
            .field("inode_number", &self.inode_number)
            .field("inode", &self.inode)
            .finish()
    }
}

impl<D: Device<u8, Ext2Error>> file::File for File<D> {
    #[inline]
    fn stat(&self) -> file::Stat {
        let filesystem = self.filesystem.borrow();

        Stat {
            dev: Dev(filesystem.device_id),
            ino: Ino(self.inode_number),
            mode: Mode(self.inode.mode),
            nlink: Nlink(u32::from(self.inode.links_count)),
            uid: Uid(self.inode.uid),
            gid: Gid(self.inode.gid),
            rdev: Dev::default(),
            size: Off(self.inode.data_size().try_into().unwrap_or_default()),
            atim: Timespec {
                tv_sec: Time(self.inode.atime.try_into().unwrap_or_default()),
                tv_nsec: i32::default(),
            },
            mtim: Timespec {
                tv_sec: Time(self.inode.mtime.try_into().unwrap_or_default()),
                tv_nsec: i32::default(),
            },
            ctim: Timespec {
                tv_sec: Time(self.inode.ctime.try_into().unwrap_or_default()),
                tv_nsec: i32::default(),
            },
            blksize: Blksize(filesystem.superblock.block_size().try_into().unwrap_or_default()),
            blkcnt: Blkcnt(self.inode.blocks.try_into().unwrap_or_default()),
        }
    }
}

/// Implementation of a regular file.
#[derive(Debug, Clone)]
pub struct Regular<D: Device<u8, Ext2Error>> {
    /// Inner file containing the regular file.
    file: File<D>,

    /// Read/Write offset (can be manipulated with [`Seek`]).
    offset: u64,
}

impl<D: Device<u8, Ext2Error>> Read for Regular<D> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> no_std_io::io::Result<usize> {
        let filesystem = self.file.filesystem.borrow();
        let device = &filesystem.device;
        self.file
            .inode
            .read_data(device, &filesystem.superblock, buf, self.offset)
            .map_err(|err| match err {
                Error::Fs(FsError::Implementation(ext2_error)) => {
                    no_std_io::io::Error::new(no_std_io::io::ErrorKind::InvalidData, ext2_error.as_str())
                },
                Error::Device(dev_error) => {
                    no_std_io::io::Error::new(no_std_io::io::ErrorKind::AddrNotAvailable, dev_error.as_str())
                },
                Error::Fs(_) | Error::Path(_) => unreachable!(),
            })
    }
}

impl<D: Device<u8, Ext2Error>> Seek for Regular<D> {
    #[inline]
    fn seek(&mut self, pos: no_std_io::io::SeekFrom) -> no_std_io::io::Result<u64> {
        let filesystem = self.file.filesystem.borrow();
        let device = filesystem.device.borrow();
        // SAFETY: it is safe to assume that the device has a length lower than 2^64 bytes.
        let device_lenght = unsafe { TryInto::<i64>::try_into(device.size().len().index() as u64).unwrap_unchecked() };

        let previous_offset = self.offset;
        match pos {
            SeekFrom::Start(offset) => self.offset = offset,
            SeekFrom::End(back_offset) => {
                self.offset = TryInto::<u64>::try_into(device_lenght - back_offset)
                    .map_err(|_err| no_std_io::io::Error::new(no_std_io::io::ErrorKind::InvalidInput, "Out of Device's Bounds"))?;
            },
            SeekFrom::Current(add_offset) => {
                // SAFETY: it is safe to assume that the device has a length lower than 2^64 bytes.
                self.offset = (unsafe { TryInto::<i64>::try_into(previous_offset).unwrap_unchecked() } + add_offset)
                    .try_into()
                    .map_err(|_err| no_std_io::io::Error::new(no_std_io::io::ErrorKind::InvalidInput, "Out of Device's Bounds"))?;
            },
        };
        if self.offset >= device.size().len().index() as u64 {
            Err(no_std_io::io::Error::new(no_std_io::io::ErrorKind::InvalidInput, "Out of Device's Bounds"))
        } else {
            Ok(previous_offset)
        }
    }
}
