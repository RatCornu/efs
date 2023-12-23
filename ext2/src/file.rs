//! Interface to manipulate UNIX files on an ext2 filesystem.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Debug;

use base::dev::sector::Address;
use base::dev::Device;
use base::error::Error;
use base::file::{self, DirectoryEntry, Stat};
use base::fs::error::FsError;
use base::fs::PATH_MAX;
use base::types::{Blkcnt, Blksize, Dev, Gid, Ino, Mode, Nlink, Off, Time, Timespec, Uid};
use no_std_io::io::{Read, Seek, SeekFrom, Write};

use super::directory::Entry;
use super::error::Ext2Error;
use super::inode::Inode;
use super::{Celled, Ext2};

/// General file implementation.
pub struct File<D: Device<u8, Ext2Error>> {
    /// Ext2 object associated with the device containing this file.
    filesystem: Celled<Ext2<D>>,

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

impl<D: Device<u8, Ext2Error>> File<D> {
    /// Returns a new ext2's [`File`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Inode::parse`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<D>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        let fs = filesystem.borrow();
        let inode = Inode::parse(&fs.device, &fs.superblock, inode_number)?;
        Ok(Self {
            filesystem: filesystem.clone(),
            inode_number,
            inode,
        })
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
#[derive(Debug)]
pub struct Regular<D: Device<u8, Ext2Error>> {
    /// Inner file containing the regular file.
    file: File<D>,

    /// Read/Write offset (can be manipulated with [`Seek`]).
    offset: u64,
}

impl<D: Device<u8, Ext2Error>> Regular<D> {
    /// Returns a new ext2's [`Regular`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Ext2::inode`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<D>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        Ok(Self {
            file: File::new(&filesystem.clone(), inode_number)?,
            offset: 0,
        })
    }
}

impl<D: Device<u8, Ext2Error>> file::File for Regular<D> {
    #[inline]
    fn stat(&self) -> Stat {
        self.file.stat()
    }
}

impl<D: Device<u8, Ext2Error>> Read for Regular<D> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> no_std_io::io::Result<usize> {
        let filesystem = self.file.filesystem.borrow();
        self.file
            .inode
            .read_data(&filesystem.device, &filesystem.superblock, buf, self.offset)
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

impl<D: Device<u8, Ext2Error>> Write for Regular<D> {
    #[inline]
    fn write(&mut self, _buf: &[u8]) -> no_std_io::io::Result<usize> {
        todo!()
    }

    #[inline]
    fn flush(&mut self) -> no_std_io::io::Result<()> {
        todo!()
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

impl<D: Device<u8, Ext2Error>> file::Regular for Regular<D> {}

/// Interface for ext2's directories.
#[derive(Debug)]
pub struct Directory<D: Device<u8, Ext2Error>> {
    /// Inner file containing the regular file.
    file: File<D>,

    /// Entries contained in this directory.
    entries: Vec<Entry>,
}

impl<D: Device<u8, Ext2Error>> Directory<D> {
    /// Returns the directory located at the given inode number.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Entry::parse`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<D>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        let file = File::new(filesystem, inode_number)?;
        let fs = filesystem.borrow();

        let mut entries = Vec::new();

        let mut accumulated_size = 0_u32;
        while accumulated_size < fs.superblock.block_size() {
            let starting_addr =
                Address::from((file.inode.direct_block_pointers[0] * fs.superblock.block_size() + accumulated_size) as usize);
            // SAFETY: `starting_addr` contains the beginning of an entry
            let entry = unsafe { Entry::parse(&fs.device, starting_addr) }?;
            accumulated_size += u32::from(entry.rec_len);
            entries.push(entry);
        }

        Ok(Self { file, entries })
    }
}

impl<D: Device<u8, Ext2Error>> file::File for Directory<D> {
    #[inline]
    fn stat(&self) -> Stat {
        self.file.stat()
    }
}

impl<D: Device<u8, Ext2Error>> file::Directory<Regular<D>, SymbolicLink<D>, File<D>> for Directory<D> {
    #[inline]
    fn entries(&self) -> Vec<file::DirectoryEntry<Regular<D>, SymbolicLink<D>, File<D>, Self>> {
        let mut entries = Vec::new();

        for entry in &self.entries {
            entries.push(DirectoryEntry {
                // SAFETY: it is checked at the entry creation that the name is a valid CString
                filename: unsafe { entry.name.clone().try_into().unwrap_unchecked() },
                file: self.file.filesystem.file(entry.inode).expect("Error while reading a directory"),
            });
        }

        entries
    }
}

/// Interface for ext2's symbolic links.
#[derive(Debug)]
pub struct SymbolicLink<D: Device<u8, Ext2Error>> {
    /// Inner file containing the symbolic link.
    file: File<D>,

    /// Read/Write offset (can be manipulated with [`Seek`]).
    pointed_file: String,
}

impl<D: Device<u8, Ext2Error>> SymbolicLink<D> {
    /// Returns a new ext2's [`Regular`] from an [`Ext2`] instance and the inode number of the file.
    ///
    /// # Errors
    ///
    /// Returns a [`BadString`](Ext2Error::BadString) if the content of the given inode does not look like a valid path.
    ///
    /// Otherwise, returns the same errors as [`Ext2::inode`].
    #[inline]
    pub fn new(filesystem: &Celled<Ext2<D>>, inode_number: u32) -> Result<Self, Error<Ext2Error>> {
        let fs = filesystem.borrow();
        let file = File::new(&filesystem.clone(), inode_number)?;
        let mut buffer = [0_u8; PATH_MAX];
        let _: usize = file.inode.read_data(&fs.device, fs.superblock(), &mut buffer, 0)?;
        let pointed_file = buffer.split(|char| *char == b'\0').next().ok_or(Ext2Error::BadString)?.to_vec();
        Ok(Self {
            file,
            pointed_file: String::from_utf8(pointed_file).map_err(|_err| Ext2Error::BadString)?,
        })
    }
}

impl<D: Device<u8, Ext2Error>> file::File for SymbolicLink<D> {
    #[inline]
    fn stat(&self) -> Stat {
        self.file.stat()
    }
}

impl<D: Device<u8, Ext2Error>> file::SymbolicLink for SymbolicLink<D> {
    #[inline]
    fn pointed_file(&self) -> &str {
        &self.pointed_file
    }
}

#[cfg(test)]
mod test {
    use core::cell::RefCell;
    use std::fs::File;

    use base::dev::sector::Address;
    use itertools::Itertools;

    use crate::directory::Entry;
    use crate::file::Directory;
    use crate::inode::{Inode, ROOT_DIRECTORY_INODE};
    use crate::superblock::Superblock;
    use crate::{Celled, Ext2};

    #[test]
    fn parse_root() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests//extended.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let root = Directory::new(&ext2, ROOT_DIRECTORY_INODE).unwrap();
        assert_eq!(
            root.entries
                .into_iter()
                .map(|entry| entry.name.to_string_lossy().to_string())
                .collect::<Vec<String>>(),
            vec![".", "..", "lost+found", "big_file"]
        );
    }

    #[test]
    fn parse_root_entries() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests//extended.ext2").unwrap());
        let celled_file = Celled::new(file);
        let superblock = Superblock::parse(&celled_file).unwrap();
        let root_inode = Inode::parse(&celled_file, &superblock, ROOT_DIRECTORY_INODE).unwrap();

        let dot = unsafe {
            Entry::parse(&celled_file, Address::new((root_inode.direct_block_pointers[0] * superblock.block_size()) as usize))
        }
        .unwrap();
        let two_dots = unsafe {
            Entry::parse(
                &celled_file,
                Address::new((root_inode.direct_block_pointers[0] * superblock.block_size()) as usize + dot.rec_len as usize),
            )
        }
        .unwrap();
        let lost_and_found = unsafe {
            Entry::parse(
                &celled_file,
                Address::new(
                    (root_inode.direct_block_pointers[0] * superblock.block_size()) as usize
                        + (dot.rec_len + two_dots.rec_len) as usize,
                ),
            )
        }
        .unwrap();
        let big_file = unsafe {
            Entry::parse(
                &celled_file,
                Address::new(
                    (root_inode.direct_block_pointers[0] * superblock.block_size()) as usize
                        + (dot.rec_len + two_dots.rec_len + lost_and_found.rec_len) as usize,
                ),
            )
        }
        .unwrap();

        assert_eq!(dot.name.as_c_str().to_string_lossy(), ".");
        assert_eq!(two_dots.name.as_c_str().to_string_lossy(), "..");
        assert_eq!(lost_and_found.name.as_c_str().to_string_lossy(), "lost+found");
        assert_eq!(big_file.name.as_c_str().to_string_lossy(), "big_file");
    }

    #[test]
    fn parse_big_file_inode_data() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests//extended.ext2").unwrap());
        let ext2 = Celled::new(Ext2::new(file, 0).unwrap());
        let root = Directory::new(&ext2, ROOT_DIRECTORY_INODE).unwrap();

        let fs = ext2.borrow();
        let big_file_inode_number = root
            .entries
            .iter()
            .find(|entry| entry.name.to_string_lossy() == "big_file")
            .unwrap()
            .inode;
        let big_file_inode = fs.inode(big_file_inode_number).unwrap();

        let singly_indirect_block_pointer = big_file_inode.singly_indirect_block_pointer;
        let doubly_indirect_block_pointer = big_file_inode.doubly_indirect_block_pointer;
        assert_ne!(singly_indirect_block_pointer, 0);
        assert_ne!(doubly_indirect_block_pointer, 0);

        assert_ne!(big_file_inode.data_size(), 0);

        for offset in 0_usize..1_024_usize {
            let mut buffer = [0_u8; 1_024];
            big_file_inode
                .read_data(&fs.device, fs.superblock(), &mut buffer, (offset * 1_024) as u64)
                .unwrap();

            assert_eq!(buffer.iter().all_equal_value(), Ok(&1));
        }

        let mut buffer = [0_u8; 1_024];
        big_file_inode.read_data(&fs.device, fs.superblock(), &mut buffer, 0x0010_0000).unwrap();
        assert_eq!(buffer.iter().all_equal_value(), Ok(&0));
    }
}
