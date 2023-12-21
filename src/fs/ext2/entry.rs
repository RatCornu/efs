//! Interface with ext2's directories.
//!
//! See the [OSdev wiki](https://wiki.osdev.org/Ext2#Directories) and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html#directory) for more informations.

use alloc::boxed::Box;
use alloc::ffi::CString;
use alloc::vec::Vec;
use core::fmt::Debug;
use core::mem::size_of;

use super::error::Ext2Error;
use super::inode::Inode;
use super::superblock::Superblock;
use super::Celled;
use crate::dev::sector::Address;
use crate::dev::Device;
use crate::error::Error;
use crate::fs::error::FsError;

/// Subset of the [`Entry`] structure to make easier its read on the device.
#[repr(packed)]
#[derive(Debug, Clone, Copy)]

struct Subfields {
    /// Inode index.
    inode: u32,

    /// Total size of this entry (including all subfields).
    rec_len: u16,

    /// Name Length least-significant 8 bits.
    name_len: u8,

    /// Type indicator (only if the feature bit for "directory entries have file type byte" is set, else this is the
    /// most-significant 8 bits of the Name Length).
    file_type: u8,
}

/// A directory entry
#[derive(Debug, Clone)]
pub struct Entry {
    /// Inode index.
    pub inode: u32,

    /// Total size of this entry (including all subfields).
    pub rec_len: u16,

    /// Name Length least-significant 8 bits.
    pub name_len: u8,

    /// Type indicator (only if the feature bit for "directory entries have file type byte" is set, else this is the
    /// most-significant 8 bits of the Name Length).
    pub file_type: u8,

    /// Name of the directory entry.
    pub name: CString,
}

impl Entry {
    /// Returns the directory entry starting at the given address.
    ///
    /// # Errors
    ///
    /// Returns an [`Ext2Error::BadString`] if the name of the entry is not a valid `<NUL>` terminated string (a C-string).
    ///
    /// Returns an [`Error`] if the device could not be read.
    ///
    /// # Safety
    ///
    /// Must ensure that a directory entry is located at `starting_addr`.
    ///
    /// Must also ensure the requirements of [`Device::read_at`].
    #[inline]
    pub unsafe fn parse<Dev: Device<u8, Ext2Error>>(
        celled_device: Celled<'_, D>,
        starting_addr: Address,
    ) -> Result<Self, Error<Ext2Error>> {
        let device = celled_device.borrow();

        let subfields = device.read_at::<Subfields>(starting_addr)?;
        let buffer = device.read_at::<[u8; 256]>(starting_addr + size_of::<Subfields>())?;
        let name = CString::from_vec_with_nul(buffer.get_unchecked(..=subfields.name_len as usize).to_vec())
            .map_err(|_err| Error::Fs(FsError::Implementation(Ext2Error::BadString)))?;
        Ok(Self {
            inode: subfields.inode,
            rec_len: subfields.rec_len,
            name_len: subfields.name_len,
            file_type: subfields.file_type,
            name,
        })
    }
}

/// Interface for ext2's directories.
#[derive(Debug)]
pub struct Directory {
    /// Entries contained in this directory.
    entries: Vec<Entry>,

    /// Parent directory.
    ///
    /// For the root directory, this field is [`None`], otherwise it is [`Some`].
    parent: Option<Box<Self>>,
}

impl Directory {
    /// Returns the directory located at the given inode number.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Entry::parse`].
    #[inline]
    pub fn parse<Dev: Device<u8, Ext2Error>>(
        celled_device: Celled<'_, D>,
        inode: Inode,
        superblock: &Superblock,
        parent: Option<Self>,
    ) -> Result<Self, Error<Ext2Error>> {
        let mut entries = Vec::new();

        let mut accumulated_size = 0_u32;
        while accumulated_size < superblock.block_size() {
            let starting_addr =
                Address::from((inode.direct_block_pointers[0] * superblock.block_size() + accumulated_size) as usize);
            // SAFETY: `starting_addr` contains the beginning of an entry
            let entry = unsafe { Entry::parse(celled_device, starting_addr) }?;
            accumulated_size += u32::from(entry.rec_len);
            entries.push(entry);
        }

        Ok(Self {
            entries,
            parent: parent.map(Box::new),
        })
    }
}

#[cfg(test)]
mod test {
    use alloc::rc::Rc;
    use core::cell::RefCell;
    use core::mem::size_of;
    use std::fs::File;

    use itertools::Itertools;

    use super::Directory;
    use crate::dev::sector::Address;
    use crate::fs::ext2::directory::{Entry, Subfields};
    use crate::fs::ext2::inode::{Inode, ROOT_DIRECTORY_INODE};
    use crate::fs::ext2::superblock::Superblock;

    #[test]
    fn struct_size() {
        assert_eq!(size_of::<Subfields>(), 8);
        assert!(size_of::<Entry>() > size_of::<Subfields>());
    }

    #[test]
    fn parse_root() {
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let celled_file = Rc::new(RefCell::new(file));
        let superblock = Superblock::parse(&celled_file).unwrap();
        let root_inode = Inode::parse(&celled_file, &superblock, ROOT_DIRECTORY_INODE).unwrap();
        let root = Directory::parse(&celled_file, root_inode, &superblock, None).unwrap();
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
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let celled_file = Rc::new(RefCell::new(file));
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
        let file = RefCell::new(File::options().read(true).write(true).open("./tests/fs/ext2/extended.ext2").unwrap());
        let celled_file = Rc::new(RefCell::new(file));
        let superblock = Superblock::parse(&celled_file).unwrap();
        let root_inode = Inode::parse(&celled_file, &superblock, ROOT_DIRECTORY_INODE).unwrap();
        let root = Directory::parse(&celled_file, root_inode, &superblock, None).unwrap();
        let big_file_inode = Inode::parse(
            &celled_file,
            &superblock,
            root.entries
                .iter()
                .find(|entry| entry.name.to_string_lossy() == "big_file")
                .unwrap()
                .inode,
        )
        .unwrap();

        let singly_indirect_block_pointer = big_file_inode.singly_indirect_block_pointer;
        let doubly_indirect_block_pointer = big_file_inode.doubly_indirect_block_pointer;
        assert_ne!(singly_indirect_block_pointer, 0);
        assert_ne!(doubly_indirect_block_pointer, 0);

        assert_ne!(big_file_inode.data_size(), 0);

        for offset in 0_usize..1_024_usize {
            let mut buffer = [0_u8; 1_024];
            big_file_inode
                .read_data(&celled_file, &superblock, &mut buffer, (offset * 1_024) as u64)
                .unwrap();

            assert_eq!(buffer.iter().all_equal_value(), Ok(&1));
        }

        let mut buffer = [0_u8; 1_024];
        big_file_inode.read_data(&celled_file, &superblock, &mut buffer, 0x0010_0000).unwrap();
        assert_eq!(buffer.iter().all_equal_value(), Ok(&0));
    }
}
