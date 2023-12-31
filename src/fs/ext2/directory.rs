//! Interface with ext2's directories.
//!
//! See the [OSdev wiki](https://wiki.osdev.org/Ext2#Directories) and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html#directory) for more information.

use alloc::ffi::CString;
use core::fmt::Debug;
use core::mem::size_of;

use super::error::Ext2Error;
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
        celled_device: &Celled<Dev>,
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

#[cfg(test)]
mod test {
    use core::mem::size_of;

    use crate::fs::ext2::directory::{Entry, Subfields};

    #[test]
    fn struct_size() {
        assert_eq!(size_of::<Subfields>(), 8);
        assert!(size_of::<Entry>() > size_of::<Subfields>());
    }
}
