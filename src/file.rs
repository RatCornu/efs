//! General interface for Unix files
//!
//! See [this Wikipedia page](https://en.wikipedia.org/wiki/Unix_file_types) and [the POSIX header of `<sys/stat.h>`](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/sys_stat.h.html) for more information.

use alloc::boxed::Box;
use alloc::vec::Vec;

use no_std_io::io::{Read, Seek, Write};

use crate::path::{UnixStr, CUR_DIR, PARENT_DIR};
use crate::types::{Blkcnt, Blksize, Dev, Gid, Ino, Mode, Nlink, Off, Timespec, Uid};

/// Minimal stat structure.
///
/// More information on [the POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/sys_stat.h.html#tag_13_62).
#[derive(Debug, Clone)]
pub struct Stat {
    /// Device ID of device containing file.
    pub dev: Dev,

    /// File serial number.
    pub ino: Ino,

    /// Mode of file.
    pub mode: Mode,

    /// Number of hard links to the file.
    pub nlink: Nlink,

    /// User ID of file.
    pub uid: Uid,

    /// Group ID of file.
    pub gid: Gid,

    /// Device ID (if file is character or block special).
    pub rdev: Dev,

    /// For regular files, the file size in bytes.
    ///
    /// For symbolic links, the length in bytes of the pathname contained in the symbolic link.
    pub size: Off,

    /// Last data access timestamp.
    pub atim: Timespec,

    /// Last data modification timestamp.
    pub mtim: Timespec,

    /// Last file status change timestamp.
    pub ctim: Timespec,

    /// A file system-specific preferred I/O block size for this object. In some file system types, this may vary from file to
    /// file.
    pub blksize: Blksize,

    /// Number of blocks allocated for this object.
    pub blkcnt: Blkcnt,
}

/// Main trait for all Unix files.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_164).
pub trait File {
    /// Retrieves information about this file.
    fn stat(&self) -> Stat;
}

/// A file that is a randomly accessible sequence of bytes, with no further structure imposed by the system.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_323).
pub trait Regular: File + Read + Write + Seek {}

/// An object that associates a filename with a file. Several directory entries can associate names with the same file.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_130).
pub struct DirectoryEntry<'path> {
    /// Name of the file pointed by this directory entry
    ///
    /// See more information on valid filenames in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_170).
    pub filename: UnixStr<'path>,

    /// File pointed by this directory entry.
    pub file: Type,
}

/// A file that contains directory entries. No two directory entries in the same directory have the same name.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_129).
pub trait Directory: File {
    /// Returns the directory entries contained.
    ///
    /// No two [`DirectoryEntry`] returned can have the same `filename`.
    ///
    /// The result must contain at least the entries `.` (the current directory) and `..` (the parent directory).
    fn entries(&self) -> Vec<DirectoryEntry>;

    /// Returns the entry with the given name.
    #[inline]
    fn entry(&self, name: UnixStr) -> Option<Type> {
        let children = self.entries();
        children.into_iter().find(|entry| entry.filename == name).map(|entry| entry.file)
    }

    /// Returns the parent directory.
    ///
    /// If `self` if the root directory, it must return itself.
    #[inline]
    fn parent(&self) -> Box<dyn Directory> {
        let Some(Type::Directory(parent_entry)) = self.entry(PARENT_DIR.clone()) else {
            unreachable!("`entries` must return `..` that corresponds to the parent directory.")
        };
        parent_entry
    }
}

impl Clone for Box<dyn Directory> {
    #[inline]
    fn clone(&self) -> Self {
        let Some(Type::Directory(parent_entry)) = self.entry(CUR_DIR.clone()) else {
            unreachable!("`entries` must return `.` that corresponds to the current directory.")
        };
        parent_entry
    }
}

/// A type of file with the property that when the file is encountered during pathname resolution, a string stored by the file is
/// used to modify the pathname resolution.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_381)
pub trait SymbolicLink: File {
    /// Returns the string stored in this symbolic link
    fn pointed_file(&self) -> &str;
}

/// A type of file with the property that data written to such a file is read on a first-in-first-out basis.
///
/// Defined in [this POSIX defintion](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_163)
pub trait Fifo: File + Read + Write {}

/// A file that refers to a device (such as a terminal device file) or that has special properties (such as /dev/null).
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_91)
pub trait CharacterDevice: File + Read + Write {}

/// A file that refers to a device. A block special file is normally distinguished from a character special file by providing access
/// to the device in a manner such that the hardware characteristics of the device are not visible.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_79)
pub trait BlockDevice: File + Read + Write {}

/// A file of a particular type that is used as a communications endpoint for process-to-process communication as described in the
/// System Interfaces volume of POSIX.1-2017.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_356)
pub trait Socket: File + Read + Write {}

/// Enumeration of possible file types in a standard UNIX-like filesystem
pub enum Type {
    /// Storage unit of a filesystem
    Regular(Box<dyn Regular>),

    /// Node containing other nodes
    Directory(Box<dyn Directory>),

    /// Node pointing towards an other node in the filesystem
    SymbolicLink(Box<dyn SymbolicLink>),

    /// Named pipe
    Fifo(Box<dyn Fifo>),

    /// An inode that refers to a device communicating by sending chars (bytes) of data
    CharacterDevice(Box<dyn CharacterDevice>),

    /// An inode that refers to a device communicating by sending blocks of data
    BlockDevice(Box<dyn BlockDevice>),

    /// Communication flow between two processes
    Socket(Box<dyn Socket>),

    /// A file system dependant file (e.g [the Doors](https://en.wikipedia.org/wiki/Doors_(computing)) on Solaris systems)
    Other(Box<dyn File>),
}
