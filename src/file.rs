//! General interface for Unix files
//!
//! See [this Wikipedia page](https://en.wikipedia.org/wiki/Unix_file_types) and [the POSIX header of `<sys/stat.h>`](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/sys_stat.h.html) for more information.

use alloc::vec::Vec;

use crate::error::Error;
use crate::io::{Read, Seek, Write};
use crate::path::{UnixStr, PARENT_DIR};
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
pub struct DirectoryEntry<'path, Dir: Directory> {
    /// Name of the file pointed by this directory entry.
    ///
    /// See more information on valid filenames in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_170).
    pub filename: UnixStr<'path>,

    /// File pointed by this directory entry.
    pub file: TypeWithFile<Dir>,
}

/// A file that contains directory entries. No two directory entries in the same directory have the same name.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_129).
pub trait Directory: Sized + File {
    /// Error type associated with the directories of the [`FileSystem`](crate::fs::FileSystem) they belong to.
    type Error: core::error::Error;

    /// Type of the regular files in the [`FileSystem`](crate::fs::FileSystem) this directory belongs to.
    type Regular: Regular;

    /// Type of the symbolic links in the [`FileSystem`](crate::fs::FileSystem) this directory belongs to.
    type SymbolicLink: SymbolicLink;

    /// Type of the other files (if any) in the [`FileSystem`](crate::fs::FileSystem) this directory belongs to.
    type File: File;

    /// Returns the directory entries contained.
    ///
    /// No two [`DirectoryEntry`] returned can have the same `filename`.
    ///
    /// The result must contain at least the entries `.` (the current directory) and `..` (the parent directory).
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    #[allow(clippy::type_complexity)]
    fn entries(&self) -> Result<Vec<DirectoryEntry<Self>>, Error<Self::Error>>;

    /// Returns the entry with the given name.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    #[allow(clippy::type_complexity)]
    #[inline]
    fn entry(&self, name: UnixStr) -> Result<Option<TypeWithFile<Self>>, Error<Self::Error>> {
        let children = self.entries()?;
        Ok(children.into_iter().find(|entry| entry.filename == name).map(|entry| entry.file))
    }

    /// Returns the parent directory.
    ///
    /// If `self` if the root directory, it must return itself.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    #[inline]
    fn parent(&self) -> Result<Self, Error<Self::Error>> {
        let Some(TypeWithFile::Directory(parent_entry)) = self.entry(PARENT_DIR.clone())? else {
            unreachable!("`entries` must return `..` that corresponds to the parent directory.")
        };
        Ok(parent_entry)
    }
}

/// A type of file with the property that when the file is encountered during pathname resolution, a string stored by the file is
/// used to modify the pathname resolution.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_381).
pub trait SymbolicLink: File {
    /// Returns the string stored in this symbolic link
    fn pointed_file(&self) -> &str;
}

/// Enumeration of possible file types in a standard UNIX-like filesystem.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    /// Storage unit of a filesystem.
    Regular,

    /// Node containing other nodes.
    Directory,

    /// Node pointing towards an other node in the filesystem.
    SymbolicLink,

    /// Named pipe.
    Fifo,

    /// An inode that refers to a device communicating by sending chars (bytes) of data.
    CharacterDevice,

    /// An inode that refers to a device communicating by sending blocks of data.
    BlockDevice,

    /// Communication flow between two processes.
    Socket,

    /// A file system dependant file (e.g [the Doors](https://en.wikipedia.org/wiki/Doors_(computing)) on Solaris systems).
    Other,
}

/// Enumeration of possible file types in a standard UNIX-like filesystem with an attached file object.
///
/// # Note
///
/// This enum does not contain the [`Fifo`](Type::Fifo), [`CharacterDevice`](Type::CharacterDevice),
/// [`BlockDevice`](Type::BlockDevice) or [`Socket`](Type::Socket) as those are special files that have no real presence in the
/// filesystem: they are abstractions created by the kernel. Thus, only the [`Regular`](Type::Regular),
/// [`Directory`](Type::Directory) and the [`SymbolicLink`](Type::SymbolicLink) can be found (and the files not described in the
/// POSIX norm).
#[allow(clippy::module_name_repetitions)]
pub enum TypeWithFile<Dir: Directory> {
    /// Storage unit of a filesystem.
    Regular(Dir::Regular),

    /// Node containing other nodes.
    Directory(Dir),

    /// Node pointing towards an other node in the filesystem.
    SymbolicLink(Dir::SymbolicLink),

    /// A file system dependant file (e.g [the Doors](https://en.wikipedia.org/wiki/Doors_(computing)) on Solaris systems).
    Other(Dir::File),
}

impl<Dir: Directory> From<TypeWithFile<Dir>> for Type {
    #[inline]
    fn from(value: TypeWithFile<Dir>) -> Self {
        match value {
            TypeWithFile::Regular(_) => Self::Regular,
            TypeWithFile::Directory(_) => Self::Directory,
            TypeWithFile::SymbolicLink(_) => Self::SymbolicLink,
            TypeWithFile::Other(_) => Self::Other,
        }
    }
}
