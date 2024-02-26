//! General interface for Unix files
//!
//! See [this Wikipedia page](https://en.wikipedia.org/wiki/Unix_file_types) and [the POSIX header of `<sys/stat.h>`](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/sys_stat.h.html) for more information.

use alloc::vec::Vec;

use itertools::Itertools;

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
    /// Error type associated with the directories of the [`FileSystem`](crate::fs::FileSystem) they belong to.
    type Error: core::error::Error;

    /// Retrieves information about this file.
    fn stat(&self) -> Stat;

    /// Retrieves the [`Type`] of this file.
    fn get_type(&self) -> Type;
}

/// A file that is a randomly accessible sequence of bytes, with no further structure imposed by the system.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_323).
pub trait Regular: File + Read + Write + Seek {
    /// Trunctates the file size to the given `size` (in bytes).
    ///
    /// If the given `size` is greater than the previous file size, this function does nothing.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    fn truncate(&mut self, size: u64) -> Result<(), Error<<Self as File>::Error>>;
}

/// A read-only file that is a randomly accessible sequence of bytes, with no further structure imposed by the system.
///
/// This is the read-only version of [`Regular`].
pub trait ReadOnlyRegular: File + Read + Seek {}

impl<R: Regular> ReadOnlyRegular for R {}

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

/// An read-only object that associates a filename with a file. Several directory entries can associate names with the same file.
///
/// This is the read-only version of [`DirectoryEntry`].
pub struct ReadOnlyDirectoryEntry<'path, RoDir: ReadOnlyDirectory> {
    /// Name of the file pointed by this directory entry.
    ///
    /// See more information on valid filenames in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_170).
    pub filename: UnixStr<'path>,

    /// File pointed by this directory entry.
    pub file: ReadOnlyTypeWithFile<RoDir>,
}

impl<'path, Dir: Directory> From<DirectoryEntry<'path, Dir>> for ReadOnlyDirectoryEntry<'path, Dir> {
    #[inline]
    fn from(value: DirectoryEntry<'path, Dir>) -> Self {
        Self {
            filename: value.filename,
            file: value.file.into(),
        }
    }
}

/// A file that contains directory entries. No two directory entries in the same directory have the same name.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_129).
pub trait Directory: Sized + File {
    /// Type of the regular files in the [`FileSystem`](crate::fs::FileSystem) this directory belongs to.
    type Regular: Regular<Error = Self::Error>;

    /// Type of the symbolic links in the [`FileSystem`](crate::fs::FileSystem) this directory belongs to.
    type SymbolicLink: SymbolicLink<Error = Self::Error>;

    /// Type of the other files (if any) in the [`FileSystem`](crate::fs::FileSystem) this directory belongs to.
    type File: File<Error = Self::Error>;

    /// Returns the directory entries contained.
    ///
    /// No two [`DirectoryEntry`] returned can have the same `filename`.
    ///
    /// The result must contain at least the entries `.` (the current directory) and `..` (the parent directory).
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    fn entries(&self) -> Result<Vec<DirectoryEntry<Self>>, Error<Self::Error>>;

    /// Adds a new empty entry to the directory, meaning that a new file will be created.
    ///
    /// # Errors
    ///
    /// Returns an [`EntryAlreadyExist`](crate::fs::error::FsError::EntryAlreadyExist) error if the entry already exist.
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be written.
    fn add_entry(&mut self, entry: DirectoryEntry<Self>) -> Result<(), Error<Self::Error>>;

    /// Removes an entry from the directory.
    ///
    /// # Errors
    ///
    /// Returns an [`NotFound`](crate::fs::error::FsError::NotFound) error if there is no entry with the given name in this
    /// directory.
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be written.
    fn remove_entry(&mut self, name: UnixStr) -> Result<(), Error<Self::Error>>;

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

/// A read-only file that contains directory entries. No two directory entries in the same directory have the same name.
///
/// This is the read-only version of [`Directory`].
pub trait ReadOnlyDirectory: Sized + File {
    /// Type of the regular files in the [`FileSystem`](crate::fs::FileSystem) this directory belongs to.
    type Regular: ReadOnlyRegular<Error = Self::Error>;

    /// Type of the symbolic links in the [`FileSystem`](crate::fs::FileSystem) this directory belongs to.
    type SymbolicLink: ReadOnlySymbolicLink<Error = Self::Error>;

    /// Type of the other files (if any) in the [`FileSystem`](crate::fs::FileSystem) this directory belongs to.
    type File: File<Error = Self::Error>;

    /// Returns the directory entries contained.
    ///
    /// No two [`DirectoryEntry`] returned can have the same `filename`.
    ///
    /// The result must contain at least the entries `.` (the current directory) and `..` (the parent directory).
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    fn entries(&self) -> Result<Vec<ReadOnlyDirectoryEntry<Self>>, Error<Self::Error>>;

    /// Returns the entry with the given name.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    #[allow(clippy::type_complexity)]
    #[inline]
    fn entry(&self, name: UnixStr) -> Result<Option<ReadOnlyTypeWithFile<Self>>, Error<Self::Error>> {
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
        let Some(ReadOnlyTypeWithFile::Directory(parent_entry)) = self.entry(PARENT_DIR.clone())? else {
            unreachable!("`entries` must return `..` that corresponds to the parent directory.")
        };
        Ok(parent_entry)
    }
}

impl<Dir: Directory> ReadOnlyDirectory for Dir {
    type File = Dir::File;
    type Regular = Dir::Regular;
    type SymbolicLink = Dir::SymbolicLink;

    #[inline]
    fn entries(&self) -> Result<Vec<ReadOnlyDirectoryEntry<Self>>, Error<Self::Error>> {
        <Self as Directory>::entries(self).map(|entries| entries.into_iter().map(Into::into).collect_vec())
    }
}

/// A type of file with the property that when the file is encountered during pathname resolution, a string stored by the file is
/// used to modify the pathname resolution.
///
/// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_381).
pub trait SymbolicLink: File {
    /// Returns the string stored in this symbolic link.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    fn get_pointed_file(&self) -> Result<&str, Error<Self::Error>>;

    /// Sets the pointed file in this symbolic link.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be written.
    fn set_pointed_file(&mut self, pointed_file: &str) -> Result<(), Error<Self::Error>>;
}

/// A read-only type of file with the property that when the file is encountered during pathname resolution, a string stored by the
/// file is used to modify the pathname resolution.
///
/// This is the read-only version of [`SymbolicLink`].
pub trait ReadOnlySymbolicLink: File {
    /// Returns the string stored in this symbolic link.
    ///
    /// # Errors
    ///
    /// Returns an [`DevError`](crate::dev::error::DevError) if the device on which the directory is located could not be read.
    fn get_pointed_file(&self) -> Result<&str, Error<Self::Error>>;
}

impl<Symlink: SymbolicLink> ReadOnlySymbolicLink for Symlink {
    #[inline]
    fn get_pointed_file(&self) -> Result<&str, Error<Self::Error>> {
        <Self as SymbolicLink>::get_pointed_file(self)
    }
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

/// Enumeration of possible file types in a standard UNIX-like filesystem with an attached file object.
///
/// This is the read-only version of [`TypeWithFile`].
#[allow(clippy::module_name_repetitions)]
pub enum ReadOnlyTypeWithFile<RoDir: ReadOnlyDirectory> {
    /// Storage unit of a filesystem.
    Regular(RoDir::Regular),

    /// Node containing other nodes.
    Directory(RoDir),

    /// Node pointing towards an other node in the filesystem.
    SymbolicLink(RoDir::SymbolicLink),

    /// A file system dependant file (e.g [the Doors](https://en.wikipedia.org/wiki/Doors_(computing)) on Solaris systems).
    Other(RoDir::File),
}

impl<Dir: Directory> From<TypeWithFile<Dir>> for ReadOnlyTypeWithFile<Dir> {
    #[inline]
    fn from(value: TypeWithFile<Dir>) -> Self {
        match value {
            TypeWithFile::Regular(file) => Self::Regular(file),
            TypeWithFile::Directory(file) => Self::Directory(file),
            TypeWithFile::SymbolicLink(file) => Self::SymbolicLink(file),
            TypeWithFile::Other(file) => Self::Other(file),
        }
    }
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
