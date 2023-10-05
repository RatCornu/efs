//! General interface for Unix files
//!
//! See [this Wikipedia page](https://en.wikipedia.org/wiki/Unix_file_types) for more informations.

use crate::types::{Blkcnt, Blksize, Dev, Gid, Ino, Mode, Nlink, Off, Timespec, Uid};

/// Enumeration of possible file types
#[derive(Debug, Clone, Copy)]
#[allow(unused)]
pub enum Type {
    /// Storage unit of a filesystem
    RegularFile,

    /// Node containing other nodes
    Directory,

    /// Node pointing towards an other node in the filesystem
    Symlink,

    /// Named pipe
    Fifo,

    /// An inode that refers to a device communicating by sending chars (bytes) of data
    CharacterDevice,

    /// An inode that refers to a device communicating by sending blocks of data
    BlockDevice,

    /// Communication flow between two processes
    UnixSocket,
}

/// Minimal stat structure
///
/// More informations on [the POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/sys_stat.h.html#tag_13_62)
pub struct Stat {
    /// Device ID of device containing file
    pub st_dev: Dev,

    /// File serial number
    pub st_ino: Ino,

    /// Mode of file
    pub st_mode: Mode,

    /// Number of hard links to the file
    pub st_nlink: Nlink,

    /// User ID of file
    pub st_uid: Uid,

    /// Group ID of file
    pub st_gid: Gid,

    /// Device ID (if file is character or block special)
    pub st_rdev: Dev,

    /// For regular files, the file size in bytes
    ///
    /// For symbolic links, the length in bytes of the pathname contained in the symbolic link.
    pub st_size: Off,

    /// Last data access timestamp
    pub st_atim: Timespec,

    /// Last data modification timestamp
    pub st_mtim: Timespec,

    /// Last file status change timestamp
    pub st_ctim: Timespec,

    /// A file system-specific preferred I/O block size for this object. In some file system types, this may vary from file to
    /// file.
    pub st_blksize: Blksize,

    /// Number of blocks allocated for this object
    pub st_blkcnt: Blkcnt,
}

/// Main trait for all Unix files
pub trait File: Into<Stat> {}
