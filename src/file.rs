//! General interface for Unix files
//!
//! See [this Wikipedia page](https://en.wikipedia.org/wiki/Unix_file_types) for more informations.

use crate::types::Dev;

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

/// Main trait for all Unix files
pub trait File {
    /// Device ID of device containing file
    fn st_dev(&self) -> Dev;
}
