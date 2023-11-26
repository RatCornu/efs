//! Implementation of the Second Extended Filesystem (ext2fs) filesystem.
//!
//! See [its Wikipedia page](https://fr.wikipedia.org/wiki/Ext2), [its OSDev page](https://wiki.osdev.org/Ext2), and the [*The Second Extended Filesystem* book](https://www.nongnu.org/ext2-doc/ext2.html) for more information.

pub mod block_group;
pub mod error;
pub mod inode;
pub mod superblock;
