//! General interface for filesystems

use alloc::boxed::Box;

use crate::file::{Directory, File};
use crate::path::Path;

/// A filesystem
pub trait FileSystem {
    /// Returns the root directory of the filesystem.
    fn root(&self) -> Box<dyn Directory>;

    /// Performs a pathname resolution as described in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap04.html#tag_04_13).
    ///
    /// Returns the file of this filesystem corresponding to the given [`Path`]
    #[inline]
    #[must_use]
    fn pathname_resolution(&self, _path: &Path) -> Box<dyn File> {
        todo!()
    }
}
