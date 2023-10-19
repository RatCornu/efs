//! General interface for filesystems

use alloc::boxed::Box;

use no_std_io::io::Result;

use crate::file::{Directory, File};
use crate::path::Path;

/// A filesystem
pub trait FileSystem {
    /// Returns the root directory of the filesystem.
    fn root(&self) -> Box<dyn Directory>;

    /// Performs a pathname resolution as described in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap04.html#tag_04_13).
    ///
    /// Returns the file of this filesystem corresponding to the given [`Path`].
    ///
    /// # Errors
    ///
    /// Returns an [`NotFound`](no_std_io::io::ErrorKind) if the given path does not leed to an existing path.
    #[inline]
    fn pathname_resolution(&self, _path: &Path) -> Result<Box<dyn File>> {
        todo!()
    }
}
