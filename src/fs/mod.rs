//! General interface for filesystems

use alloc::borrow::ToOwned;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;
use core::str::FromStr;

use itertools::{Itertools, Position};

use crate::error::Error;
use crate::file::{Directory, SymbolicLink, TypeWithFile};
use crate::fs::error::FsError;
use crate::path::{Component, Path};

pub mod error;

#[cfg(feature = "ext2")]
pub mod ext2;

/// Maximal length for a path.
///
/// This is defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap04.html#tag_04_13).
///
/// This value is the same as the one defined in [the linux's `limits.h` header](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/tree/include/uapi/linux/limits.h?h=v6.5.8#n13).
pub const PATH_MAX: usize = 4_096;

/// A filesystem.
pub trait FileSystem<Dir: Directory> {
    /// Returns the root directory of the filesystem.
    ///
    /// # Errors
    ///
    /// Returns a [`DevError`](crate::dev::error::DevError) if the device could not be read.
    fn root(&self) -> Result<Dir, Error<Dir::Error>>;

    /// Returns the double slash root directory of the filesystem.
    ///
    /// If you do not have any idea of what this is, you are probably looking for [`root`](trait.FileSystem.html#tymethod.root).
    ///
    /// See [`DoubleSlashRootDir`](Component::DoubleSlashRootDir) and [`Path`] for more information.
    ///
    /// # Errors
    ///
    /// Returns a [`DevError`](crate::dev::error::DevError) if the device could not be read.
    fn double_slash_root(&self) -> Result<Dir, Error<Dir::Error>>;

    /// Performs a pathname resolution as described in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap04.html#tag_04_13).
    ///
    /// Returns the file of this filesystem corresponding to the given `path`, starting at the `current_dir`.
    ///
    /// `symlink_resolution` indicates whether the function calling this method is required to act on the symbolic link itself, or
    /// certain arguments direct that the function act on the symbolic link itself.
    ///
    /// # Errors
    ///
    /// Returns an [`NotFound`](FsError::NotFound) error if the given path does not leed to an existing path.
    ///
    /// Returns an [`NotDir`](FsError::NotDir) error if one of the components of the file is not a directory.
    ///
    /// Returns an [`Loop`](FsError::Loop) error if a loop is found during the symbolic link resolution.
    ///
    /// Returns an [`NameTooLong`](FsError::NameTooLong) error if the complete path contains more than [`PATH_MAX`] characters.
    ///
    /// Returns an [`NoEnt`](FsError::NoEnt) error if an encountered symlink points to a non-existing file.
    #[inline]
    fn get_file(&self, path: &Path, current_dir: Dir, symlink_resolution: bool) -> Result<TypeWithFile<Dir>, Error<Dir::Error>>
    where
        Self: Sized,
    {
        /// Auxiliary function used to store the visited symlinks during the pathname resolution to detect loops caused bt symbolic
        /// links.
        #[inline]
        fn path_resolution<E: core::error::Error, D: Directory<Error = E>>(
            fs: &impl FileSystem<D>,
            path: &Path,
            mut current_dir: D,
            symlink_resolution: bool,
            mut visited_symlinks: Vec<String>,
        ) -> Result<TypeWithFile<D>, Error<E>> {
            let canonical_path = path.canonical();

            if canonical_path.len() > PATH_MAX {
                return Err(Error::Fs(FsError::NameTooLong(canonical_path.to_string())));
            }

            let trailing_blackslash = canonical_path.as_unix_str().has_trailing_backslash();
            let mut symlink_encountered = None;

            let mut components = canonical_path.components();

            for (pos, comp) in components.with_position() {
                match comp {
                    Component::RootDir => {
                        if pos == Position::First || pos == Position::Only {
                            current_dir = fs.root()?;
                        } else {
                            unreachable!("The root directory cannot be encountered during the pathname resolution");
                        }
                    },
                    Component::DoubleSlashRootDir => {
                        if pos == Position::First || pos == Position::Only {
                            current_dir = fs.double_slash_root()?;
                        } else {
                            unreachable!("The double slash root directory cannot be encountered during the pathname resolution");
                        }
                    },
                    Component::CurDir => {},
                    Component::ParentDir => {
                        current_dir = current_dir.parent()?;
                    },
                    Component::Normal(filename) => {
                        let children = current_dir.entries()?;
                        let Some(entry) = children.into_iter().find(|entry| entry.filename == filename).map(|entry| entry.file)
                        else {
                            return Err(Error::Fs(FsError::NotFound(filename.to_string())));
                        };

                        #[allow(clippy::wildcard_enum_match_arm)]
                        match entry {
                            TypeWithFile::Directory(dir) => {
                                current_dir = dir;
                            },

                            // This case is the symbolic link resolution, which is the one described as **not** being the one
                            // explained in the following paragraph from the POSIX definition of the
                            // pathname resolution:
                            //
                            // If a symbolic link is encountered during pathname resolution, the behavior shall depend on whether
                            // the pathname component is at the end of the pathname and on the function
                            // being performed. If all of the following are true, then pathname
                            // resolution is complete:
                            //   1. This is the last pathname component of the pathname.
                            //   2. The pathname has no trailing <slash>.
                            //   3. The function is required to act on the symbolic link itself, or certain arguments direct that
                            //      the function act on the symbolic link itself.
                            TypeWithFile::SymbolicLink(symlink)
                                if (pos != Position::Last && pos != Position::Only)
                                    || !trailing_blackslash
                                    || !symlink_resolution =>
                            {
                                let pointed_file = symlink.get_pointed_file()?.to_owned();
                                if pointed_file.is_empty() {
                                    return Err(Error::Fs(FsError::NoEnt(filename.to_string())));
                                };

                                symlink_encountered = Some(pointed_file);
                                break;
                            },
                            _ => {
                                return if (pos == Position::Last || pos == Position::Only) && !trailing_blackslash {
                                    Ok(entry)
                                } else {
                                    Err(Error::Fs(FsError::NotDir(filename.to_string())))
                                };
                            },
                        }
                    },
                }
            }

            match symlink_encountered {
                None => Ok(TypeWithFile::Directory(current_dir)),
                Some(pointed_file) => {
                    if visited_symlinks.contains(&pointed_file) {
                        return Err(Error::Fs(FsError::Loop(pointed_file)));
                    }
                    visited_symlinks.push(pointed_file.clone());

                    let pointed_path = Path::from_str(&pointed_file).map_err(Error::Path)?;

                    let complete_path = match TryInto::<Path>::try_into(&components) {
                        Ok(remaining_path) => pointed_path.join(&remaining_path),
                        Err(_) => pointed_path,
                    };

                    if complete_path.len() >= PATH_MAX {
                        Err(Error::Fs(FsError::NameTooLong(complete_path.to_string())))
                    } else {
                        path_resolution(fs, &complete_path, current_dir, symlink_resolution, visited_symlinks)
                    }
                },
            }
        }

        path_resolution(self, path, current_dir, symlink_resolution, vec![])
    }
}
