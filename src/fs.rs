//! General interface for filesystems

use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;
use core::error;
use core::fmt::{self, Display};
use core::str::FromStr;

use itertools::{Itertools, Position};
use no_std_io::io;

use crate::error::Error;
use crate::file::{Directory, Type};
use crate::path::{Component, Path};

/// Maximal length for a path.
///
/// This is defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap04.html#tag_04_13).
///
/// This value is the same as the one defined in [the linux's `limits.h` header](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/tree/include/uapi/linux/limits.h?h=v6.5.8#n13).
pub const PATH_MAX: usize = 4_096;

/// Enumeration of possible errors encountered with [`FileSystem`]s' manipulation.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug)]
pub enum FsError {
    /// Indicates that the given [`Path`] is too long to be resolved
    NameTooLong(String),

    /// Indicates that the given filename is not a [`Directory`]
    NotDir(String),

    /// Indicates that the given filename is an symbolic link pointing at an empty string
    NoEnt(String),

    /// Indicates that a loop has been encountered during the given path resolution
    Loop(String),
}

impl Display for FsError {
    #[inline]
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Loop(path) => write!(formatter, "Loop: a loop has been encountered during the resolution of \"{path}\""),
            Self::NameTooLong(path) => write!(formatter, "Name too long: \"{path}\" is too long to be resolved"),
            Self::NotDir(filename) => write!(formatter, "Not a Directory: \"{filename}\" is not a directory"),
            Self::NoEnt(filename) => write!(formatter, "No entry: \"{filename}\" is an symbolic link pointing at an empty string"),
        }
    }
}

impl error::Error for FsError {}

/// A filesystem
pub trait FileSystem {
    /// Error type associated with the filesystem
    type Error: error::Error;

    /// Returns the root directory of the filesystem.
    fn root(&self) -> Box<dyn Directory>;

    /// Returns the double slash root directory of the filesystem.
    ///
    /// If you do not have any idea of what this is, you are probably looking for [`root`](trait.FileSystem.html#tymethod.root).
    ///
    /// See [`Component::DoubleSlashRootDir`] and [`Path`] for more informations.
    fn double_slash_root(&self) -> Box<dyn Directory>;

    /// Performs a pathname resolution as described in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap04.html#tag_04_13).
    ///
    /// Returns the file of this filesystem corresponding to the given `path`, starting at the `current_dir`.
    ///
    /// `symlink_resolution` indicates whether the function calling this method is required to act on the symbolic link itself, or
    /// certain arguments direct that the function act on the symbolic link itself.
    ///
    /// # Errors
    ///
    /// Returns an [`NotFound`](no_std_io::io::ErrorKind) error if the given path does not leed to an existing path.
    ///
    /// Returns an [`NotDir`](FsError::NotDir) error if one of the components of the file is not a directory.
    ///
    /// Returns an [`Loop`](FsError::Loop) error if a loop is found during the symbolic link resolution.
    ///
    /// Returns an [`NameTooLong`](FsError::NameTooLong) error if the complete path contains more than [`PATH_MAX`] characters.
    ///
    /// Returns an [`NoEnt`](FsError::NoEnt) error if an encountered symlink points to a non-existing file.
    #[inline]
    fn pathname_resolution(
        &self,
        path: &Path,
        current_dir: Box<dyn Directory>,
        symlink_resolution: bool,
    ) -> Result<Type, Error<Self::Error>>
    where
        Self: Sized,
    {
        /// Auxiliary function used to store the visited symlinks during the pathname resolution to detect loops caused bt symbolic
        /// links.
        #[inline]
        fn inner_resolution<E: error::Error>(
            fs: &impl FileSystem,
            path: &Path,
            mut current_dir: Box<dyn Directory>,
            symlink_resolution: bool,
            mut visited_symlinks: Vec<String>,
        ) -> Result<Type, Error<E>> {
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
                            current_dir = fs.root();
                        } else {
                            unreachable!("The root directory cannot be encountered during the pathname resolution");
                        }
                    },
                    Component::DoubleSlashRootDir => {
                        if pos == Position::First || pos == Position::Only {
                            current_dir = fs.double_slash_root();
                        } else {
                            unreachable!("The double slash root directory cannot be encountered during the pathname resolution");
                        }
                    },
                    Component::CurDir => {},
                    Component::ParentDir => {
                        current_dir = current_dir.parent();
                    },
                    Component::Normal(filename) => {
                        let children = current_dir.entries();
                        let Some(entry) = children.into_iter().find(|entry| entry.filename == filename).map(|entry| entry.file)
                        else {
                            return Err(Error::IO(io::Error::new(io::ErrorKind::NotFound, "File not found")));
                        };

                        #[allow(clippy::wildcard_enum_match_arm)]
                        match entry {
                            Type::Directory(dir) => {
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
                            //      the
                            //    function act on the symbolic link itself.
                            Type::SymbolicLink(symlink)
                                if (pos != Position::Last && pos != Position::Only)
                                    || !trailing_blackslash
                                    || !symlink_resolution =>
                            {
                                let pointed_file = symlink.pointed_file().to_owned();
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
                None => Ok(Type::Directory(current_dir)),
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
                        inner_resolution(fs, &complete_path, current_dir, symlink_resolution, visited_symlinks)
                    }
                },
            }
        }

        inner_resolution(self, path, current_dir, symlink_resolution, vec![])
    }
}
