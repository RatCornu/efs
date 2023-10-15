//! Path manipulation for UNIX-like filesystems

use alloc::borrow::ToOwned;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::str::FromStr;

use once_cell::sync::Lazy;
use regex::Regex;

/// A general structure to implement paths.
///
/// A [`UnixStr`] cannot be empty nor contain <NUL> character ('\0')! It is guaranteed at creation time.
#[derive(Debug, Clone)]
pub struct UnixStr(String);

impl UnixStr {
    /// Creates a new [`UnixStr`] from a string.
    ///
    /// # Examples
    ///
    /// ```
    /// use efs::path::UnixStr;
    ///
    /// let valid = UnixStr::new("/").unwrap();
    /// ```
    ///
    /// ```should_panic
    /// use efs::path::UnixStr;
    ///
    /// let not_valid = UnixStr::new("").unwrap();
    /// ```
    #[inline]
    #[must_use]
    pub fn new(str: &str) -> Option<Self> {
        let path = str.to_owned();
        if path.is_empty() || path.contains('\0') { None } else { Some(Self(path)) }
    }

    /// Checks whether the inner string contains exactly two leading '/' characters
    fn starts_with_two_slashes(&self) -> bool {
        self.0.starts_with("//") && !self.0.starts_with("///")
    }
}

impl FromStr for UnixStr {
    type Err = &'static str;

    #[inline]
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        Self::new(str).ok_or("Tried to make a UnixStr from an empty string")
    }
}

impl ToString for UnixStr {
    #[inline]
    fn to_string(&self) -> String {
        self.0.clone()
    }
}

/// A slice of a path
///
/// It is represented by a string that is used to identify a file. It has optional beginning `/`, followed by zero or more filenames
/// separated by `/`. A pathname can optionally contain one or more trailing `/`. Multiple successive `/` characters are considered
/// to be the same as one `/`, except for the case of exactly two leading `/`.
///
/// See [the POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_271) for more informations.
#[derive(Debug, Clone)]
#[cfg_attr(not(doc), repr(transparent))]
pub struct Path {
    /// Inner representation of a bath by a [`UnixStr`].
    name: UnixStr,
}

impl Path {
    /// Directly wraps a [`UnixStr`] slice as a [`Path`] slice.
    #[inline]
    #[must_use]
    pub fn new<US: Into<UnixStr>>(str: US) -> Self {
        Self { name: str.into() }
    }

    /// Checks if the path is absolute.
    ///
    /// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_02).
    ///
    /// Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::Path;
    ///
    /// assert!(Path::from_str("/home").unwrap().is_absolute());
    /// assert!(!Path::from_str("./foo/bar").unwrap().is_absolute());
    /// assert!(!Path::from_str("//home").unwrap().is_absolute());
    /// ```
    #[inline]
    #[must_use]
    pub fn is_absolute(&self) -> bool {
        self.name.0.starts_with('/') && !self.name.starts_with_two_slashes()
    }

    /// Checks if the path is absolute.
    ///
    /// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_324).
    ///
    /// # Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::Path;
    ///
    /// assert!(Path::from_str("./foo/bar").unwrap().is_relative());
    /// assert!(!Path::from_str("/home").unwrap().is_relative());
    /// assert!(!Path::from_str("//home").unwrap().is_relative());
    /// ```
    #[inline]
    #[must_use]
    pub fn is_relative(&self) -> bool {
        !self.name.0.starts_with('/')
    }

    /// Returns the canonical path associated with `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::Path;
    ///
    /// assert_eq!(
    ///     Path::from_str("/home/user/foo").unwrap(),
    ///     Path::from_str("/home//user///foo").unwrap().canonical()
    /// );
    ///
    /// assert_eq!(
    ///     Path::from_str("//bin/foo").unwrap(),
    ///     Path::from_str("//bin///foo").unwrap().canonical()
    /// );
    ///
    /// assert_eq!(
    ///     Path::from_str("./foo/bar").unwrap(),
    ///     Path::from_str("foo/bar").unwrap().canonical()
    /// );
    /// assert_eq!(
    ///     Path::from_str("./foo/bar/").unwrap(),
    ///     Path::from_str("foo///bar//").unwrap().canonical()
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn canonical(&self) -> Self {
        /// Regex matching one slash or more.
        static SLASHES: Lazy<Regex> = Lazy::new(|| Regex::new("/+").unwrap_or_else(|_| unreachable!()));

        let almost_canonical = SLASHES.replace_all(self.name.0.as_str(), "/").to_string();
        if self.name.starts_with_two_slashes() {
            let mut canon = "/".to_owned();
            canon.push_str(&almost_canonical);
            Self {
                name: UnixStr(canon),
            }
        } else if almost_canonical.starts_with('/') {
            Self {
                name: UnixStr(almost_canonical),
            }
        } else {
            let mut canon = "./".to_owned();
            canon.push_str(&almost_canonical);
            Self {
                name: UnixStr(canon),
            }
        }
    }

    /// Yields the underlying [`UnixStr`] slice.
    #[inline]
    #[must_use]
    pub const fn as_unix_str(&self) -> &UnixStr {
        &self.name
    }

    /// Yields a mutable referebce to the underlying [`UnixStr`] slice.
    #[inline]
    #[must_use]
    pub const fn as_mut_unix_str(&mut self) -> &mut UnixStr {
        &mut self.name
    }
}

impl FromStr for Path {
    type Err = &'static str;

    #[inline]
    fn from_str(str: &str) -> Result<Self, Self::Err> {
        Ok(Self::new(UnixStr::from_str(str)?))
    }
}

impl PartialEq for Path {
    /// This method tests for `self` and `other` values to be equal, and is used by `==`.
    ///
    /// This checks for equivalence in the pathname, not strict equality or pathname resolution.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::str::FromStr;
    ///
    /// use efs::path::{Path, UnixStr};
    ///
    /// assert_eq!(Path::from_str("/").unwrap(), Path::from_str("///").unwrap());
    ///
    /// assert_eq!(Path::from_str("/home//").unwrap(), Path::from_str("///home/").unwrap());
    ///
    /// assert_eq!(Path::from_str("//").unwrap(), Path::from_str("//").unwrap());
    ///
    /// assert_ne!(Path::from_str("/").unwrap(), Path::from_str("//").unwrap());
    /// assert_ne!(Path::from_str("//home").unwrap(), Path::from_str("/home").unwrap());
    /// ```
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if (self.name.starts_with_two_slashes() && !other.name.starts_with_two_slashes())
            || (!self.name.starts_with_two_slashes() && other.name.starts_with_two_slashes())
        {
            return false;
        }

        match (self.name.0.strip_prefix('/'), other.name.0.strip_prefix('/')) {
            (None, None) | (Some(_), Some(_)) => {},
            _ => return false,
        }

        match (self.name.0.strip_suffix('/'), other.name.0.strip_suffix('/')) {
            (None, None) | (Some(_), Some(_)) => {},
            _ => return false,
        }

        let self_chars = self.name.0.chars().filter(|ch| ch != &'/').collect::<Vec<char>>();
        let other_chars = other.name.0.chars().filter(|ch| ch != &'/').collect::<Vec<char>>();

        self_chars == other_chars
    }
}

impl Eq for Path {}

/// Root directory
pub static ROOT: Lazy<Path> = Lazy::new(|| Path::from_str("/").unwrap_or_else(|_| unreachable!("ROOT is a non-empty path")));

#[cfg(test)]
mod test {
    use core::str::FromStr;

    use crate::path::{Path, UnixStr};

    #[test]
    fn unix_str_creation() {
        assert!(UnixStr::new("/").is_some());
        assert!(UnixStr::new("/home//user///foo").is_some());

        assert!(UnixStr::new("").is_none());
        assert!(UnixStr::new("/home//user///\0foo").is_none());
    }

    #[test]
    fn path_eq() {
        assert_eq!(Path::from_str("/").unwrap(), Path::from_str("/").unwrap());
        assert_eq!(Path::from_str("/").unwrap(), Path::from_str("///").unwrap());
        assert_eq!(Path::from_str("///").unwrap(), Path::from_str("/").unwrap());

        assert_eq!(Path::from_str("/home").unwrap(), Path::from_str("/home").unwrap());
        assert_eq!(Path::from_str("/home//").unwrap(), Path::from_str("///home/").unwrap());

        assert_eq!(Path::from_str("//").unwrap(), Path::from_str("//").unwrap());
        assert_eq!(Path::from_str("//home/").unwrap(), Path::from_str("//home/").unwrap());

        assert_ne!(Path::from_str("/").unwrap(), Path::from_str("//").unwrap());
        assert_ne!(Path::from_str("//home").unwrap(), Path::from_str("/home").unwrap());
    }

    #[test]
    fn path_canonical() {
        assert_eq!(Path::from_str("/").unwrap(), Path::from_str("/").unwrap());
        assert_eq!(Path::from_str("/").unwrap(), Path::from_str("///").unwrap());
        assert_eq!(Path::from_str("///").unwrap(), Path::from_str("/").unwrap());

        assert_eq!(Path::from_str("/home").unwrap(), Path::from_str("/home").unwrap());
        assert_eq!(Path::from_str("/home//").unwrap(), Path::from_str("///home/").unwrap());

        assert_eq!(Path::from_str("//").unwrap(), Path::from_str("//").unwrap());
        assert_eq!(Path::from_str("//home/").unwrap(), Path::from_str("//home/").unwrap());

        assert_ne!(Path::from_str("/").unwrap(), Path::from_str("//").unwrap());
        assert_ne!(Path::from_str("//home").unwrap(), Path::from_str("/home").unwrap());
    }
}
