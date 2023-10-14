//! Path manipulation for UNIX-like filesystems

use alloc::borrow::ToOwned;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use once_cell::sync::Lazy;
use regex::Regex;

/// A general structure to implement paths.
///
/// A [`UnixStr`] cannot be empty! It is guaranteed at creation time.
///
/// Beware, the equality is defined [here](#method.eq) and does not correspond to the strict equality.
#[derive(Debug, Clone)]
pub struct UnixStr(String);

impl UnixStr {
    /// Creates a new [`UnixStr`] from a string
    ///
    /// # Example
    ///
    /// ```
    /// # use efs::path::UnixStr;
    /// #
    /// let valid = UnixStr::new("/").unwrap();
    /// ```
    ///
    /// ```should_panic
    /// # use efs::path::UnixStr;
    /// #
    /// let not_valid = UnixStr::new("").unwrap();
    /// ```
    #[inline]
    #[must_use]
    pub fn new(str: &str) -> Option<Self> {
        let path = str.to_owned();
        if path.is_empty() { None } else { Some(Self(path)) }
    }

    /// Checks whether the inner string contains exactly two leading '/' characters
    fn starts_with_two_slashes(&self) -> bool {
        self.0.starts_with("//") && !self.0.starts_with("///")
    }

    /// Returns the canonical path associated with `self`
    ///
    /// # Example
    ///
    /// ```
    /// # use efs::path::UnixStr;
    /// #
    /// assert_eq!(
    ///     UnixStr::new("/home/user/foo").unwrap(),
    ///     UnixStr::new("/home//user///foo").unwrap().canonical()
    /// );
    ///
    /// assert_eq!(
    ///     UnixStr::new("//bin/foo").unwrap(),
    ///     UnixStr::new("//bin///foo").unwrap().canonical()
    /// );
    ///
    /// assert_eq!(UnixStr::new("./foo/bar").unwrap(), UnixStr::new("foo/bar").unwrap().canonical());
    /// assert_eq!(
    ///     UnixStr::new("./foo/bar/").unwrap(),
    ///     UnixStr::new("foo///bar//").unwrap().canonical()
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn canonical(&self) -> Self {
        /// Regex matching one slash or more
        static SLASHES: Lazy<Regex> = Lazy::new(|| Regex::new("/+").unwrap_or_else(|_| unreachable!()));

        let almost_canonical = SLASHES.replace_all(self.0.as_str(), "/").to_string();
        if self.starts_with_two_slashes() {
            let mut canon = "/".to_owned();
            canon.push_str(&almost_canonical);
            Self(canon)
        } else if almost_canonical.starts_with('/') {
            Self(almost_canonical)
        } else {
            let mut canon = "./".to_owned();
            canon.push_str(&almost_canonical);
            Self(canon)
        }
    }
}

impl PartialEq for UnixStr {
    /// This method tests for `self` and `other` values to be equal, and is used by `==`.
    ///
    /// This checks for equivalence in the pathname, not strict equality or pathname resolution.
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if (self.starts_with_two_slashes() && !other.starts_with_two_slashes())
            || (!self.starts_with_two_slashes() && other.starts_with_two_slashes())
        {
            return false;
        }

        match (self.0.strip_prefix('/'), other.0.strip_prefix('/')) {
            (None, None) | (Some(_), Some(_)) => {},
            _ => return false,
        }

        match (self.0.strip_suffix('/'), other.0.strip_suffix('/')) {
            (None, None) | (Some(_), Some(_)) => {},
            _ => return false,
        }

        let self_chars = self.0.chars().filter(|ch| ch != &'/').collect::<Vec<char>>();
        let other_chars = other.0.chars().filter(|ch| ch != &'/').collect::<Vec<char>>();

        self_chars == other_chars
    }
}

impl Eq for UnixStr {}

/// A slice of a path
#[derive(Debug, Clone)]
pub struct Path {
    /// A string that is used to identify a file. It has optional beginning `/`, followed by zero or more filenames separated by
    /// `/`. A pathname can optionally contain one or more trailing `/`. Multiple successive `/` characters are considered to be
    /// the same as one `/`, except for the case of exactly two leading `/`.
    ///
    /// See [the POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_271) for more informations.
    pub name: UnixStr,
}

impl Path {
    /// Checks if the path is absolute.
    ///
    /// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_02).
    #[inline]
    #[must_use]
    pub fn is_absolute(&self) -> bool {
        self.name.0.starts_with('/')
    }

    /// Checks if the path is absolute.
    ///
    /// Defined in [this POSIX definition](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap03.html#tag_03_324).
    #[inline]
    #[must_use]
    pub fn is_relative(&self) -> bool {
        !self.is_absolute()
    }
}

#[cfg(test)]
mod test {
    use crate::path::UnixStr;

    #[test]
    fn unix_str_eq() {
        assert_eq!(UnixStr("/".to_owned()), UnixStr("/".to_owned()));
        assert_eq!(UnixStr("/".to_owned()), UnixStr("///".to_owned()));
        assert_eq!(UnixStr("///".to_owned()), UnixStr("/".to_owned()));

        assert_eq!(UnixStr("/home".to_owned()), UnixStr("/home".to_owned()));
        assert_eq!(UnixStr("/home//".to_owned()), UnixStr("///home/".to_owned()));

        assert_eq!(UnixStr("//".to_owned()), UnixStr("//".to_owned()));
        assert_eq!(UnixStr("//home/".to_owned()), UnixStr("//home/".to_owned()));

        assert_ne!(UnixStr("/".to_owned()), UnixStr("//".to_owned()));
        assert_ne!(UnixStr("//home".to_owned()), UnixStr("/home".to_owned()));
    }
}
