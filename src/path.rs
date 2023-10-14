//! Path manipulation for UNIX-like filesystems

use alloc::string::String;
use alloc::vec::Vec;

use derive_more::{Deref, DerefMut};

/// A general structure to implement paths.
///
/// A [`UnixStr`] cannot be empty! It is guaranteed at creation time.
///
/// Beware, the equality is defined [here](#method.eq) and does not correspond to the strict equality.
#[derive(Debug, Clone, Deref, DerefMut)]
pub struct UnixStr(String);

impl UnixStr {
    /// Checks whether the inner string contains exactly two leading '/' characters
    fn starts_with_two_slashes(&self) -> bool {
        self.starts_with("//") && !self.starts_with("///")
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

        match (self.strip_prefix('/'), other.strip_prefix('/')) {
            (None, None) | (Some(_), Some(_)) => {},
            _ => return false,
        }

        match (self.strip_suffix('/'), other.strip_suffix('/')) {
            (None, None) | (Some(_), Some(_)) => {},
            _ => return false,
        }

        let self_chars = self.chars().filter(|ch| ch != &'/').collect::<Vec<char>>();
        let other_chars = other.chars().filter(|ch| ch != &'/').collect::<Vec<char>>();

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
        todo!()
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

        assert_ne!(UnixStr("/".to_owned()), UnixStr("//".to_owned()));
    }
}
