//! General interface for errors returned with filesystem manipulations

use alloc::string::String;
use core::fmt::{self, Display};
use core::result;

/// A list specifying general categories of I/O error
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Kind {
    ///This operation was interrupted.
    ///
    /// Interrupted operations can typically be retried.
    Interrupted,

    /// A custom error that does not fall under any other error kind.
    ///
    /// This can be used to construct your own [`Error`]s that does not match any [`Kind`].
    Other,
}

impl Kind {
    /// Converts the error kind into a `&'static str`.
    const fn as_str(self) -> &'static str {
        match self {
            Self::Interrupted => "operation interrupted",
            Self::Other => "other error",
        }
    }
}

impl Display for Kind {
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}", self.as_str())
    }
}

/// The error type for operations of reading, writing, seeking, and associated operations.
#[derive(Debug, Clone)]
pub struct Error {
    /// Kind of the error
    kind: Kind,

    /// Arbitrary payload
    description: String,
}

impl Error {
    /// Creates a new error from a known kind of error as well as an arbitrary payload.
    #[inline]
    #[must_use]
    pub const fn new(kind: Kind, error: String) -> Self {
        Self {
            kind,
            description: error,
        }
    }

    /// Creates a new error from an arbitrary payload.
    #[inline]
    #[must_use]
    pub const fn other(error: String) -> Self {
        Self::new(Kind::Other, error)
    }

    /// Returns the [`Kind`] of this error.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> Kind {
        self.kind
    }

    /// Returns the description of this error.
    #[inline]
    #[must_use]
    pub fn description(&self) -> &str {
        &self.description
    }
}

impl Display for Error {
    #[inline]
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}: {}", self.kind, self.description)
    }
}

/// A specialized [`Result`] type for this crate
pub type Result<T> = result::Result<T, Error>;
