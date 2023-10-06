//! General interface for errors returned with filesystem manipulations

use alloc::string::String;
use core::fmt::Display;

/// A list specifying general categories of I/O error
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub enum Kind {
    /// A custom error that does not fall under any other error kind
    ///
    /// This can be used to construct your own [`Error`]s that does not match any [`Kind`]
    Other,
}

impl Kind {
    /// Converts the error kind into a `&'static str`
    fn as_str(&self) -> &'static str {
        match self {
            Self::Other => "other error",
        }
    }
}

impl Display for Kind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// The error type for operations of reading, writing, seeking, and associated operations
#[derive(Debug, Clone)]
pub struct Error {
    /// Kind of the error
    kind: Kind,

    /// Arbitrary payload
    description: String,
}

impl Error {
    /// Creates a new error from a known kind of error as well as an arbitrary payload
    pub fn new(kind: Kind, error: String) -> Self {
        Self {
            kind,
            description: error,
        }
    }

    /// Creates a new error from an arbitrary payload
    pub fn other(error: String) -> Self {
        Self::new(Kind::Other, error)
    }

    /// Returns the [`Kind`] of this error
    pub fn kind(&self) -> Kind {
        self.kind
    }

    /// Returns the description of this error
    pub fn description<'err>(&'err self) -> &'err str {
        &self.description
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}: {}", self.kind, self.description)
    }
}

/// A specialized [`Result`] type for this crate
pub type Result<T> = core::result::Result<T, Error>;
