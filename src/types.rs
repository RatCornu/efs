//! Definitions of needed types

use derive_more::{Deref, DerefMut};

/// Used for device IDs
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Dev(pub u16);

// impl Dev {
//     /// Major device ID
//     pub fn major(&self) -> u16 {
//         todo!()
//     }
//
//     /// Minor device ID
//     pub fn minor(&self) -> u16 {
//         todo!()
//     }
//
//     /// Create a device ID from a major and a minor device ID
//     pub fn makedev(major: u16, minor: u16) -> Self {
//         todo!()
//     }
// }

/// Used for file serial numbers
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Ino(pub u32);

/// Used for some file attributes
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Mode(pub u16);

/// Used for link counts
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Nlink(pub u32);

/// Used for user IDs
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Uid(pub u16);

/// Used for group IDs
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Gid(pub u16);

/// Used for file sizes
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Off(pub i32);

/// Used for block sizes
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Blksize(pub i32);

/// Used for file block counts
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Blkcnt(pub i32);

/// Used for time in seconds
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Time(pub i32);

/// Used for time in seconds
///
/// Times shall be given in seconds since the Epoch
#[derive(Debug, Clone, Copy)]
pub struct Timespec {
    /// Seconds
    pub tv_sec: Time,

    /// Nanoseconds
    pub tv_nsec: u32,
}
