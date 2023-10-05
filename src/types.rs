//! Definitions of needed types

use derive_more::{Deref, DerefMut};

/// Used for device IDs
#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct Dev(pub u32);

impl Dev {
    /// Major device ID
    pub fn major(&self) -> u32 {
        todo!()
    }

    /// Minor device ID
    pub fn minor(&self) -> u32 {
        todo!()
    }

    /// Create a device ID from a major and a minor device ID
    pub fn makedev(major: u32, minor: u32) -> Self {
        todo!()
    }
}
