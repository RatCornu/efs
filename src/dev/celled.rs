//! TODO

use alloc::rc::Rc;
use core::cell::RefCell;

use derive_more::{Deref, DerefMut};

/// Type alias for celled objects.
#[derive(Deref, DerefMut)]
pub struct Celled<T>(Rc<RefCell<T>>);

impl<T> Clone for Celled<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl<T> Celled<T> {
    /// Creates a new celled object.
    #[inline]
    pub fn new(obj: T) -> Self {
        Self(Rc::new(RefCell::new(obj)))
    }
}
