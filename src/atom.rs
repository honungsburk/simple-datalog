//! An atom is a unique value. It can be compared for equality but not for ordering.
//!
//! Usually we thing of them as strings, but they are internalized to a u64.
//!
//! See the `internalizer` module for more details.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Atom(u64);

impl Atom {
    pub fn new(id: u64) -> Self {
        Self(id)
    }

    pub fn id(&self) -> u64 {
        self.0
    }
}

impl std::fmt::Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Atom({})", self.0)
    }
}
