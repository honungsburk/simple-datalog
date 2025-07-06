//! String internalization for efficient atom creation.
//!
//! This module provides the `Internalizer` struct which converts strings into unique
//! `Atom` values. The same string will always produce the same atom, allowing for
//! efficient string comparison and storage.
//!
//! # Examples
//!
//! ```
//! use simple_datalog::{Internalizer, Atom};
//!
//! let mut internalizer = Internalizer::new();
//! let atom1 = internalizer.intern("hello");
//! let atom2 = internalizer.intern("world");
//! let atom3 = internalizer.intern("hello"); // Same as atom1
//!
//! assert_eq!(atom1, atom3);
//! assert_ne!(atom1, atom2);
//! assert_eq!(internalizer.get_string(atom1), Some("hello"));
//! ```

use crate::atom::Atom;
use std::collections::HashMap;

/// Converts strings into unique atoms and provides bidirectional mapping.
///
/// The internalizer maintains two data structures:
/// - A `Vec<String>` for O(1) atom-to-string lookup by index
/// - A `HashMap<String, u64>` for O(1) string-to-atom lookup
///
/// This design ensures efficient conversion in both directions while
/// guaranteeing that identical strings always produce the same atom.
///
/// # Examples
///
/// ```
/// use simple_datalog::Internalizer;
///
/// let mut internalizer = Internalizer::new();
/// let atom = internalizer.intern("example");
/// assert_eq!(internalizer.get_string(atom), Some("example"));
/// ```
pub struct Internalizer {
    strings: Vec<String>,
    string_to_id: HashMap<String, u64>,
}

impl Internalizer {
    /// Creates a new empty internalizer.
    ///
    /// # Examples
    ///
    /// ```
    /// use simple_datalog::Internalizer;
    ///
    /// let internalizer = Internalizer::new();
    /// assert!(internalizer.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            strings: Vec::new(),
            string_to_id: HashMap::new(),
        }
    }

    /// Converts a string into an atom, reusing existing atoms for identical strings.
    ///
    /// If the string has been interned before, returns the existing atom.
    /// Otherwise, creates a new atom and stores the string for future lookups.
    ///
    /// # Arguments
    ///
    /// * `s` - The string to intern
    ///
    /// # Returns
    ///
    /// An `Atom` that uniquely represents the input string.
    ///
    /// # Examples
    ///
    /// ```
    /// use simple_datalog::Internalizer;
    ///
    /// let mut internalizer = Internalizer::new();
    /// let atom1 = internalizer.intern("hello");
    /// let atom2 = internalizer.intern("hello");
    /// assert_eq!(atom1, atom2);
    /// ```
    pub fn intern(&mut self, s: &str) -> Atom {
        if let Some(&id) = self.string_to_id.get(s) {
            Atom::new(id)
        } else {
            let id = self.strings.len() as u64;
            let owned_string = s.to_string();
            self.strings.push(owned_string.clone());
            self.string_to_id.insert(owned_string, id);
            Atom::new(id)
        }
    }

    /// Retrieves the original string from an atom.
    ///
    /// Returns `None` if the atom was not created by this internalizer
    /// or if the atom ID is out of bounds.
    ///
    /// # Arguments
    ///
    /// * `atom` - The atom to look up
    ///
    /// # Returns
    ///
    /// `Some(&str)` containing the original string, or `None` if not found.
    ///
    /// # Examples
    ///
    /// ```
    /// use simple_datalog::Internalizer;
    ///
    /// let mut internalizer = Internalizer::new();
    /// let atom = internalizer.intern("hello");
    /// assert_eq!(internalizer.get_string(atom), Some("hello"));
    /// ```
    pub fn get_string(&self, atom: Atom) -> Option<&str> {
        self.strings.get(atom.id() as usize).map(|s| s.as_str())
    }

    /// Returns the number of unique strings that have been interned.
    ///
    /// # Examples
    ///
    /// ```
    /// use simple_datalog::Internalizer;
    ///
    /// let mut internalizer = Internalizer::new();
    /// assert_eq!(internalizer.len(), 0);
    /// internalizer.intern("hello");
    /// assert_eq!(internalizer.len(), 1);
    /// internalizer.intern("hello"); // Duplicate
    /// assert_eq!(internalizer.len(), 1);
    /// internalizer.intern("world");
    /// assert_eq!(internalizer.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Returns `true` if no strings have been interned.
    ///
    /// # Examples
    ///
    /// ```
    /// use simple_datalog::Internalizer;
    ///
    /// let mut internalizer = Internalizer::new();
    /// assert!(internalizer.is_empty());
    /// internalizer.intern("hello");
    /// assert!(!internalizer.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

impl Default for Internalizer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_internalizer() {
        let internalizer = Internalizer::new();
        assert!(internalizer.is_empty());
        assert_eq!(internalizer.len(), 0);
    }

    #[test]
    fn test_intern_single_string() {
        let mut internalizer = Internalizer::new();
        let atom = internalizer.intern("hello");

        assert_eq!(internalizer.len(), 1);
        assert_eq!(internalizer.get_string(atom), Some("hello"));
    }

    #[test]
    fn test_intern_same_string_twice() {
        let mut internalizer = Internalizer::new();
        let atom1 = internalizer.intern("hello");
        let atom2 = internalizer.intern("hello");

        assert_eq!(atom1, atom2);
        assert_eq!(internalizer.len(), 1);
        assert_eq!(internalizer.get_string(atom1), Some("hello"));
        assert_eq!(internalizer.get_string(atom2), Some("hello"));
    }

    #[test]
    fn test_intern_different_strings() {
        let mut internalizer = Internalizer::new();
        let atom1 = internalizer.intern("hello");
        let atom2 = internalizer.intern("world");

        assert_ne!(atom1, atom2);
        assert_eq!(internalizer.len(), 2);
        assert_eq!(internalizer.get_string(atom1), Some("hello"));
        assert_eq!(internalizer.get_string(atom2), Some("world"));
    }

    #[test]
    fn test_get_string_nonexistent() {
        let internalizer = Internalizer::new();
        let atom = Atom::new(999);
        assert_eq!(internalizer.get_string(atom), None);
    }

    #[test]
    fn test_multiple_interns() {
        let mut internalizer = Internalizer::new();

        let atoms: Vec<Atom> = vec!["apple", "banana", "cherry", "apple", "date", "banana"]
            .iter()
            .map(|&s| internalizer.intern(s))
            .collect();

        assert_eq!(internalizer.len(), 4); // unique strings
        assert_eq!(atoms[0], atoms[3]); // "apple" should be same atom
        assert_eq!(atoms[1], atoms[5]); // "banana" should be same atom
        assert_ne!(atoms[0], atoms[1]); // different strings should be different atoms
        assert_ne!(atoms[1], atoms[2]); // different strings should be different atoms
    }

    #[test]
    fn test_empty_string() {
        let mut internalizer = Internalizer::new();
        let atom = internalizer.intern("");

        assert_eq!(internalizer.len(), 1);
        assert_eq!(internalizer.get_string(atom), Some(""));
    }

    #[test]
    fn test_atom_ids_sequential() {
        let mut internalizer = Internalizer::new();
        let atom1 = internalizer.intern("first");
        let atom2 = internalizer.intern("second");
        let atom3 = internalizer.intern("third");

        assert_eq!(atom1.id(), 0);
        assert_eq!(atom2.id(), 1);
        assert_eq!(atom3.id(), 2);
    }
}
