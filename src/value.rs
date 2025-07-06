use crate::atom::Atom;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Integer(i64),
    Atom(Atom),
    String(String),
    Float(f64),
    Boolean(bool),
}

impl Value {
    pub fn integer(value: i64) -> Self {
        Self::Integer(value)
    }

    pub fn atom(atom: Atom) -> Self {
        Self::Atom(atom)
    }

    pub fn string<T: Into<String>>(value: T) -> Self {
        Self::String(value.into())
    }

    pub fn float(value: f64) -> Self {
        Self::Float(value)
    }

    pub fn boolean(value: bool) -> Self {
        Self::Boolean(value)
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Integer(i) => write!(f, "{}", i),
            Value::Atom(a) => write!(f, "{}", a),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Float(fl) => write!(f, "{}", fl),
            Value::Boolean(b) => write!(f, "{}", b),
        }
    }
}

impl Eq for Value {}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Value::Integer(i) => {
                0.hash(state);
                i.hash(state);
            }
            Value::Atom(a) => {
                1.hash(state);
                a.hash(state);
            }
            Value::String(s) => {
                2.hash(state);
                s.hash(state);
            }
            Value::Float(fl) => {
                3.hash(state);
                fl.to_bits().hash(state);
            }
            Value::Boolean(b) => {
                4.hash(state);
                b.hash(state);
            }
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Value::Integer(a), Value::Integer(b)) => a.cmp(b),
            (Value::Atom(a), Value::Atom(b)) => a.cmp(b),
            (Value::String(a), Value::String(b)) => a.cmp(b),
            (Value::Float(a), Value::Float(b)) => a.partial_cmp(b).unwrap_or(Ordering::Equal),
            (Value::Boolean(a), Value::Boolean(b)) => a.cmp(b),
            (Value::Integer(_), _) => Ordering::Less,
            (Value::Atom(_), Value::Integer(_)) => Ordering::Greater,
            (Value::Atom(_), _) => Ordering::Less,
            (Value::String(_), Value::Integer(_) | Value::Atom(_)) => Ordering::Greater,
            (Value::String(_), _) => Ordering::Less,
            (Value::Float(_), Value::Integer(_) | Value::Atom(_) | Value::String(_)) => {
                Ordering::Greater
            }
            (Value::Float(_), _) => Ordering::Less,
            (Value::Boolean(_), _) => Ordering::Greater,
        }
    }
}
