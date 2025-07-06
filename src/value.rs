use crate::atom::Atom;

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

    pub fn string(value: String) -> Self {
        Self::String(value)
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
