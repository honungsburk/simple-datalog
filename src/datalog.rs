use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};

/// A term in a Datalog program - either a value or a variable
#[derive(Debug, Clone)]
pub enum Term<T> {
    Value(T),
    Variable(String),
}

impl<T: PartialEq> PartialEq for Term<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Term::Value(a), Term::Value(b)) => a == b,
            (Term::Variable(a), Term::Variable(b)) => a == b,
            _ => false,
        }
    }
}

impl<T: Eq> Eq for Term<T> {}

impl<T: Hash> Hash for Term<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Term::Value(v) => {
                0.hash(state);
                v.hash(state);
            }
            Term::Variable(v) => {
                1.hash(state);
                v.hash(state);
            }
        }
    }
}

impl<T: fmt::Display> fmt::Display for Term<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Value(v) => write!(f, "{}", v),
            Term::Variable(v) => write!(f, "?{}", v),
        }
    }
}

/// A tuple of terms representing a fact or goal
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Tuple<T>(pub Vec<Term<T>>);

impl<T: fmt::Display> fmt::Display for Tuple<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, term) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", term)?;
        }
        write!(f, ")")
    }
}

/// A substitution mapping variable names to values
#[derive(Debug, Clone)]
pub struct Substitution<T>(HashMap<String, T>);

impl<T> Substitution<T> {
    pub fn new() -> Self {
        Substitution(HashMap::new())
    }

    pub fn insert(&mut self, var: String, value: T) {
        self.0.insert(var, value);
    }

    pub fn get(&self, var: &str) -> Option<&T> {
        self.0.get(var)
    }

    pub fn extend(&mut self, other: &Substitution<T>)
    where
        T: Clone,
    {
        for (k, v) in &other.0 {
            self.0.insert(k.clone(), v.clone());
        }
    }
}

/// A relation containing a set of tuples
#[derive(Debug, Clone)]
pub struct Relation<T> {
    pub name: String,
    pub tuples: HashSet<Vec<T>>,
}

impl<T> Relation<T>
where
    T: Clone + Eq + Hash,
{
    pub fn new(name: String) -> Self {
        Relation {
            name,
            tuples: HashSet::new(),
        }
    }

    pub fn insert(&mut self, tuple: Vec<T>) {
        self.tuples.insert(tuple);
    }

    pub fn contains(&self, tuple: &[T]) -> bool {
        self.tuples.contains(tuple)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Vec<T>> {
        self.tuples.iter()
    }

    pub fn len(&self) -> usize {
        self.tuples.len()
    }
}

/// A Datalog rule: heads :- body
#[derive(Debug, Clone)]
pub struct Rule<T> {
    pub heads: Vec<(String, Tuple<T>)>,
    pub body: Vec<(String, Tuple<T>)>,
}

impl<T: fmt::Display> fmt::Display for Rule<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, (rel, tuple)) in self.heads.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}({})", rel, tuple)?;
        }
        write!(f, " :- ")?;
        for (i, (rel, tuple)) in self.body.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}({})", rel, tuple)?;
        }
        Ok(())
    }
}

/// The main Datalog database engine
#[derive(Debug)]
pub struct Database<T> {
    relations: HashMap<String, Relation<T>>,
    rules: Vec<Rule<T>>,
}

impl<T> Database<T>
where
    T: Clone + Eq + Hash + Ord,
{
    pub fn new() -> Self {
        Database {
            relations: HashMap::new(),
            rules: Vec::new(),
        }
    }

    pub fn add_relation(&mut self, relation: Relation<T>) {
        self.relations.insert(relation.name.clone(), relation);
    }

    pub fn get_relation(&self, name: &str) -> Option<&Relation<T>> {
        self.relations.get(name)
    }

    pub fn get_relation_mut(&mut self, name: &str) -> Option<&mut Relation<T>> {
        self.relations.get_mut(name)
    }

    pub fn add_rule(&mut self, rule: Rule<T>) {
        self.rules.push(rule);
    }

    pub fn insert_fact(&mut self, relation_name: &str, tuple: Vec<T>) {
        if let Some(relation) = self.relations.get_mut(relation_name) {
            relation.insert(tuple);
        } else {
            let mut relation = Relation::new(relation_name.to_string());
            relation.insert(tuple);
            self.relations.insert(relation_name.to_string(), relation);
        }
    }

    /// Evaluate all rules until fixpoint is reached
    pub fn evaluate(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            for rule in self.rules.clone() {
                if self.apply_rule(&rule) {
                    changed = true;
                }
            }
        }
    }

    fn apply_rule(&mut self, rule: &Rule<T>) -> bool {
        let mut new_facts = Vec::new();
        let substitutions = self.find_substitutions(&rule.body);

        for substitution in substitutions {
            for head in &rule.heads {
                if let Some(new_fact) = self.apply_substitution(head, &substitution) {
                    new_facts.push((head.0.clone(), new_fact));
                }
            }
        }

        let mut changed = false;
        for (relation_name, fact) in new_facts {
            let old_size = self
                .relations
                .get(&relation_name)
                .map(|r| r.len())
                .unwrap_or(0);

            self.insert_fact(&relation_name, fact);

            let new_size = self
                .relations
                .get(&relation_name)
                .map(|r| r.len())
                .unwrap_or(0);
            if new_size > old_size {
                changed = true;
            }
        }

        changed
    }

    fn find_substitutions(&self, goals: &[(String, Tuple<T>)]) -> Vec<Substitution<T>> {
        if goals.is_empty() {
            return vec![Substitution::new()];
        }

        let mut results = vec![Substitution::new()];

        for (relation_name, goal_tuple) in goals {
            let mut new_results = Vec::new();

            if let Some(relation) = self.relations.get(relation_name) {
                for substitution in &results {
                    for tuple in relation.iter() {
                        if let Some(new_sub) = self.unify_tuple(goal_tuple, tuple, substitution) {
                            new_results.push(new_sub);
                        }
                    }
                }
            }

            results = new_results;
        }

        results
    }

    fn unify_tuple(
        &self,
        pattern: &Tuple<T>,
        tuple: &[T],
        substitution: &Substitution<T>,
    ) -> Option<Substitution<T>> {
        if pattern.0.len() != tuple.len() {
            return None;
        }

        let mut new_substitution = substitution.clone();

        for (pattern_term, value) in pattern.0.iter().zip(tuple.iter()) {
            match pattern_term {
                Term::Value(pattern_value) => {
                    if pattern_value != value {
                        return None;
                    }
                }
                Term::Variable(var_name) => {
                    if let Some(existing_value) = new_substitution.get(var_name) {
                        if existing_value != value {
                            return None;
                        }
                    } else {
                        new_substitution.insert(var_name.clone(), value.clone());
                    }
                }
            }
        }

        Some(new_substitution)
    }

    fn apply_substitution(
        &self,
        head: &(String, Tuple<T>),
        substitution: &Substitution<T>,
    ) -> Option<Vec<T>> {
        let mut result = Vec::new();

        for term in &head.1 .0 {
            match term {
                Term::Value(v) => result.push(v.clone()),
                Term::Variable(var_name) => {
                    if let Some(value) = substitution.get(var_name) {
                        result.push(value.clone());
                    } else {
                        return None; // Unbound variable
                    }
                }
            }
        }

        Some(result)
    }
}

// Helper macros for ergonomic API
#[macro_export]
macro_rules! term {
    ($value:expr) => {
        Term::Value($value)
    };
}

#[macro_export]
macro_rules! var {
    ($name:expr) => {
        Term::Variable($name.to_string())
    };
}

#[macro_export]
macro_rules! tuple {
    ($($term:expr),*) => {
        Tuple(vec![$($term),*])
    };
}

#[macro_export]
macro_rules! rule {
    ($($head_rel:expr, $head_tuple:expr),+ => $($body_rel:expr, $body_tuple:expr),*) => {
        Rule {
            heads: vec![$(($head_rel.to_string(), $head_tuple)),+],
            body: vec![$(($body_rel.to_string(), $body_tuple)),*],
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_facts() {
        let mut db = Database::new();

        db.insert_fact("parent", vec!["alice", "bob"]);
        db.insert_fact("parent", vec!["bob", "charlie"]);

        let parent_relation = db.get_relation("parent").unwrap();
        assert!(parent_relation.contains(&vec!["alice", "bob"]));
        assert!(parent_relation.contains(&vec!["bob", "charlie"]));
        assert!(!parent_relation.contains(&vec!["alice", "charlie"]));
    }

    #[test]
    fn test_simple_rule() {
        let mut db = Database::new();

        // Facts
        db.insert_fact("parent", vec!["alice", "bob"]);
        db.insert_fact("parent", vec!["bob", "charlie"]);

        // Rule: grandparent(X, Z) :- parent(X, Y), parent(Y, Z)
        let grandparent_rule = rule!(
            "grandparent", tuple![var!("X"), var!("Z")] =>
            "parent", tuple![var!("X"), var!("Y")],
            "parent", tuple![var!("Y"), var!("Z")]
        );

        db.add_rule(grandparent_rule);
        db.evaluate();

        let grandparent_relation = db.get_relation("grandparent").unwrap();
        assert!(grandparent_relation.contains(&vec!["alice", "charlie"]));
    }

    #[test]
    fn test_numeric_values() {
        let mut db = Database::new();

        db.insert_fact("edge", vec![1, 2]);
        db.insert_fact("edge", vec![2, 3]);
        db.insert_fact("edge", vec![3, 4]);

        // Rule: path(X, Z) :- edge(X, Y), edge(Y, Z)
        let path_rule = rule!(
            "path", tuple![var!("X"), var!("Z")] =>
            "edge", tuple![var!("X"), var!("Y")],
            "edge", tuple![var!("Y"), var!("Z")]
        );

        db.add_rule(path_rule);
        db.evaluate();

        let path_relation = db.get_relation("path").unwrap();
        assert!(path_relation.contains(&vec![1, 3]));
        assert!(path_relation.contains(&vec![2, 4]));
    }

    #[test]
    fn test_multiple_heads() {
        let mut db = Database::new();

        db.insert_fact("person", vec!["alice"]);
        db.insert_fact("person", vec!["bob"]);

        // Rule with multiple heads:
        // human(X), mortal(X) :- person(X)
        let multi_head_rule = rule!(
            "human", tuple![var!("X")],
            "mortal", tuple![var!("X")] =>
            "person", tuple![var!("X")]
        );

        db.add_rule(multi_head_rule);
        db.evaluate();

        let human_relation = db.get_relation("human").unwrap();
        let mortal_relation = db.get_relation("mortal").unwrap();

        assert!(human_relation.contains(&vec!["alice"]));
        assert!(human_relation.contains(&vec!["bob"]));
        assert!(mortal_relation.contains(&vec!["alice"]));
        assert!(mortal_relation.contains(&vec!["bob"]));
    }
}
