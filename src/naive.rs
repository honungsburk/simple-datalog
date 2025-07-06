//! Naive implementation of Datalog
//!
//! This is pretty much the simplest thing you can get away with. Checkout the `semi_naive` module for a more
//! optimized implementation.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};

/// A term in a Datalog program - either a value or a variable
#[derive(Debug, Clone)]
pub enum Term<T> {
    Value(T),
    Variable(String),
}

impl<T> Term<T> {
    pub fn value(value: T) -> Self {
        Term::Value(value)
    }

    pub fn variable<S: Into<String>>(name: S) -> Self {
        Term::Variable(name.into())
    }
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

impl<T> Tuple<T> {
    pub fn new(terms: Vec<Term<T>>) -> Self {
        Tuple(terms)
    }

    pub fn from_values(values: Vec<T>) -> Self {
        Tuple(values.into_iter().map(Term::value).collect())
    }

    pub fn from_variables<S: Into<String>>(vars: Vec<S>) -> Self {
        Tuple(vars.into_iter().map(|v| Term::variable(v)).collect())
    }
}

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

impl<T> Rule<T> {
    pub fn new() -> RuleBuilder<T> {
        RuleBuilder::new()
    }
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

/// Builder for creating Datalog rules
pub struct RuleBuilder<T> {
    heads: Vec<(String, Tuple<T>)>,
    body: Vec<(String, Tuple<T>)>,
}

impl<T> RuleBuilder<T> {
    pub fn new() -> Self {
        RuleBuilder {
            heads: Vec::new(),
            body: Vec::new(),
        }
    }

    pub fn head<S: Into<String>>(mut self, relation: S, tuple: Tuple<T>) -> Self {
        self.heads.push((relation.into(), tuple));
        self
    }

    pub fn body<S: Into<String>>(mut self, relation: S, tuple: Tuple<T>) -> Self {
        self.body.push((relation.into(), tuple));
        self
    }

    pub fn build(self) -> Rule<T> {
        Rule {
            heads: self.heads,
            body: self.body,
        }
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
        let grandparent_rule = Rule::new()
            .head("grandparent", Tuple::from_variables(vec!["X", "Z"]))
            .body("parent", Tuple::from_variables(vec!["X", "Y"]))
            .body("parent", Tuple::from_variables(vec!["Y", "Z"]))
            .build();

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
        let path_rule = Rule::new()
            .head("path", Tuple::from_variables(vec!["X", "Z"]))
            .body("edge", Tuple::from_variables(vec!["X", "Y"]))
            .body("edge", Tuple::from_variables(vec!["Y", "Z"]))
            .build();

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
        let multi_head_rule = Rule::new()
            .head("human", Tuple::from_variables(vec!["X"]))
            .head("mortal", Tuple::from_variables(vec!["X"]))
            .body("person", Tuple::from_variables(vec!["X"]))
            .build();

        db.add_rule(multi_head_rule);
        db.evaluate();

        let human_relation = db.get_relation("human").unwrap();
        let mortal_relation = db.get_relation("mortal").unwrap();

        assert!(human_relation.contains(&vec!["alice"]));
        assert!(human_relation.contains(&vec!["bob"]));
        assert!(mortal_relation.contains(&vec!["alice"]));
        assert!(mortal_relation.contains(&vec!["bob"]));
    }

    #[test]
    fn test_mixed_value_types() {
        use crate::atom::Atom;
        use crate::value::Value;

        let mut db = Database::new();

        // Insert facts with different value types
        db.insert_fact(
            "person",
            vec![
                Value::string("alice"),
                Value::integer(25),
                Value::boolean(true),
                Value::atom(Atom::new(1)),
                Value::float(5.5),
            ],
        );

        db.insert_fact(
            "person",
            vec![
                Value::string("bob"),
                Value::integer(30),
                Value::boolean(false),
                Value::atom(Atom::new(2)),
                Value::float(6.2),
            ],
        );

        db.insert_fact(
            "config",
            vec![
                Value::string("max_age"),
                Value::integer(100),
                Value::boolean(true),
            ],
        );

        // Rule: adult(X, Age) :- person(X, Age, B, A, F)
        let adult_rule = Rule::new()
            .head("adult", Tuple::from_variables(vec!["X", "Age"]))
            .body(
                "person",
                Tuple::from_variables(vec!["X", "Age", "B", "A", "F"]),
            )
            .build();

        db.add_rule(adult_rule);
        db.evaluate();

        let person_relation = db.get_relation("person").unwrap();
        let adult_relation = db.get_relation("adult").unwrap();
        let config_relation = db.get_relation("config").unwrap();

        // Verify facts with mixed types are stored correctly
        assert!(person_relation.contains(&vec![
            Value::string("alice"),
            Value::integer(25),
            Value::boolean(true),
            Value::atom(Atom::new(1)),
            Value::float(5.5)
        ]));

        assert!(person_relation.contains(&vec![
            Value::string("bob"),
            Value::integer(30),
            Value::boolean(false),
            Value::atom(Atom::new(2)),
            Value::float(6.2)
        ]));

        assert!(config_relation.contains(&vec![
            Value::string("max_age"),
            Value::integer(100),
            Value::boolean(true)
        ]));

        // Verify rule evaluation works with mixed types
        assert!(adult_relation.contains(&vec![Value::string("alice"), Value::integer(25)]));

        assert!(adult_relation.contains(&vec![Value::string("bob"), Value::integer(30)]));

        // Verify different value types are distinct
        assert!(!person_relation.contains(&vec![
            Value::string("alice"),
            Value::integer(25),
            Value::boolean(false), // Different boolean
            Value::atom(Atom::new(1)),
            Value::float(5.5)
        ]));

        assert!(!person_relation.contains(&vec![
            Value::string("alice"),
            Value::integer(25),
            Value::boolean(true),
            Value::atom(Atom::new(3)), // Different atom
            Value::float(5.5)
        ]));
    }

    #[test]
    fn test_semi_naive_optimization() {
        let mut db = Database::new();

        // Create a chain of relationships: a->b->c->d->e
        db.insert_fact("edge", vec![1, 2]);
        db.insert_fact("edge", vec![2, 3]);
        db.insert_fact("edge", vec![3, 4]);
        db.insert_fact("edge", vec![4, 5]);

        // Rule: path(X, Z) :- edge(X, Y), path(Y, Z)
        // Rule: path(X, Y) :- edge(X, Y)
        let path_rule1 = Rule::new()
            .head("path", Tuple::from_variables(vec!["X", "Y"]))
            .body("edge", Tuple::from_variables(vec!["X", "Y"]))
            .build();

        let path_rule2 = Rule::new()
            .head("path", Tuple::from_variables(vec!["X", "Z"]))
            .body("edge", Tuple::from_variables(vec!["X", "Y"]))
            .body("path", Tuple::from_variables(vec!["Y", "Z"]))
            .build();

        db.add_rule(path_rule1);
        db.add_rule(path_rule2);
        db.evaluate();

        let path_relation = db.get_relation("path").unwrap();

        // Should derive all transitive paths
        assert!(path_relation.contains(&vec![1, 2]));
        assert!(path_relation.contains(&vec![2, 3]));
        assert!(path_relation.contains(&vec![3, 4]));
        assert!(path_relation.contains(&vec![4, 5]));
        assert!(path_relation.contains(&vec![1, 3]));
        assert!(path_relation.contains(&vec![2, 4]));
        assert!(path_relation.contains(&vec![3, 5]));
        assert!(path_relation.contains(&vec![1, 4]));
        assert!(path_relation.contains(&vec![2, 5]));
        assert!(path_relation.contains(&vec![1, 5]));
    }

    #[test]
    fn test_rule_builder_api() {
        let mut db = Database::new();

        db.insert_fact("parent", vec!["alice", "bob"]);
        db.insert_fact("parent", vec!["bob", "charlie"]);

        // Test the new RuleBuilder API
        let rule = Rule::new()
            .head("grandparent", Tuple::from_variables(vec!["X", "Z"]))
            .body("parent", Tuple::from_variables(vec!["X", "Y"]))
            .body("parent", Tuple::from_variables(vec!["Y", "Z"]))
            .build();

        db.add_rule(rule);
        db.evaluate();

        let grandparent_relation = db.get_relation("grandparent").unwrap();
        assert!(grandparent_relation.contains(&vec!["alice", "charlie"]));
    }

    #[test]
    fn test_tuple_creation_methods_int() {
        // Test Tuple::from_values for integers
        let value_tuple: Tuple<i32> = Tuple::from_values(vec![1, 2, 3]);
        assert_eq!(value_tuple.0.len(), 3);
        assert!(matches!(value_tuple.0[0], Term::Value(1)));
        assert!(matches!(value_tuple.0[1], Term::Value(2)));
        assert!(matches!(value_tuple.0[2], Term::Value(3)));

        // Test Tuple::from_variables for integers (variable names are still strings)
        let var_tuple: Tuple<i32> = Tuple::from_variables(vec!["X", "Y", "Z"]);
        assert_eq!(var_tuple.0.len(), 3);
        assert!(matches!(var_tuple.0[0], Term::Variable(ref v) if v == "X"));
        assert!(matches!(var_tuple.0[1], Term::Variable(ref v) if v == "Y"));
        assert!(matches!(var_tuple.0[2], Term::Variable(ref v) if v == "Z"));
    }

    #[test]
    fn test_tuple_creation_methods_str() {
        // Test Tuple::from_values for strings
        let value_tuple: Tuple<&str> = Tuple::from_values(vec!["alice", "bob", "carol"]);
        assert_eq!(value_tuple.0.len(), 3);
        assert!(matches!(value_tuple.0[0], Term::Value("alice")));
        assert!(matches!(value_tuple.0[1], Term::Value("bob")));
        assert!(matches!(value_tuple.0[2], Term::Value("carol")));

        // Test Tuple::from_variables for strings
        let var_tuple: Tuple<&str> = Tuple::from_variables(vec!["X", "Y", "Z"]);
        assert_eq!(var_tuple.0.len(), 3);
        assert!(matches!(var_tuple.0[0], Term::Variable(ref v) if v == "X"));
        assert!(matches!(var_tuple.0[1], Term::Variable(ref v) if v == "Y"));
        assert!(matches!(var_tuple.0[2], Term::Variable(ref v) if v == "Z"));
    }
}
