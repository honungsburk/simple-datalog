//! Semi-naive implementation of Datalog
//!
//! One step up from the naive implementation. The big idea is to introduce a notion of "stable" and "delta"
//! facts in relations. We know that we have already checked all combinations of stable facts, so we can skip
//! them and new combinations that at least binds to one delta fact.
//!
//! The big changes are in the `find_substitutions` function and the relation struct.

use crate::atom::Atom;
use crate::value::Value;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DatalogError {
    CyclicNegation { rules: HashSet<usize> },
    NonStratifiableProgram,
}

impl fmt::Display for DatalogError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DatalogError::CyclicNegation { rules } => {
                write!(f, "Cyclic negation detected: {:?}", rules)
            }
            DatalogError::NonStratifiableProgram => write!(f, "Program is not stratifiable"),
        }
    }
}

impl std::error::Error for DatalogError {}

/// A term in a Datalog program - either a value or a variable
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Value(Value),
    Variable(String),
    Aggregation(AggregationOp, Vec<Term>),
}

impl Term {
    pub fn integer(value: i64) -> Self {
        Term::Value(Value::integer(value))
    }

    pub fn string(value: &str) -> Self {
        Term::Value(Value::string(value))
    }

    pub fn atom(value: Atom) -> Self {
        Term::Value(Value::atom(value))
    }

    pub fn float(value: f64) -> Self {
        Term::Value(Value::float(value))
    }

    pub fn boolean(value: bool) -> Self {
        Term::Value(Value::boolean(value))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AggregationOp {
    Count,
    Sum,
    Avg,
    Min,
    Max,
    Mean,
}

impl fmt::Display for AggregationOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AggregationOp::Count => write!(f, "count"),
            AggregationOp::Sum => write!(f, "sum"),
            AggregationOp::Avg => write!(f, "avg"),
            AggregationOp::Min => write!(f, "min"),
            AggregationOp::Max => write!(f, "max"),
            AggregationOp::Mean => write!(f, "mean"),
        }
    }
}

impl Term {
    pub fn value(value: Value) -> Self {
        Term::Value(value)
    }

    pub fn variable<S: Into<String>>(name: S) -> Self {
        Term::Variable(name.into())
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Value(v) => write!(f, "{}", v),
            Term::Variable(v) => write!(f, "?{}", v),
            Term::Aggregation(op, terms) => {
                write!(f, "{}", op)?;
                write!(f, "(")?;
                for (i, term) in terms.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", term)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A tuple of terms representing a fact or goal
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Tuple {
    pub terms: Vec<Term>,
    pub is_negated: bool,
}

impl Tuple {
    pub fn new(terms: Vec<Term>) -> Self {
        Tuple {
            terms,
            is_negated: false,
        }
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn terms(&self) -> &[Term] {
        &self.terms
    }

    pub fn iter(&self) -> impl Iterator<Item = &Term> {
        self.terms.iter()
    }

    pub fn from_values(values: Vec<Value>) -> Self {
        Tuple {
            terms: values.into_iter().map(Term::value).collect(),
            is_negated: false,
        }
    }

    pub fn from_variables<S: Into<String>>(vars: Vec<S>) -> Self {
        Tuple {
            terms: vars.into_iter().map(|v| Term::variable(v)).collect(),
            is_negated: false,
        }
    }

    pub fn negate(self) -> Self {
        Tuple {
            terms: self.terms,
            is_negated: !self.is_negated,
        }
    }
}

impl fmt::Display for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, term) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", term)?;
        }
        write!(f, ")")
    }
}

struct Stratifier {
    visited: Vec<bool>,
    strata_assignments: Vec<usize>,
    strata_counter: usize,
    path: Vec<PathElement>,
}

struct PathElement {
    rule: usize,
    is_aggregation: bool,
}

impl Stratifier {
    pub fn new(length: usize) -> Self {
        Self {
            visited: vec![false; length],
            strata_assignments: vec![0; length],
            strata_counter: 0,
            path: Vec::new(),
        }
    }

    pub fn run(&mut self, rules: Vec<Rule>) -> Result<Stratification, DatalogError> {
        if rules.is_empty() {
            return Ok(Stratification::new());
        }

        // Build rule-to-rule dependency graph
        let mut rule_deps: HashMap<usize, Vec<(usize, bool)>> = HashMap::new();
        let mut relation_to_rules: HashMap<String, Vec<usize>> = HashMap::new();

        // Initialize dependency graph
        for (i, rule) in rules.iter().enumerate() {
            rule_deps.insert(i, Vec::new());

            // Track which rules produce each relation
            for relation_name in rule.produces() {
                relation_to_rules
                    .entry(relation_name)
                    .or_insert_with(Vec::new)
                    .push(i);
            }
        }

        // Build dependencies between rules
        for (i, rule) in rules.iter().enumerate() {
            for (relation_name, is_negated) in rule.dependencies() {
                if let Some(producer_rules) = relation_to_rules.get(&relation_name) {
                    for &producer_rule in producer_rules {
                        if producer_rule != i {
                            rule_deps
                                .get_mut(&i)
                                .unwrap()
                                .push((producer_rule, is_negated));
                        }
                    }
                }
            }
        }

        for rule in 0..rules.len() {
            if self.visited[rule] {
                continue;
            }
            let mut current_visited = HashSet::new();
            self.find_strata(rule, &mut current_visited, false, &rule_deps)?;
            for rule in current_visited {
                self.visited[rule] = true;
            }
        }

        let mut stratification = Stratification::new();
        for (i, stratum) in self.strata_assignments.iter().enumerate() {
            stratification
                .strata
                .entry(*stratum)
                .or_insert_with(|| Stratum {
                    id: *stratum,
                    rules: Vec::new(),
                })
                .rules
                .push(rules[i].clone());
        }

        // Build dependency graph
        let mut dependency_graph = HashMap::new();
        for stratum in stratification.strata.values() {
            let mut deps = HashSet::new();
            let mut relations = HashSet::new();
            for rule in stratum.rules.iter() {
                for (relation_name, _) in rule.dependencies() {
                    relations.insert(relation_name);
                }
            }
            for relation in relations {
                if let Some(producers) = relation_to_rules.get(&relation) {
                    for &producer in producers {
                        let strata = self.strata_assignments[producer];
                        deps.insert(strata);
                    }
                }
            }
            dependency_graph.insert(stratum.id, deps);
        }

        stratification.dependency_graph = dependency_graph;

        Ok(stratification)
    }

    /// Find all rules that are parts of cycles and group them into stratas. If
    /// a rule is not part of a cycle, it is alone in its stratum.
    fn find_strata(
        &mut self,
        rule: usize,
        current_visited: &mut HashSet<usize>,
        is_negated: bool,
        rule_deps: &HashMap<usize, Vec<(usize, bool)>>,
    ) -> Result<(), DatalogError> {
        if current_visited.contains(&rule) {
            if is_negated {
                return Err(DatalogError::CyclicNegation {
                    rules: current_visited.clone(),
                });
            }

            // We have found a cycle, store the path on the stack
            let mut stratum = 0;
            // Find if any of the rules in the path have a stratum assignment
            // which means that it is a part of a cycle. If so, we need to assign
            // the same stratum to all the rules that is a part of the cycle we just found, effectively
            // joining the cycle into one stratum.
            for dep_rule in self.path.iter() {
                if rule == dep_rule.rule {
                    self.strata_counter += 1;
                    stratum = self.strata_counter;
                    break;
                }
                if self.strata_assignments[dep_rule.rule] != 0 {
                    stratum = self.strata_assignments[dep_rule.rule];
                    break;
                }
            }

            // Assign the stratum to all the rules that is a part of the cycle we just found, effectively
            // joining the cycle into one stratum.
            for dep_rule in self.path.iter() {
                if rule == dep_rule.rule {
                    break;
                }
                self.strata_assignments[dep_rule.rule] = stratum;
            }

            // Assign the stratum to the rule itself.
            self.strata_assignments[rule] = stratum;

            return Ok(());
        }
        self.path.push(PathElement {
            rule,
            is_aggregation: false,
        });
        current_visited.insert(rule);

        // Recursively find strata for all dependencies
        for (dep_rule, rule_is_negated) in rule_deps.get(&rule).unwrap_or(&Vec::new()) {
            if !self.visited[*dep_rule] {
                self.find_strata(
                    *dep_rule,
                    current_visited,
                    is_negated || *rule_is_negated,
                    rule_deps,
                )?;
            }
        }

        // If the rule has no stratum assignment, assign it a new stratum
        if self.strata_assignments[rule] == 0 {
            self.strata_counter += 1;
            self.strata_assignments[rule] = self.strata_counter;
        }

        self.path.pop();
        Ok(())
    }
}
type StratumID = usize;

pub struct Stratum {
    pub id: StratumID,
    pub rules: Vec<Rule>,
}

pub struct Stratification {
    pub strata: HashMap<StratumID, Stratum>,
    pub dependency_graph: HashMap<StratumID, HashSet<StratumID>>,
}

impl Stratification {
    pub fn new() -> Self {
        Self {
            strata: HashMap::new(),
            dependency_graph: HashMap::new(),
        }
    }

    pub fn from_rules(rules: Vec<Rule>) -> Result<Self, DatalogError> {
        let mut stratifier = Stratifier::new(rules.len());
        stratifier.run(rules)
    }

    pub fn iter(&self) -> Vec<&Stratum> {
        let mut result = Vec::new();
        let mut visited = HashSet::new();

        for stratum_id in self.strata.keys() {
            if !visited.contains(stratum_id) {
                self.topological_sort_visit(*stratum_id, &mut visited, &mut result);
            }
        }

        result
    }

    fn topological_sort_visit<'a>(
        &'a self,
        stratum_id: StratumID,
        visited: &mut HashSet<StratumID>,
        result: &mut Vec<&'a Stratum>,
    ) {
        if visited.contains(&stratum_id) {
            return;
        }

        visited.insert(stratum_id);

        if let Some(dependencies) = self.dependency_graph.get(&stratum_id) {
            for &dep_id in dependencies {
                self.topological_sort_visit(dep_id, visited, result);
            }
        }

        if let Some(stratum) = self.strata.get(&stratum_id) {
            result.push(stratum);
        }
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
    pub stable: HashSet<Vec<T>>,
    pub delta: HashSet<Vec<T>>,
}

impl<T> Relation<T>
where
    T: Clone + Eq + Hash,
{
    pub fn new(name: String) -> Self {
        Relation {
            name,
            stable: HashSet::new(),
            delta: HashSet::new(),
        }
    }

    pub fn insert(&mut self, tuple: Vec<T>) {
        if !self.stable.contains(&tuple) {
            self.delta.insert(tuple);
        }
    }

    pub fn insert_all(&mut self, tuples: Vec<Vec<T>>) {
        for tuple in tuples {
            self.insert(tuple);
        }
    }

    pub fn contains(&self, tuple: &[T]) -> bool {
        self.stable.contains(tuple) || self.delta.contains(tuple)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Vec<T>> {
        self.stable_iter().chain(self.delta_iter())
    }

    pub fn stable_iter(&self) -> impl Iterator<Item = &Vec<T>> {
        self.stable.iter()
    }

    pub fn len(&self) -> usize {
        self.stable.len() + self.delta.len()
    }

    pub fn delta_iter(&self) -> impl Iterator<Item = &Vec<T>> {
        self.delta.iter()
    }

    pub fn ground(&mut self) {
        self.stable.extend(self.delta.drain());
    }
}

/// A Datalog rule: heads :- body
#[derive(Debug, Clone)]
pub struct Rule {
    pub heads: Vec<(String, Tuple)>,
    pub body: Vec<(String, Tuple)>,
}

impl Rule {
    pub fn new() -> RuleBuilder {
        RuleBuilder::new()
    }

    /// Get all relations that this rule depends on (reads from)
    /// The boolean indicates whether the dependency is positive or negative
    /// true means negative, false means positive
    pub fn dependencies(&self) -> HashMap<String, bool> {
        let mut deps = HashMap::new();
        for (relation_name, tuple) in &self.body {
            deps.insert(relation_name.clone(), tuple.is_negated);
        }
        deps
    }

    /// Get all relations that this rule produces (writes to)
    pub fn produces(&self) -> HashSet<String> {
        let mut prods = HashSet::new();
        for (relation_name, _) in &self.heads {
            prods.insert(relation_name.clone());
        }
        prods
    }

    /// Check if this rule has any negative dependencies
    pub fn has_negation(&self) -> bool {
        self.body.iter().any(|(_, tuple)| tuple.is_negated)
    }
}

impl fmt::Display for Rule {
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
pub struct RuleBuilder {
    heads: Vec<(String, Tuple)>,
    body: Vec<(String, Tuple)>,
}

impl RuleBuilder {
    pub fn new() -> Self {
        RuleBuilder {
            heads: Vec::new(),
            body: Vec::new(),
        }
    }

    pub fn head<S: Into<String>>(mut self, relation: S, tuple: Tuple) -> Self {
        self.heads.push((relation.into(), tuple));
        self
    }

    pub fn body<S: Into<String>>(mut self, relation: S, tuple: Tuple) -> Self {
        self.body.push((relation.into(), tuple));
        self
    }

    pub fn body_negative<S: Into<String>>(mut self, relation: S, tuple: Tuple) -> Self {
        let mut negated_tuple = tuple;
        negated_tuple.is_negated = true;
        self.body.push((relation.into(), negated_tuple));
        self
    }

    pub fn build(self) -> Rule {
        Rule {
            heads: self.heads,
            body: self.body,
        }
    }
}

/// The main Datalog database engine
#[derive(Debug)]
pub struct Database {
    relations: HashMap<String, Relation<Value>>,
    rules: Vec<Rule>,
}

impl Database {
    pub fn new() -> Self {
        Database {
            relations: HashMap::new(),
            rules: Vec::new(),
        }
    }

    pub fn add_relation(&mut self, relation: Relation<Value>) {
        self.relations.insert(relation.name.clone(), relation);
    }

    pub fn get_relation(&self, name: &str) -> Option<&Relation<Value>> {
        self.relations.get(name)
    }

    pub fn get_relation_mut(&mut self, name: &str) -> Option<&mut Relation<Value>> {
        self.relations.get_mut(name)
    }

    pub fn add_rule(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    pub fn ground_relation(&mut self, relation_name: &str) {
        if let Some(relation) = self.relations.get_mut(relation_name) {
            relation.ground();
        }
    }

    pub fn insert_fact(&mut self, relation_name: &str, tuple: Vec<Value>) {
        if let Some(relation) = self.relations.get_mut(relation_name) {
            relation.insert(tuple);
        } else {
            let mut relation = Relation::new(relation_name.to_string());
            relation.insert(tuple);
            self.relations.insert(relation_name.to_string(), relation);
        }
    }

    pub fn insert_facts(&mut self, relation_name: &str, facts: Vec<Vec<Value>>) {
        if let Some(relation) = self.relations.get_mut(relation_name) {
            relation.insert_all(facts);
        } else {
            let mut relation = Relation::new(relation_name.to_string());
            relation.insert_all(facts);
            self.relations.insert(relation_name.to_string(), relation);
        }
    }

    pub fn ground_all(&mut self) {
        for relation in self.relations.values_mut() {
            relation.ground();
        }
    }

    pub fn size_of_relation(&self, relation_name: &str) -> usize {
        self.relations
            .get(relation_name)
            .map(|r| r.len())
            .unwrap_or(0)
    }

    /// Evaluate a single stratum
    fn evaluate_stratum(&mut self, rules: &[Rule]) {
        let mut changed = true;
        while changed {
            changed = false;
            for rule in rules {
                if self.apply_rule(rule) {
                    changed = true;
                }
            }
        }
    }

    /// Evaluate all rules using stratified evaluation
    pub fn evaluate(&mut self) -> Result<(), DatalogError> {
        if self.rules.is_empty() {
            return Ok(());
        }

        // Compute stratification
        let stratification = Stratification::from_rules(self.rules.clone())?;

        // Evaluate each stratum in order
        for stratum in stratification.iter() {
            self.evaluate_stratum(&stratum.rules);
        }

        Ok(())
    }

    fn apply_rule(&mut self, rule: &Rule) -> bool {
        let mut new_facts = HashMap::new();
        let substitutions = self.find_substitutions(&rule.body);

        for substitution in substitutions {
            for head in &rule.heads {
                if let Some(new_fact) = self.apply_substitution(head, &substitution) {
                    new_facts
                        .entry(head.0.clone())
                        .or_insert(Vec::new())
                        .push(new_fact);
                }
            }
        }

        let mut changed = false;
        for (relation_name, facts) in new_facts {
            self.ground_relation(&relation_name);

            let old_size = self.size_of_relation(&relation_name);

            self.insert_facts(&relation_name, facts);

            let new_size = self.size_of_relation(&relation_name);
            if new_size > old_size {
                changed = true;
            }
        }

        changed
    }

    fn find_substitutions(&self, goals: &[(String, Tuple)]) -> Vec<Substitution<Value>> {
        if goals.is_empty() {
            return vec![Substitution::new()];
        }

        let mut all_results = Vec::new();

        // Semi-naive evaluation:
        // For each goal position, try using only delta tuples for that position
        // and stable tuples for all other positions
        // This ensures that at least one goal is evaluated using only delta tuples

        // Given three relations: (X, 𝜟X), (Y, 𝜟Y), (Z, 𝜟Z)
        // We want the following combinations:
        // 1. 𝜟X, 𝜟Y, 𝜟Z
        // 2. 𝜟X, 𝜟Y, Z
        // 3. 𝜟X, Y, 𝜟Z
        // 4. X, 𝜟Y, 𝜟Z
        // 5. X, Y, 𝜟Z
        // 6. X, 𝜟Y, Z
        // 7. 𝜟X, Y, Z
        //
        // Count: 2^n - 1 a.k.a. 2^3 - 1 = 7
        //
        // Note that we DO NOT WANT: X, Y, Z
        //
        // This can be rewritten as:
        // 1. 𝜟X, 𝜟Y + Y, 𝜟Z + Z
        // 2. X, 𝜟Y, 𝜟Z + Z
        // 3. X, Y, 𝜟Z
        // Count: n a.k.a. 3
        //
        // This last one reduces the number of iteration of the outer loop which is good when there are many goals and
        // is the one we want to use.

        // We use the starting point to avoid re-evaluating the same goal multiple times.
        let mut starting_point = Some(vec![Substitution::new()]);

        for delta_goal_idx in 0..goals.len() {
            // Use take() to avoid cloning the starting point
            let mut results = starting_point.take().unwrap_or(vec![Substitution::new()]);

            // saturating sub is used to avoid going out of bounds a.k.a. 0 - 1 = 0 instead of panicking
            let start_index = delta_goal_idx.saturating_sub(1);
            for goal_idx in start_index..goals.len() {
                let (relation_name, goal_tuple) = &goals[goal_idx];
                if goal_idx == delta_goal_idx {
                    starting_point = Some(results.clone());
                }
                if goal_tuple.is_negated {
                    // Negative goal, so there can not be ANY matching tuple
                    if let Some(relation) = self.relations.get(relation_name) {
                        let mut new_results = Vec::new();

                        for substitution in results.drain(..) {
                            let mut add = true;
                            if goal_idx == delta_goal_idx {
                                // Use only delta tuples
                                for tuple in relation.delta_iter() {
                                    if let Some(_) =
                                        self.unify_tuple(goal_tuple, tuple, &substitution)
                                    {
                                        add = false;
                                        break;
                                    }
                                }
                            } else if goal_idx < delta_goal_idx {
                                // Use only stable tuples (not delta)
                                for tuple in relation.stable_iter() {
                                    if let Some(_) =
                                        self.unify_tuple(goal_tuple, tuple, &substitution)
                                    {
                                        add = false;
                                        break;
                                    }
                                }
                            } else {
                                // Use both stable and delta tuples
                                for tuple in relation.iter() {
                                    if let Some(_) =
                                        self.unify_tuple(goal_tuple, tuple, &substitution)
                                    {
                                        add = false;
                                        break;
                                    }
                                }
                            }

                            if add {
                                new_results.push(substitution.clone());
                            }
                        }
                        results = new_results;
                    }
                } else {
                    // Positive goal, so we can use any existing substitution that matches the pattern
                    let mut new_results = Vec::new();
                    if let Some(relation) = self.relations.get(relation_name) {
                        for substitution in results.iter() {
                            if goal_idx == delta_goal_idx {
                                // Use only delta tuples
                                for tuple in relation.delta_iter() {
                                    if let Some(new_sub) =
                                        self.unify_tuple(goal_tuple, tuple, substitution)
                                    {
                                        new_results.push(new_sub);
                                    }
                                }
                            } else if goal_idx < delta_goal_idx {
                                // Use only stable tuples (not delta)
                                for tuple in relation.stable_iter() {
                                    if let Some(new_sub) =
                                        self.unify_tuple(goal_tuple, tuple, substitution)
                                    {
                                        new_results.push(new_sub);
                                    }
                                }
                            } else {
                                // Use both stable and delta tuples
                                for tuple in relation.iter() {
                                    if let Some(new_sub) =
                                        self.unify_tuple(goal_tuple, tuple, substitution)
                                    {
                                        new_results.push(new_sub);
                                    }
                                }
                            }
                        }
                    }
                    results = new_results;
                }
            }

            all_results.extend(results);
        }

        all_results
    }

    fn unify_tuple(
        &self,
        pattern: &Tuple,
        tuple: &[Value],
        substitution: &Substitution<Value>,
    ) -> Option<Substitution<Value>> {
        if pattern.len() != tuple.len() {
            return None;
        }

        let mut new_substitution = substitution.clone();

        for (pattern_term, value) in pattern.iter().zip(tuple.iter()) {
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
                _ => {
                    panic!("Aggregation terms are not supported in body");
                }
            }
        }

        Some(new_substitution)
    }

    fn apply_substitution(
        &self,
        head: &(String, Tuple),
        substitution: &Substitution<Value>,
    ) -> Option<Vec<Value>> {
        let mut result = Vec::new();

        for term in head.1.iter() {
            match term {
                Term::Value(v) => result.push(v.clone()),
                Term::Variable(var_name) => {
                    if let Some(value) = substitution.get(var_name) {
                        result.push(value.clone());
                    } else {
                        return None; // Unbound variable
                    }
                }
                _ => {
                    panic!("Aggregation terms are not supported in head");
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

        db.insert_fact("parent", vec![Value::string("alice"), Value::string("bob")]);
        db.insert_fact(
            "parent",
            vec![Value::string("bob"), Value::string("charlie")],
        );

        let parent_relation = db.get_relation("parent").unwrap();
        assert!(parent_relation.contains(&vec![Value::string("alice"), Value::string("bob")]));
        assert!(parent_relation.contains(&vec![Value::string("bob"), Value::string("charlie")]));
        assert!(!parent_relation.contains(&vec![Value::string("alice"), Value::string("charlie")]));
    }

    #[test]
    fn test_simple_rule() {
        let mut db = Database::new();

        // Facts
        db.insert_fact("parent", vec![Value::string("alice"), Value::string("bob")]);
        db.insert_fact(
            "parent",
            vec![Value::string("bob"), Value::string("charlie")],
        );

        // Rule: grandparent(X, Z) :- parent(X, Y), parent(Y, Z)
        let grandparent_rule = Rule::new()
            .head("grandparent", Tuple::from_variables(vec!["X", "Z"]))
            .body("parent", Tuple::from_variables(vec!["X", "Y"]))
            .body("parent", Tuple::from_variables(vec!["Y", "Z"]))
            .build();

        db.add_rule(grandparent_rule);
        db.evaluate().unwrap();

        let grandparent_relation = db.get_relation("grandparent").unwrap();
        assert!(
            grandparent_relation.contains(&vec![Value::string("alice"), Value::string("charlie")])
        );
    }

    #[test]
    fn test_numeric_values() {
        let mut db = Database::new();

        db.insert_fact("edge", vec![Value::integer(1), Value::integer(2)]);
        db.insert_fact("edge", vec![Value::integer(2), Value::integer(3)]);
        db.insert_fact("edge", vec![Value::integer(3), Value::integer(4)]);

        // Rule: path(X, Z) :- edge(X, Y), edge(Y, Z)
        let path_rule = Rule::new()
            .head("path", Tuple::from_variables(vec!["X", "Z"]))
            .body("edge", Tuple::from_variables(vec!["X", "Y"]))
            .body("edge", Tuple::from_variables(vec!["Y", "Z"]))
            .build();

        db.add_rule(path_rule);
        db.evaluate().unwrap();

        let path_relation = db.get_relation("path").unwrap();
        assert!(path_relation.contains(&vec![Value::integer(1), Value::integer(3)]));
        assert!(path_relation.contains(&vec![Value::integer(2), Value::integer(4)]));
    }

    #[test]
    fn test_multiple_heads() {
        let mut db = Database::new();

        db.insert_fact("person", vec![Value::string("alice")]);
        db.insert_fact("person", vec![Value::string("bob")]);

        // Rule with multiple heads:
        // human(X), mortal(X) :- person(X)
        let multi_head_rule = Rule::new()
            .head("human", Tuple::from_variables(vec!["X"]))
            .head("mortal", Tuple::from_variables(vec!["X"]))
            .body("person", Tuple::from_variables(vec!["X"]))
            .build();

        db.add_rule(multi_head_rule);
        db.evaluate().unwrap();

        let human_relation = db.get_relation("human").unwrap();
        let mortal_relation = db.get_relation("mortal").unwrap();

        assert!(human_relation.contains(&vec![Value::string("alice")]));
        assert!(human_relation.contains(&vec![Value::string("bob")]));
        assert!(mortal_relation.contains(&vec![Value::string("alice")]));
        assert!(mortal_relation.contains(&vec![Value::string("bob")]));
    }

    #[test]
    fn test_negation() {
        let mut db = Database::new();

        // Facts
        db.insert_fact("parent", vec![Value::string("alice"), Value::string("bob")]);
        db.insert_fact(
            "parent",
            vec![Value::string("bob"), Value::string("charlie")],
        );
        db.insert_fact("married", vec![Value::string("alice")]);

        // Rule: single_parent(X) :- parent(X, Y), not married(X)
        let single_parent_rule = Rule::new()
            .head("single_parent", Tuple::from_variables(vec!["X"]))
            .body("parent", Tuple::from_variables(vec!["X", "Y"]))
            .body_negative("married", Tuple::from_variables(vec!["X"]))
            .build();

        db.add_rule(single_parent_rule);
        db.evaluate().unwrap();

        let single_parent_relation = db.get_relation("single_parent").unwrap();

        // bob should be a single parent (has child but not married)
        assert!(single_parent_relation.contains(&vec![Value::string("bob")]));
        // alice should not be a single parent (is married)
        assert!(!single_parent_relation.contains(&vec![Value::string("alice")]));
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
        db.evaluate().unwrap();

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
        db.insert_fact("edge", vec![Value::integer(1), Value::integer(2)]);
        db.insert_fact("edge", vec![Value::integer(2), Value::integer(3)]);
        db.insert_fact("edge", vec![Value::integer(3), Value::integer(4)]);
        db.insert_fact("edge", vec![Value::integer(4), Value::integer(5)]);

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
        db.evaluate().unwrap();

        let path_relation = db.get_relation("path").unwrap();

        // Should derive all transitive paths
        assert!(path_relation.contains(&vec![Value::integer(1), Value::integer(2)]));
        assert!(path_relation.contains(&vec![Value::integer(2), Value::integer(3)]));
        assert!(path_relation.contains(&vec![Value::integer(3), Value::integer(4)]));
        assert!(path_relation.contains(&vec![Value::integer(4), Value::integer(5)]));
        assert!(path_relation.contains(&vec![Value::integer(1), Value::integer(3)]));
        assert!(path_relation.contains(&vec![Value::integer(2), Value::integer(4)]));
        assert!(path_relation.contains(&vec![Value::integer(3), Value::integer(5)]));
        assert!(path_relation.contains(&vec![Value::integer(1), Value::integer(4)]));
        assert!(path_relation.contains(&vec![Value::integer(2), Value::integer(5)]));
        assert!(path_relation.contains(&vec![Value::integer(1), Value::integer(5)]));
    }

    #[test]
    fn test_rule_builder_api() {
        let mut db = Database::new();

        db.insert_fact("parent", vec![Value::string("alice"), Value::string("bob")]);
        db.insert_fact(
            "parent",
            vec![Value::string("bob"), Value::string("charlie")],
        );

        // Test the new RuleBuilder API
        let rule = Rule::new()
            .head("grandparent", Tuple::from_variables(vec!["X", "Z"]))
            .body("parent", Tuple::from_variables(vec!["X", "Y"]))
            .body("parent", Tuple::from_variables(vec!["Y", "Z"]))
            .build();

        db.add_rule(rule);
        db.evaluate().unwrap();

        let grandparent_relation = db.get_relation("grandparent").unwrap();
        assert!(
            grandparent_relation.contains(&vec![Value::string("alice"), Value::string("charlie")])
        );
    }

    #[test]
    fn test_tuple_creation_methods_int() {
        // Test Tuple::from_values for integers
        let value_tuple: Tuple = Tuple::from_values(vec![
            Value::integer(1),
            Value::integer(2),
            Value::integer(3),
        ]);
        assert_eq!(value_tuple.len(), 3);
        assert!(value_tuple.terms[0] == Term::integer(1));
        assert!(value_tuple.terms[1] == Term::integer(2));
        assert!(value_tuple.terms[2] == Term::integer(3));

        // Test Tuple::from_variables for integers (variable names are still strings)
        let var_tuple: Tuple = Tuple::from_variables(vec!["X", "Y", "Z"]);
        assert_eq!(var_tuple.len(), 3);
        assert!(matches!(var_tuple.terms[0], Term::Variable(ref v) if v == "X"));
        assert!(matches!(var_tuple.terms[1], Term::Variable(ref v) if v == "Y"));
        assert!(matches!(var_tuple.terms[2], Term::Variable(ref v) if v == "Z"));
    }

    #[test]
    fn test_tuple_creation_methods_str() {
        // Test Tuple::from_values for strings
        let value_tuple: Tuple = Tuple::from_values(vec![
            Value::string("alice"),
            Value::string("bob"),
            Value::string("carol"),
        ]);
        assert_eq!(value_tuple.len(), 3);
        assert!(value_tuple.terms[0] == Term::string("alice"));
        assert!(value_tuple.terms[1] == Term::string("bob"));
        assert!(value_tuple.terms[2] == Term::string("carol"));

        // Test Tuple::from_variables for strings
        let var_tuple: Tuple = Tuple::from_variables(vec!["X", "Y", "Z"]);
        assert_eq!(var_tuple.len(), 3);
        assert!(var_tuple.terms[0] == Term::variable("X"));
        assert!(var_tuple.terms[1] == Term::variable("Y"));
        assert!(var_tuple.terms[2] == Term::variable("Z"));
    }

    #[test]
    fn test_stratification() {
        let mut db = Database::new();

        // Facts
        db.insert_fact("parent", vec![Value::string("alice"), Value::string("bob")]);
        db.insert_fact(
            "parent",
            vec![Value::string("bob"), Value::string("charlie")],
        );
        db.insert_fact("married", vec![Value::string("alice")]);

        // Rules with negation that require stratification:
        // 1. single_parent(X) :- parent(X, Y), not married(X)  (stratum 1)
        // 2. grandparent(X, Z) :- parent(X, Y), parent(Y, Z)  (stratum 0)
        // 3. not_single_grandparent(X, Z) :- grandparent(X, Z), not single_parent(X)  (stratum 2)

        let grandparent_rule = Rule::new()
            .head("grandparent", Tuple::from_variables(vec!["X", "Z"]))
            .body("parent", Tuple::from_variables(vec!["X", "Y"]))
            .body("parent", Tuple::from_variables(vec!["Y", "Z"]))
            .build();

        let single_parent_rule = Rule::new()
            .head("single_parent", Tuple::from_variables(vec!["X"]))
            .body("parent", Tuple::from_variables(vec!["X", "Y"]))
            .body_negative("married", Tuple::from_variables(vec!["X"]))
            .build();

        let not_single_grandparent_rule = Rule::new()
            .head(
                "not_single_grandparent",
                Tuple::from_variables(vec!["X", "Z"]),
            )
            .body("grandparent", Tuple::from_variables(vec!["X", "Z"]))
            .body_negative("single_parent", Tuple::from_variables(vec!["X"]))
            .build();

        db.add_rule(not_single_grandparent_rule);
        db.add_rule(grandparent_rule);
        db.add_rule(single_parent_rule);
        db.evaluate().unwrap();

        let grandparent_relation = db.get_relation("grandparent").unwrap();
        let single_parent_relation = db.get_relation("single_parent").unwrap();
        let not_single_grandparent_relation = db.get_relation("not_single_grandparent").unwrap();

        // Verify grandparent facts (stratum 0)
        assert!(
            grandparent_relation.contains(&vec![Value::string("alice"), Value::string("charlie")])
        );

        // Verify single_parent facts (stratum 1)
        assert!(single_parent_relation.contains(&vec![Value::string("bob")])); // bob has child but not married
        assert!(!single_parent_relation.contains(&vec![Value::string("alice")])); // alice is married

        // Verify not_single_grandparent facts (stratum 2)
        // alice is a grandparent but not a single parent (she's married)
        assert!(not_single_grandparent_relation
            .contains(&vec![Value::string("alice"), Value::string("charlie")]));
        // bob is a grandparent and a single parent, so should not be in this relation
        assert!(!not_single_grandparent_relation
            .contains(&vec![Value::string("bob"), Value::string("charlie")]));
    }

    #[test]
    fn test_negation_cycle_detection_too_strict() {
        // This test checks that you can have cycles bellow the negation.
        // - Rule 0: a(X) :- b(X)
        // - Rule 1: b(X) :- a(X)
        // - Rule 2: c(X) :- not a(X), d(X)

        let mut db = Database::new();

        // Add some facts
        db.insert_facts(
            "b",
            vec![vec![Value::string("x")], vec![Value::string("y")]],
        );
        db.insert_facts("d", vec![vec![Value::string("y")]]);

        // Rule 0: a(X) :- b(X)
        let rule0 = Rule::new()
            .head("a", Tuple::from_variables(vec!["X"]))
            .body("b", Tuple::from_variables(vec!["X"]))
            .build();

        // Rule 1: b(X) :- a(X)
        let rule1 = Rule::new()
            .head("b", Tuple::from_variables(vec!["X"]))
            .body("a", Tuple::from_variables(vec!["X"]))
            .build();

        // Rule 2: c(X) :- not a(X), d(X)
        let rule2 = Rule::new()
            .head("c", Tuple::from_variables(vec!["X"]))
            .body_negative("a", Tuple::from_variables(vec!["X"]))
            .body("d", Tuple::from_variables(vec!["X"]))
            .build();

        // Add rules in an order that might trigger the bug
        db.add_rule(rule2);
        db.add_rule(rule0);
        db.add_rule(rule1);

        // This should NOT fail with CyclicNegation error
        // The cycle a->b->a doesn't involve negation
        // The negation in rule2 is separate from the cycle
        let result = db.evaluate();

        assert!(result == Ok(()));

        let a_relation = db.get_relation("a").unwrap();
        let b_relation = db.get_relation("b").unwrap();
        let c_relation = db.get_relation("c").unwrap();
        let d_relation = db.get_relation("d").unwrap();

        assert_eq!(a_relation.len(), 2);
        assert_eq!(b_relation.len(), 2);
        assert_eq!(c_relation.len(), 1);
        assert_eq!(d_relation.len(), 1);
    }
}
