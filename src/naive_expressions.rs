//! Semi-naive implementation of Datalog
//!
//! One step up from the naive implementation. The big idea is to introduce a notion of "stable" and "delta"
//! facts in relations. We know that we have already checked all combinations of stable facts, so we can skip
//! them and new combinations that at least binds to one delta fact.
//!
//! The big changes are in the `find_substitutions` function and the relation struct.

use crate::atom::Atom;
use crate::expression::{self, Expr};
use crate::value::Value;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DatalogError {
    CyclicNegation { rules: HashSet<usize> },
    CyclicAggregation { rules: HashSet<usize> },
    NonStratifiableProgram,
    UnboundVariable { variable: String },
    InvalidClauseInHead(Clause),
    ExpressionEvaluationError(String),
}

impl fmt::Display for DatalogError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DatalogError::CyclicNegation { rules } => {
                write!(f, "Cyclic negation detected: {:?}", rules)
            }
            DatalogError::CyclicAggregation { rules } => {
                write!(f, "Cyclic aggregation detected: {:?}", rules)
            }
            DatalogError::NonStratifiableProgram => write!(f, "Program is not stratifiable"),
            DatalogError::UnboundVariable { variable } => {
                write!(f, "Unbound variable: {}", variable)
            }
            DatalogError::InvalidClauseInHead(clause) => {
                write!(f, "Invalid clause in head: {}", clause)
            }
            DatalogError::ExpressionEvaluationError(e) => {
                write!(f, "Expression evaluation error: {}", e)
            }
        }
    }
}

impl std::error::Error for DatalogError {}

/// A term in a Datalog program - either a value or a variable
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Value(Value),
    Variable(String),
    Aggregation(AggregationOp, String),
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

    pub fn aggregation<S: Into<String>>(op: AggregationOp, var_name: S) -> Self {
        Term::Aggregation(op, var_name.into())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AggregationOp {
    Count,
    Sum,
    Avg,
    Min,
    Max,
}

impl fmt::Display for AggregationOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AggregationOp::Count => write!(f, "count"),
            AggregationOp::Sum => write!(f, "sum"),
            AggregationOp::Avg => write!(f, "avg"),
            AggregationOp::Min => write!(f, "min"),
            AggregationOp::Max => write!(f, "max"),
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
            Term::Aggregation(op, var_name) => {
                write!(f, "{}", op)?;
                write!(f, "(")?;
                write!(f, "?{}", var_name)?;
                write!(f, ")")?;
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Clause {
    Relation(RelationPattern), // p(X, Y)
    Filter(Expr),              // X + Y > 5
    Binding(Binding),          // X = 5
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Clause::Relation(relation) => write!(f, "{}", relation)?,
            Clause::Filter(expr) => write!(f, "{}", expr)?,
            Clause::Binding(binding) => write!(f, "{} = {}", binding.variable, binding.value)?,
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelationPattern {
    pub name: String,
    pub arguments: Vec<Term>,
    pub is_negated: bool,
}

impl RelationPattern {
    pub fn is_aggregated(&self) -> bool {
        self.arguments
            .iter()
            .any(|term| matches!(term, Term::Aggregation(_, _)))
    }
}

impl fmt::Display for RelationPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        write!(f, "(")?;
        for (i, term) in self.arguments.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", term)?;
        }
        write!(f, ")")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Binding {
    pub variable: String,
    pub value: Expr,
}

struct Stratifier {
    visited: Vec<bool>,
    strata_assignments: Vec<usize>,
    strata_counter: usize,
    path: Vec<PathElement>,
    rule_is_aggregated: Vec<bool>,
}

#[derive(Debug)]
struct PathElement {
    from_rule: usize,
    is_negated: bool,
}

impl Stratifier {
    pub fn new(length: usize) -> Self {
        Self {
            visited: vec![false; length],
            rule_is_aggregated: vec![false; length],
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
            self.rule_is_aggregated[i] = rule.is_aggregated();

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
                        rule_deps
                            .get_mut(&i)
                            .unwrap()
                            .push((producer_rule, is_negated));
                    }
                }
            }
        }

        for rule in 0..rules.len() {
            if self.visited[rule] {
                continue;
            }
            let mut current_visited = HashSet::new();
            self.find_strata(rule, &mut current_visited, &rule_deps)?;
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
        rule_deps: &HashMap<usize, Vec<(usize, bool)>>,
    ) -> Result<(), DatalogError> {
        if current_visited.contains(&rule) {
            // We have found a cycle, store the path on the stack
            let mut stratum = 0;
            // Find if any of the rules in the path have a stratum assignment
            // which means that it is a part of a cycle. If so, we need to assign
            // the same stratum to all the rules that is a part of the cycle we just found, effectively
            // joining the cycle into one stratum.
            for path in self.path.iter().rev() {
                if rule == path.from_rule {
                    self.strata_counter += 1;
                    stratum = self.strata_counter;
                    break;
                }
                if self.strata_assignments[path.from_rule] != 0 {
                    stratum = self.strata_assignments[path.from_rule];
                    break;
                }
            }

            // Assign the stratum to all the rules that is a part of the cycle we just found, effectively
            // joining the cycle into one stratum.
            for dep_rule in self.path.iter().rev() {
                if dep_rule.is_negated {
                    return Err(DatalogError::CyclicNegation {
                        rules: current_visited.clone(),
                    });
                }
                if self.rule_is_aggregated[dep_rule.from_rule] {
                    return Err(DatalogError::CyclicAggregation {
                        rules: current_visited.clone(),
                    });
                }
                self.strata_assignments[dep_rule.from_rule] = stratum;
                if rule == dep_rule.from_rule {
                    break;
                }
            }

            // Assign the stratum to the rule itself.
            self.strata_assignments[rule] = stratum;

            return Ok(());
        }
        current_visited.insert(rule);

        // Recursively find strata for all dependencies
        for (dep_rule, rule_is_negated) in rule_deps.get(&rule).unwrap_or(&Vec::new()) {
            self.path.push(PathElement {
                from_rule: rule,
                is_negated: *rule_is_negated,
            });
            if !self.visited[*dep_rule] {
                self.find_strata(*dep_rule, current_visited, rule_deps)?;
            }
            self.path.pop();
        }

        // If the rule has no stratum assignment, assign it a new stratum
        if self.strata_assignments[rule] == 0 {
            self.strata_counter += 1;
            self.strata_assignments[rule] = self.strata_counter;
        }

        Ok(())
    }
}

type StratumID = usize;

#[derive(Debug)]
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

impl expression::VariableContext for Substitution<Value> {
    fn get_variable(&self, variable: &str) -> Option<Value> {
        self.0.get(variable).cloned()
    }
}

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
    pub heads: Vec<Clause>,
    pub body: Vec<Clause>,
}

impl Rule {
    pub fn new() -> RuleBuilder {
        RuleBuilder::new()
    }

    pub fn is_aggregated(&self) -> bool {
        self.heads.iter().any(|clause| match clause {
            Clause::Relation(relation) => relation.is_aggregated(),
            _ => false,
        })
    }

    /// Get all relations that this rule depends on (reads from)
    /// The boolean indicates whether the dependency is positive or negative
    /// true means negative, false means positive
    pub fn dependencies(&self) -> HashMap<String, bool> {
        let mut deps = HashMap::new();
        for clause in &self.body {
            match clause {
                Clause::Relation(relation) => {
                    deps.insert(relation.name.clone(), relation.is_negated);
                }
                _ => {}
            }
        }
        deps
    }

    /// Get all relations that this rule produces (writes to)
    pub fn produces(&self) -> HashSet<String> {
        let mut prods = HashSet::new();
        for clause in &self.heads {
            match clause {
                Clause::Relation(relation) => {
                    prods.insert(relation.name.clone());
                }
                _ => {}
            }
        }
        prods
    }

    /// Check if this rule has any negative dependencies
    pub fn has_negation(&self) -> bool {
        self.body.iter().any(|clause| match clause {
            Clause::Relation(relation) => relation.is_negated,
            _ => false,
        })
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, clause) in self.heads.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", clause)?;
        }
        write!(f, " :- ")?;
        for (i, clause) in self.body.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", clause)?;
        }
        Ok(())
    }
}

/// Builder for creating Datalog rules
pub struct RuleBuilder {
    heads: Vec<Clause>,
    body: Vec<Clause>,
}

impl RuleBuilder {
    pub fn new() -> Self {
        RuleBuilder {
            heads: Vec::new(),
            body: Vec::new(),
        }
    }

    pub fn head<S: Into<String>>(mut self, name: S, terms: Vec<Term>) -> Self {
        self.heads.push(Clause::Relation(RelationPattern {
            name: name.into(),
            arguments: terms,
            is_negated: false,
        }));
        self
    }

    pub fn head_vars<S: Into<String>>(mut self, name: S, terms: Vec<&str>) -> Self {
        self.heads.push(Clause::Relation(RelationPattern {
            name: name.into(),
            arguments: terms.iter().map(|t| Term::variable(*t)).collect(),
            is_negated: false,
        }));
        self
    }

    pub fn body_binding(mut self, binding: Binding) -> Self {
        self.body.push(Clause::Binding(binding));
        self
    }

    pub fn body_expr(mut self, expr: Expr) -> Self {
        self.body.push(Clause::Filter(expr));
        self
    }

    pub fn body_vars<S: Into<String>>(mut self, name: S, terms: Vec<&str>) -> Self {
        self.body.push(Clause::Relation(RelationPattern {
            name: name.into(),
            arguments: terms.iter().map(|t| Term::variable(*t)).collect(),
            is_negated: false,
        }));
        self
    }

    pub fn body_pattern<S: Into<String>>(mut self, name: S, terms: Vec<Term>) -> Self {
        self.body.push(Clause::Relation(RelationPattern {
            name: name.into(),
            arguments: terms,
            is_negated: false,
        }));
        self
    }

    pub fn body_pattern_negated<S: Into<String>>(mut self, name: S, terms: Vec<Term>) -> Self {
        self.body.push(Clause::Relation(RelationPattern {
            name: name.into(),
            arguments: terms,
            is_negated: true,
        }));
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
    fn evaluate_stratum(&mut self, rules: &[Rule]) -> Result<(), DatalogError> {
        loop {
            let mut new_facts = HashMap::new();
            for rule in rules {
                self.apply_rule(rule, &mut new_facts)?;
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
            if !changed {
                return Ok(());
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
            self.evaluate_stratum(&stratum.rules)?;
        }

        Ok(())
    }

    fn apply_rule(
        &mut self,
        rule: &Rule,
        new_facts: &mut HashMap<String, Vec<Vec<Value>>>,
    ) -> Result<(), DatalogError> {
        let substitutions = self.find_substitutions(&rule.body)?;

        for head in &rule.heads {
            match head {
                Clause::Relation(relation) => {
                    if relation.is_aggregated() {
                        let mut aggregated_facts = HashMap::new();
                        for substitution in substitutions.iter() {
                            self.apply_aggregation(
                                &mut aggregated_facts,
                                &relation.arguments,
                                &substitution,
                            )?;
                        }
                        let mut facts = Vec::new();
                        for (mut value, state) in aggregated_facts {
                            for agg_state in state.iter() {
                                let agg_value = agg_state.compute();
                                value.insert(agg_state.index, agg_value);
                            }
                            facts.push(value);
                        }
                        new_facts.insert(relation.name.clone(), facts);
                    } else {
                        let facts = new_facts.entry(relation.name.clone()).or_insert(Vec::new());
                        for substitution in substitutions.iter() {
                            let new_fact =
                                self.apply_substitution(&relation.arguments, &substitution)?;
                            facts.push(new_fact);
                        }
                    }
                }
                _ => {
                    return Err(DatalogError::InvalidClauseInHead(head.clone()));
                }
            }
        }
        Ok(())
    }

    fn find_substitutions(
        &self,
        goals: &[Clause],
    ) -> Result<Vec<Substitution<Value>>, DatalogError> {
        if goals.is_empty() {
            return Ok(vec![Substitution::new()]);
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
        // 2.  X,     𝜟Y, 𝜟Z + Z
        // 3.  X,      Y,     𝜟Z
        // Count: n a.k.a. 3
        //
        // This last one reduces the number of iteration of the outer loop which is good when there are many goals and
        // is the one we want to use.
        //
        // There is some complication in the case of clauses that are not relation patterns. But basically all we need to do is
        // skip them in the outer loop.
        //
        // This can be rewritten as:
        // 1. 𝜟X, X > 3, 𝜟Y + Y, 𝜟Z + Z
        // 2.  X, X > 3,     𝜟Y, 𝜟Z + Z
        // 3.  X, X > 3,      Y,     𝜟Z
        //
        // Note that where we should pick up the computation is always where the single 𝜟 was last time.

        // We use the starting point to avoid re-evaluating the same goal multiple times.
        let mut starting_point = Some(vec![Substitution::new()]);

        let mut start_index = 0;
        let mut deltas_left = true;

        for delta_goal_idx in 0..goals.len() {
            if delta_goal_idx < start_index || !deltas_left {
                continue;
            }
            // Deals with the scenario where the ending clauses are not relation patterns so we do not
            // need to recompute since all facts are already computed.
            deltas_left = false;

            // Use take() to avoid cloning the starting point
            let mut results = starting_point.take().unwrap_or(vec![Substitution::new()]);

            // saturating sub is used to avoid going out of bounds a.k.a. 0 - 1 = 0 instead of panicking
            for goal_idx in start_index..goals.len() {
                match &goals[goal_idx] {
                    Clause::Filter(expr) => {
                        let mut new_results = Vec::new();
                        for substitution in results.drain(..) {
                            let value = expression::eval(expr, &substitution)
                                .map_err(|e| DatalogError::ExpressionEvaluationError(e))?;

                            if value.is_truthy() {
                                new_results.push(substitution);
                            }
                        }
                        results = new_results;
                    }
                    Clause::Binding(Binding { variable, value }) => {
                        let mut new_results = Vec::new();
                        for mut substitution in results.drain(..) {
                            let value = expression::eval(value, &substitution)
                                .map_err(|e| DatalogError::ExpressionEvaluationError(e))?;

                            if let Some(other_value) = substitution.get(variable) {
                                if *other_value == value {
                                    new_results.push(substitution);
                                }
                            } else {
                                substitution.insert(variable.clone(), value);
                                new_results.push(substitution);
                            }
                        }
                        results = new_results;
                    }

                    Clause::Relation(goal_relation) => {
                        if goal_idx == delta_goal_idx {
                            start_index = delta_goal_idx;
                            starting_point = Some(results.clone());
                        } else if goal_idx > delta_goal_idx {
                            deltas_left = true;
                        }
                        if goal_relation.is_negated {
                            // Negative goal, so there can not be ANY matching tuple
                            if let Some(relation) = self.relations.get(&goal_relation.name) {
                                let mut new_results = Vec::new();

                                for substitution in results.drain(..) {
                                    let mut add = true;
                                    if goal_idx == delta_goal_idx {
                                        // Use only delta tuples
                                        for tuple in relation.delta_iter() {
                                            if let Some(_) = self.unify_tuple(
                                                &goal_relation.arguments,
                                                tuple,
                                                &substitution,
                                            ) {
                                                add = false;
                                                break;
                                            }
                                        }
                                    } else if goal_idx < delta_goal_idx {
                                        // Use only stable tuples (not delta)
                                        for tuple in relation.stable_iter() {
                                            if let Some(_) = self.unify_tuple(
                                                &goal_relation.arguments,
                                                tuple,
                                                &substitution,
                                            ) {
                                                add = false;
                                                break;
                                            }
                                        }
                                    } else {
                                        // Use both stable and delta tuples
                                        for tuple in relation.iter() {
                                            if let Some(_) = self.unify_tuple(
                                                &goal_relation.arguments,
                                                tuple,
                                                &substitution,
                                            ) {
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

                            if let Some(relation) = self.relations.get(&goal_relation.name) {
                                for substitution in results.iter() {
                                    if goal_idx == delta_goal_idx {
                                        // Use only delta tuples
                                        for tuple in relation.delta_iter() {
                                            if let Some(new_sub) = self.unify_tuple(
                                                &goal_relation.arguments,
                                                tuple,
                                                substitution,
                                            ) {
                                                new_results.push(new_sub);
                                            }
                                        }
                                    } else if goal_idx < delta_goal_idx {
                                        // Use only stable tuples (not delta)
                                        for tuple in relation.stable_iter() {
                                            if let Some(new_sub) = self.unify_tuple(
                                                &goal_relation.arguments,
                                                tuple,
                                                substitution,
                                            ) {
                                                new_results.push(new_sub);
                                            }
                                        }
                                    } else {
                                        // Use both stable and delta tuples
                                        for tuple in relation.iter() {
                                            if let Some(new_sub) = self.unify_tuple(
                                                &goal_relation.arguments,
                                                tuple,
                                                substitution,
                                            ) {
                                                new_results.push(new_sub);
                                            }
                                        }
                                    }
                                }
                            }
                            results = new_results;
                        }
                    }
                }
            }

            all_results.extend(results);
        }

        Ok(all_results)
    }

    fn unify_tuple(
        &self,
        pattern: &[Term],
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
        head: &[Term],
        substitution: &Substitution<Value>,
    ) -> Result<Vec<Value>, DatalogError> {
        let mut result = Vec::new();

        for term in head.iter() {
            match term {
                Term::Value(v) => result.push(v.clone()),
                Term::Variable(var_name) => {
                    if let Some(value) = substitution.get(var_name) {
                        result.push(value.clone());
                    } else {
                        return Err(DatalogError::UnboundVariable {
                            variable: var_name.clone(),
                        });
                    }
                }
                _ => {
                    panic!(
                        "This branch should not be reached, should be in apply_aggregation: {:?}",
                        term
                    );
                }
            }
        }

        Ok(result)
    }

    fn apply_aggregation(
        &self,
        aggregate_state: &mut HashMap<Vec<Value>, Vec<AggregationState>>,
        head: &[Term],
        substitution: &Substitution<Value>,
    ) -> Result<(), DatalogError> {
        let mut key = Vec::new();
        let mut agg_state = Vec::new();
        for (index, term) in head.iter().enumerate() {
            match term {
                Term::Value(v) => key.push(v.clone()),
                Term::Variable(var_name) => {
                    if let Some(value) = substitution.get(var_name) {
                        key.push(value.clone());
                    } else {
                        return Err(DatalogError::UnboundVariable {
                            variable: var_name.clone(),
                        });
                    }
                }
                Term::Aggregation(op, var_name) => {
                    if let Some(value) = substitution.get(var_name) {
                        agg_state.push(AggregationState {
                            op: op.clone(),
                            state: value.clone(),
                            count: 1,
                            index: index,
                        });
                    } else {
                        return Err(DatalogError::UnboundVariable {
                            variable: var_name.clone(),
                        });
                    }
                }
            }
        }

        let entry = aggregate_state.entry(key).or_insert(Vec::new());

        if entry.is_empty() {
            for state in agg_state {
                entry.push(state);
            }
        } else {
            for (i, state) in agg_state.iter().enumerate() {
                entry[i].combine(state);
            }
        }

        Ok(())
    }
}

struct AggregationState {
    op: AggregationOp,
    state: Value,
    count: u64,
    index: usize,
}

impl AggregationState {
    fn compute(&self) -> Value {
        match self.op {
            AggregationOp::Count => Value::integer(self.count as i64),
            AggregationOp::Sum => self.state.clone(),
            AggregationOp::Avg => match self.state {
                Value::Integer(i) => Value::Float(i as f64 / self.count as f64),
                Value::Float(f) => Value::Float(f / self.count as f64),
                _ => panic!("Cannot compute avg of {:?}", self.state),
            },

            AggregationOp::Min => self.state.clone(),
            AggregationOp::Max => self.state.clone(),
        }
    }
    fn combine(&mut self, other: &AggregationState) {
        match self.op {
            AggregationOp::Count => {
                self.count += other.count;
            }
            AggregationOp::Sum => {
                self.state = Self::sum(&self.state, &other.state);
            }
            AggregationOp::Avg => {
                self.state = Self::sum(&self.state, &other.state);
                self.count += other.count;
            }
            AggregationOp::Min => {
                self.state = Self::min(&self.state, &other.state);
            }
            AggregationOp::Max => {
                self.state = Self::max(&self.state, &other.state);
            }
        }
    }

    fn sum(value: &Value, other: &Value) -> Value {
        match (value, other) {
            (Value::Integer(i), Value::Integer(j)) => Value::Integer(i + j),
            (Value::Float(f), Value::Float(g)) => Value::Float(f + g),
            (Value::Integer(i), Value::Float(f)) => Value::Float(*i as f64 + f),
            (Value::Float(f), Value::Integer(i)) => Value::Float(f + *i as f64),
            _ => panic!("Cannot sum {:?} and {:?}", value, other),
        }
    }

    fn min(value: &Value, other: &Value) -> Value {
        match (value, other) {
            (Value::Integer(i), Value::Integer(j)) => Value::Integer(*i.min(j)),
            (Value::Float(f), Value::Float(g)) => Value::Float(f.min(*g)),
            (Value::Integer(i), Value::Float(f)) => Value::Float((*i as f64).min(*f)),
            (Value::Float(f), Value::Integer(i)) => Value::Float(f.min(*i as f64)),
            _ => panic!("Cannot take min of {:?} and {:?}", value, other),
        }
    }

    fn max(value: &Value, other: &Value) -> Value {
        match (value, other) {
            (Value::Integer(i), Value::Integer(j)) => Value::Integer(*i.max(j)),
            (Value::Float(f), Value::Float(g)) => Value::Float(f.max(*g)),
            (Value::Integer(i), Value::Float(f)) => Value::Float((*i as f64).max(*f)),
            (Value::Float(f), Value::Integer(i)) => Value::Float(f.max(*i as f64)),
            _ => panic!("Cannot take max of {:?} and {:?}", value, other),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::expression::BinaryOp;

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
            .head(
                "grandparent",
                vec![Term::variable("X"), Term::variable("Z")],
            )
            .body_pattern("parent", vec![Term::variable("X"), Term::variable("Y")])
            .body_pattern("parent", vec![Term::variable("Y"), Term::variable("Z")])
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
            .head_vars("path", vec!["X", "Z"])
            .body_vars("edge", vec!["X", "Y"])
            .body_vars("edge", vec!["Y", "Z"])
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
            .head_vars("human", vec!["X"])
            .head_vars("mortal", vec!["X"])
            .body_vars("person", vec!["X"])
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
            .head_vars("single_parent", vec!["X"])
            .body_vars("parent", vec!["X", "Y"])
            .body_pattern_negated("married", vec![Term::variable("X")])
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
            .head_vars("adult", vec!["X", "Age"])
            .body_vars("person", vec!["X", "Age", "B", "A", "F"])
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
            .head_vars("path", vec!["X", "Y"])
            .body_vars("edge", vec!["X", "Y"])
            .build();

        let path_rule2 = Rule::new()
            .head_vars("path", vec!["X", "Z"])
            .body_vars("edge", vec!["X", "Y"])
            .body_vars("path", vec!["Y", "Z"])
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
            .head_vars("grandparent", vec!["X", "Z"])
            .body_vars("parent", vec!["X", "Y"])
            .body_vars("parent", vec!["Y", "Z"])
            .build();

        db.add_rule(rule);
        db.evaluate().unwrap();

        let grandparent_relation = db.get_relation("grandparent").unwrap();
        assert!(
            grandparent_relation.contains(&vec![Value::string("alice"), Value::string("charlie")])
        );
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
            .head_vars("grandparent", vec!["X", "Z"])
            .body_vars("parent", vec!["X", "Y"])
            .body_vars("parent", vec!["Y", "Z"])
            .build();

        let single_parent_rule = Rule::new()
            .head_vars("single_parent", vec!["X"])
            .body_vars("parent", vec!["X", "Y"])
            .body_pattern_negated("married", vec![Term::variable("X")])
            .build();

        let not_single_grandparent_rule = Rule::new()
            .head_vars("not_single_grandparent", vec!["X", "Z"])
            .body_vars("grandparent", vec!["X", "Z"])
            .body_pattern_negated("single_parent", vec![Term::variable("X")])
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
        db.insert_facts(
            "a",
            vec![
                vec![Value::string("x")],
                vec![Value::string("v")],
                vec![Value::string("w")],
            ],
        );
        db.insert_facts(
            "d",
            vec![vec![Value::string("y")], vec![Value::string("v")]],
        );

        // Rule 0: a(X) :- b(X)
        let rule2 = Rule::new()
            .head_vars("a", vec!["X"])
            .body_vars("b", vec!["X"])
            .build();

        // Rule 1: b(X) :- a(X)
        let rule1 = Rule::new()
            .head_vars("b", vec!["X"])
            .body_vars("a", vec!["X"])
            .build();

        // Rule 2: c(X) :- not a(X), d(X)
        let rule0 = Rule::new()
            .head_vars("c", vec!["X"])
            .body_pattern_negated("a", vec![Term::variable("X")])
            .body_vars("d", vec!["X"])
            .build();

        // Add rules in an order that might trigger the bug
        db.add_rule(rule0);
        db.add_rule(rule1);
        db.add_rule(rule2);

        // This should NOT fail with CyclicNegation error
        // The cycle a->b->a doesn't involve negation
        // The negation in rule2 is separate from the cycle
        let result = db.evaluate();

        assert!(result == Ok(()));

        let a_relation = db.get_relation("a").unwrap();
        let b_relation = db.get_relation("b").unwrap();
        let c_relation = db.get_relation("c").unwrap();
        let d_relation = db.get_relation("d").unwrap();

        assert_eq!(a_relation.len(), 4);
        assert_eq!(b_relation.len(), 4);
        assert_eq!(c_relation.len(), 2);
        assert_eq!(d_relation.len(), 2);
    }

    #[test]
    fn test_aggregation() {
        let mut db = Database::new();

        db.insert_facts(
            "a",
            vec![
                vec![Value::integer(1)],
                vec![Value::integer(2)],
                vec![Value::integer(3)],
            ],
        );

        let rule = Rule::new()
            .head("count", vec![Term::aggregation(AggregationOp::Count, "X")])
            .body_vars("a", vec!["X"])
            .build();

        let rule2 = Rule::new()
            .head("sum", vec![Term::aggregation(AggregationOp::Sum, "X")])
            .body_vars("a", vec!["X"])
            .build();

        let rule3 = Rule::new()
            .head("avg", vec![Term::aggregation(AggregationOp::Avg, "X")])
            .body_vars("a", vec!["X"])
            .build();

        let rule4 = Rule::new()
            .head("min", vec![Term::aggregation(AggregationOp::Min, "X")])
            .body_vars("a", vec!["X"])
            .build();

        let rule5 = Rule::new()
            .head("max", vec![Term::aggregation(AggregationOp::Max, "X")])
            .body_vars("a", vec!["X"])
            .build();

        db.add_rule(rule);
        db.add_rule(rule2);
        db.add_rule(rule3);
        db.add_rule(rule4);
        db.add_rule(rule5);
        db.evaluate().unwrap();

        let count_relation = db.get_relation("count").unwrap();
        assert_eq!(count_relation.len(), 1);
        assert_eq!(
            count_relation.iter().next().unwrap(),
            &vec![Value::integer(3)]
        );

        let sum_relation = db.get_relation("sum").unwrap();
        assert_eq!(sum_relation.len(), 1);
        assert_eq!(
            sum_relation.iter().next().unwrap(),
            &vec![Value::integer(6)]
        );

        let avg_relation = db.get_relation("avg").unwrap();
        assert_eq!(avg_relation.len(), 1);

        let min_relation = db.get_relation("min").unwrap();
        assert_eq!(min_relation.len(), 1);
        assert_eq!(
            min_relation.iter().next().unwrap(),
            &vec![Value::integer(1)]
        );

        let max_relation = db.get_relation("max").unwrap();
        assert_eq!(max_relation.len(), 1);
        assert_eq!(
            max_relation.iter().next().unwrap(),
            &vec![Value::integer(3)]
        );
    }

    #[test]
    fn test_aggregation_cycle() {
        let mut db = Database::new();

        db.insert_facts(
            "a",
            vec![
                vec![Value::integer(1)],
                vec![Value::integer(2)],
                vec![Value::integer(4)],
            ],
        );

        let rule = Rule::new()
            .head("a", vec![Term::aggregation(AggregationOp::Count, "X")])
            .body_vars("a", vec!["X"])
            .build();

        db.add_rule(rule);

        let result = db.evaluate();
        assert!(result.is_err());
        assert!(matches!(
            result,
            Err(DatalogError::CyclicAggregation { rules: _ })
        ));
    }

    #[test]
    fn test_binding() {
        let mut db = Database::new();
        db.insert_facts(
            "a",
            vec![
                vec![Value::integer(1)],
                vec![Value::integer(2)],
                vec![Value::integer(3)],
            ],
        );

        let rule = Rule::new()
            .head("b", vec![Term::variable("Y")])
            .body_vars("a", vec!["X"])
            .body_binding(Binding {
                variable: "Y".to_string(),
                value: Expr::binary(BinaryOp::Add, Expr::variable("X"), Expr::variable("X")),
            })
            .build();

        db.add_rule(rule);
        db.evaluate().unwrap();

        let b_relation = db.get_relation("b").unwrap();
        assert_eq!(b_relation.len(), 3);
        assert!(b_relation.contains(&vec![Value::integer(2)]));
        assert!(b_relation.contains(&vec![Value::integer(4)]));
        assert!(b_relation.contains(&vec![Value::integer(6)]));
    }

    #[test]
    fn test_expression() {
        let mut db = Database::new();
        db.insert_facts(
            "a",
            vec![
                vec![Value::integer(1)],
                vec![Value::integer(2)],
                vec![Value::integer(3)],
            ],
        );

        let rule = Rule::new()
            .head("b", vec![Term::variable("X")])
            .body_vars("a", vec!["X"])
            .body_expr(Expr::binary(
                BinaryOp::Ge,
                Expr::variable("X"),
                Expr::int(2),
            ))
            .build();

        db.add_rule(rule);
        db.evaluate().unwrap();

        let b_relation = db.get_relation("b").unwrap();
        assert_eq!(b_relation.len(), 2);
        assert!(b_relation.contains(&vec![Value::integer(2)]));
        assert!(b_relation.contains(&vec![Value::integer(3)]));
    }
}
