//! Expressions IR for the query language. These
//! are not exposed to the user directly so we have a lot
//! of freedom to change the representation.
//!
//! We will start with a simple tree representation but in the
//! future I would like to create a bytecode instead.
//! Here is a good guide: https://craftinginterpreters.com/contents.html
//! we only need the expression part of the book so it should be much
//! simpler then what they are doing.

use std::collections::HashMap;
use std::fmt;

use crate::atom::Atom;
use crate::value::Value;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Literal(Value),
    Variable(String),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    Unary(UnaryOp, Box<Expr>),
}

impl Expr {
    pub fn iter_children(&self) -> impl Iterator<Item = &Box<Expr>> {
        match self {
            Expr::Binary(_, left, right) => vec![left, right].into_iter(),
            Expr::Unary(_, expr) => vec![expr].into_iter(),
            _ => vec![].into_iter(),
        }
    }
    pub fn eval(&self, variables: &impl VariableContext) -> Result<Value, String> {
        eval(self, variables)
    }

    pub fn variable<T: Into<String>>(name: T) -> Self {
        Self::Variable(name.into())
    }

    pub fn atom(atom: Atom) -> Self {
        Self::Literal(Value::Atom(atom))
    }

    pub fn string<T: Into<String>>(string: T) -> Self {
        Self::Literal(Value::String(string.into()))
    }

    pub fn boolean(boolean: bool) -> Self {
        Self::Literal(Value::Boolean(boolean))
    }

    pub fn float(float: f64) -> Self {
        Self::Literal(Value::Float(float))
    }

    pub fn int(int: i64) -> Self {
        Self::Literal(Value::Integer(int))
    }

    pub fn binary(op: BinaryOp, left: Self, right: Self) -> Self {
        Self::Binary(op, Box::new(left), Box::new(right))
    }

    pub fn unary(op: UnaryOp, expr: Self) -> Self {
        Self::Unary(op, Box::new(expr))
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Literal(literal) => write!(f, "{}", literal)?,
            Expr::Variable(variable) => write!(f, "{}", variable)?,
            Expr::Binary(op, left, right) => write!(f, "{} {} {}", left, op, right)?,
            Expr::Unary(op, expr) => write!(f, "{} {}", op, expr)?,
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    And,
    Or,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinaryOp::And => write!(f, "and")?,
            BinaryOp::Or => write!(f, "or")?,
            BinaryOp::Eq => write!(f, "==")?,
            BinaryOp::Ne => write!(f, "!=")?,
            BinaryOp::Lt => write!(f, "<")?,
            BinaryOp::Le => write!(f, "<=")?,
            BinaryOp::Gt => write!(f, ">")?,
            BinaryOp::Ge => write!(f, ">=")?,
            BinaryOp::Add => write!(f, "+")?,
            BinaryOp::Sub => write!(f, "-")?,
            BinaryOp::Mul => write!(f, "*")?,
            BinaryOp::Div => write!(f, "/")?,
            BinaryOp::Mod => write!(f, "%")?,
            BinaryOp::Pow => write!(f, "**")?,
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Not,
    Negate,
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnaryOp::Not => write!(f, "not")?,
            UnaryOp::Negate => write!(f, "-")?,
        }
        Ok(())
    }
}

/// Optimize an expression by replacing constants and variables with their values.
///
/// It will also try to simplify expressions such as `1 + 1` to `2` by running
/// the expression through the evaluator on each sub-expression.
///
pub fn optimize(expr: Expr, variables: &HashMap<String, Value>) -> Expr {
    let (expr, _) = optimize_impl(expr, variables);
    expr
}

// Optimize an expression by replacing variables and constants and then try to evaluate it.
// We return a boolean indicating if the expression can be evaluated so we do not reevaluate
// unneeded sub-expressions.
fn optimize_impl(expr: Expr, variables: &impl VariableContext) -> (Expr, bool) {
    match expr {
        Expr::Binary(op, left, right) => {
            let (left, left_can_be_evaluated) = optimize_impl(*left, variables);
            let (right, right_can_be_evaluated) = optimize_impl(*right, variables);
            let new_expr = Expr::Binary(op, Box::new(left), Box::new(right));
            if left_can_be_evaluated && right_can_be_evaluated {
                eval(&new_expr, variables)
                    .map(|v| (Expr::Literal(v), true))
                    .unwrap_or((new_expr, false))
            } else {
                (new_expr, false)
            }
        }
        Expr::Variable(variable) => {
            if let Some(value) = variables.get_variable(&variable) {
                (Expr::Literal(value), true)
            } else {
                (Expr::Variable(variable), false)
            }
        }
        Expr::Unary(op, expr) => {
            let (expr, expr_can_be_evaluated) = optimize_impl(*expr, variables);

            let new_expr = Expr::Unary(op, Box::new(expr));
            if expr_can_be_evaluated {
                eval(&new_expr, variables)
                    .map(|v| (Expr::Literal(v), true))
                    .unwrap_or((new_expr, false))
            } else {
                (new_expr, false)
            }
        }
        _ => (expr, true),
    }
}

/// Execute an expression and return the result.
///
/// This is a simple interpreter that evaluates the expression
/// and returns the result. Will produce an error if the expression
/// is invalid.
///
pub fn eval(expr: &Expr, variables: &impl VariableContext) -> Result<Value, String> {
    match expr {
        Expr::Literal(literal) => Ok(literal.clone()),
        Expr::Variable(variable) => variables
            .get_variable(&variable)
            .ok_or_else(|| format!("Variable not found: {}", variable)),
        Expr::Binary(op, left, right) => {
            let left_val = eval(left, variables)?;
            let right_val = eval(right, variables)?;
            match op {
                BinaryOp::And => match (left_val, right_val) {
                    (Value::Boolean(left), Value::Boolean(right)) => {
                        Ok(Value::Boolean(left && right))
                    }
                    _ => Err("And operator requires boolean operands".to_string()),
                },
                BinaryOp::Or => match (left_val, right_val) {
                    (Value::Boolean(left), Value::Boolean(right)) => {
                        Ok(Value::Boolean(left || right))
                    }
                    _ => Err("Or operator requires boolean operands".to_string()),
                },
                BinaryOp::Eq => Ok(Value::Boolean(left_val == right_val)),
                BinaryOp::Ne => Ok(Value::Boolean(left_val != right_val)),
                BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                    match (left_val, right_val) {
                        (Value::Integer(left), Value::Integer(right)) => match op {
                            BinaryOp::Lt => Ok(Value::Boolean(left < right)),
                            BinaryOp::Le => Ok(Value::Boolean(left <= right)),
                            BinaryOp::Gt => Ok(Value::Boolean(left > right)),
                            BinaryOp::Ge => Ok(Value::Boolean(left >= right)),
                            _ => unreachable!(),
                        },
                        (Value::Float(left), Value::Float(right)) => match op {
                            BinaryOp::Lt => Ok(Value::Boolean(left < right)),
                            BinaryOp::Le => Ok(Value::Boolean(left <= right)),
                            BinaryOp::Gt => Ok(Value::Boolean(left > right)),
                            BinaryOp::Ge => Ok(Value::Boolean(left >= right)),
                            _ => unreachable!(),
                        },
                        (Value::Integer(left), Value::Float(right)) => match op {
                            BinaryOp::Lt => Ok(Value::Boolean((left as f64) < right)),
                            BinaryOp::Le => Ok(Value::Boolean((left as f64) <= right)),
                            BinaryOp::Gt => Ok(Value::Boolean((left as f64) > right)),
                            BinaryOp::Ge => Ok(Value::Boolean((left as f64) >= right)),
                            _ => unreachable!(),
                        },
                        (Value::Float(left), Value::Integer(right)) => match op {
                            BinaryOp::Lt => Ok(Value::Boolean(left < right as f64)),
                            BinaryOp::Le => Ok(Value::Boolean(left <= right as f64)),
                            BinaryOp::Gt => Ok(Value::Boolean(left > right as f64)),
                            BinaryOp::Ge => Ok(Value::Boolean(left >= right as f64)),
                            _ => unreachable!(),
                        },
                        _ => Err("Comparison operators require numeric operands".to_string()),
                    }
                }
                BinaryOp::Add
                | BinaryOp::Sub
                | BinaryOp::Mul
                | BinaryOp::Div
                | BinaryOp::Mod
                | BinaryOp::Pow => match (left_val, right_val) {
                    (Value::Integer(left), Value::Integer(right)) => match op {
                        BinaryOp::Add => Ok(Value::Integer(left + right)),
                        BinaryOp::Sub => Ok(Value::Integer(left - right)),
                        BinaryOp::Mul => Ok(Value::Integer(left * right)),
                        BinaryOp::Mod => Ok(Value::Integer(left % right)),
                        BinaryOp::Pow => Ok(Value::Integer(left.pow(right as u32))),
                        BinaryOp::Div => {
                            if right == 0 {
                                Err("Division by zero".to_string())
                            } else {
                                Ok(Value::Integer(left / right))
                            }
                        }
                        _ => unreachable!(),
                    },
                    (Value::Float(left), Value::Float(right)) => match op {
                        BinaryOp::Add => Ok(Value::Float(left + right)),
                        BinaryOp::Sub => Ok(Value::Float(left - right)),
                        BinaryOp::Mul => Ok(Value::Float(left * right)),
                        BinaryOp::Mod => Ok(Value::Float(left % right)),
                        BinaryOp::Pow => Ok(Value::Float(left.powf(right as f64))),
                        BinaryOp::Div => {
                            if right == 0.0 {
                                Err("Division by zero".to_string())
                            } else {
                                Ok(Value::Float(left / right))
                            }
                        }
                        _ => unreachable!(),
                    },
                    (Value::Integer(left), Value::Float(right)) => match op {
                        BinaryOp::Add => Ok(Value::Float(left as f64 + right)),
                        BinaryOp::Sub => Ok(Value::Float(left as f64 - right)),
                        BinaryOp::Mul => Ok(Value::Float(left as f64 * right)),
                        BinaryOp::Mod => Ok(Value::Float((left as f64) % right)),
                        BinaryOp::Pow => Ok(Value::Float((left as f64).powf(right))),
                        BinaryOp::Div => {
                            if right == 0.0 {
                                Err("Division by zero".to_string())
                            } else {
                                Ok(Value::Float(left as f64 / right))
                            }
                        }
                        _ => unreachable!(),
                    },
                    (Value::Float(left), Value::Integer(right)) => match op {
                        BinaryOp::Add => Ok(Value::Float(left + right as f64)),
                        BinaryOp::Sub => Ok(Value::Float(left - right as f64)),
                        BinaryOp::Mul => Ok(Value::Float(left * right as f64)),
                        BinaryOp::Mod => Ok(Value::Float(left % right as f64)),
                        BinaryOp::Pow => Ok(Value::Float(left.powf(right as f64))),
                        BinaryOp::Div => {
                            if right == 0 {
                                Err("Division by zero".to_string())
                            } else {
                                Ok(Value::Float(left / right as f64))
                            }
                        }
                        _ => unreachable!(),
                    },
                    _ => Err("Arithmetic operators require numeric operands".to_string()),
                },
            }
        }
        Expr::Unary(op, expr) => {
            let val = eval(expr, variables)?;
            match op {
                UnaryOp::Not => match val {
                    Value::Boolean(b) => Ok(Value::Boolean(!b)),
                    _ => Err("Not operator requires boolean operand".to_string()),
                },
                UnaryOp::Negate => match val {
                    Value::Integer(i) => Ok(Value::Integer(-i)),
                    Value::Float(f) => Ok(Value::Float(-f)),
                    _ => Err("Negate operator requires numeric operand".to_string()),
                },
            }
        }
    }
}

/// Extract common variables between two expressions.
///
/// This is a simple function that extracts the variables that are common
/// to both expressions.
///
pub fn extract_common_variables(left: &Expr, right: &Expr) -> Vec<String> {
    let left_variables = extract_variables(left);
    let right_variables = extract_variables(right);
    left_variables
        .iter()
        .filter(|v| right_variables.contains(v))
        .cloned()
        .collect()
}

/// Extract all variables from an expression.
///
/// This is a simple function that extracts all the variables from an expression.
///
pub fn extract_variables(expr: &Expr) -> Vec<String> {
    let mut worklist = vec![expr];
    let mut variables = vec![];
    while let Some(expr) = worklist.pop() {
        match expr {
            Expr::Variable(variable) => variables.push(variable.clone()),
            _ => worklist.extend(expr.iter_children().map(|e| e.as_ref())),
        }
    }
    variables
}

pub trait VariableContext {
    fn get_variable(&self, variable: &str) -> Option<Value>;
}

pub trait ConstantContext {
    fn get_constant(&self, constant: &str) -> Option<Value>;
}

impl VariableContext for HashMap<String, Value> {
    fn get_variable(&self, variable: &str) -> Option<Value> {
        self.get(variable).cloned()
    }
}

impl ConstantContext for HashMap<String, Value> {
    fn get_constant(&self, constant: &str) -> Option<Value> {
        self.get(constant).cloned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal() {
        let expr = Expr::Literal(Value::Boolean(true));
        let variables = HashMap::new();
        assert_eq!(eval(&expr, &variables), Ok(Value::Boolean(true)));
    }

    #[test]
    fn test_variable() {
        let mut env = HashMap::new();
        env.insert("x".to_string(), Value::Integer(42));
        let expr = Expr::Variable("x".to_string());
        assert_eq!(eval(&expr, &env), Ok(Value::Integer(42)));
    }

    #[test]
    fn test_variable_not_found() {
        let env = HashMap::new();
        let expr = Expr::Variable("x".to_string());
        assert!(eval(&expr, &env).is_err());
    }

    #[test]
    fn test_boolean_ops() {
        let env = HashMap::new();
        let cases = vec![
            (
                Expr::Binary(
                    BinaryOp::And,
                    Box::new(Expr::Literal(Value::Boolean(true))),
                    Box::new(Expr::Literal(Value::Boolean(true))),
                ),
                Ok(Value::Boolean(true)),
            ),
            (
                Expr::Binary(
                    BinaryOp::And,
                    Box::new(Expr::Literal(Value::Boolean(true))),
                    Box::new(Expr::Literal(Value::Boolean(false))),
                ),
                Ok(Value::Boolean(false)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Or,
                    Box::new(Expr::Literal(Value::Boolean(true))),
                    Box::new(Expr::Literal(Value::Boolean(false))),
                ),
                Ok(Value::Boolean(true)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Or,
                    Box::new(Expr::Literal(Value::Boolean(false))),
                    Box::new(Expr::Literal(Value::Boolean(false))),
                ),
                Ok(Value::Boolean(false)),
            ),
            (
                Expr::Unary(UnaryOp::Not, Box::new(Expr::Literal(Value::Boolean(true)))),
                Ok(Value::Boolean(false)),
            ),
            (
                Expr::Unary(UnaryOp::Not, Box::new(Expr::Literal(Value::Boolean(false)))),
                Ok(Value::Boolean(true)),
            ),
        ];

        for (expr, expected) in cases {
            assert_eq!(eval(&expr, &env), expected);
        }
    }

    #[test]
    fn test_numeric_ops() {
        let env = HashMap::new();
        let cases = vec![
            (
                Expr::Binary(
                    BinaryOp::Add,
                    Box::new(Expr::Literal(Value::Integer(2))),
                    Box::new(Expr::Literal(Value::Integer(3))),
                ),
                Ok(Value::Integer(5)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Sub,
                    Box::new(Expr::Literal(Value::Integer(5))),
                    Box::new(Expr::Literal(Value::Integer(3))),
                ),
                Ok(Value::Integer(2)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Mul,
                    Box::new(Expr::Literal(Value::Integer(4))),
                    Box::new(Expr::Literal(Value::Integer(3))),
                ),
                Ok(Value::Integer(12)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Div,
                    Box::new(Expr::Literal(Value::Integer(6))),
                    Box::new(Expr::Literal(Value::Integer(2))),
                ),
                Ok(Value::Integer(3)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Div,
                    Box::new(Expr::Literal(Value::Integer(6))),
                    Box::new(Expr::Literal(Value::Integer(0))),
                ),
                Err("Division by zero".to_string()),
            ),
        ];

        for (expr, expected) in cases {
            assert_eq!(eval(&expr, &env), expected);
        }
    }

    #[test]
    fn test_mixed_numeric_ops() {
        let env = HashMap::new();
        let cases = vec![
            (
                Expr::Binary(
                    BinaryOp::Add,
                    Box::new(Expr::Literal(Value::Integer(2))),
                    Box::new(Expr::Literal(Value::Float(3.0))),
                ),
                Ok(Value::Float(5.0)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Sub,
                    Box::new(Expr::Literal(Value::Float(5.0))),
                    Box::new(Expr::Literal(Value::Integer(3))),
                ),
                Ok(Value::Float(2.0)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Mul,
                    Box::new(Expr::Literal(Value::Integer(4))),
                    Box::new(Expr::Literal(Value::Float(3.0))),
                ),
                Ok(Value::Float(12.0)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Div,
                    Box::new(Expr::Literal(Value::Integer(6))),
                    Box::new(Expr::Literal(Value::Float(2.0))),
                ),
                Ok(Value::Float(3.0)),
            ),
        ];

        for (expr, expected) in cases {
            assert_eq!(eval(&expr, &env), expected);
        }
    }

    #[test]
    fn test_comparison_ops() {
        let env = HashMap::new();
        let cases = vec![
            (
                Expr::Binary(
                    BinaryOp::Lt,
                    Box::new(Expr::Literal(Value::Integer(2))),
                    Box::new(Expr::Literal(Value::Integer(3))),
                ),
                Ok(Value::Boolean(true)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Le,
                    Box::new(Expr::Literal(Value::Integer(3))),
                    Box::new(Expr::Literal(Value::Integer(3))),
                ),
                Ok(Value::Boolean(true)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Gt,
                    Box::new(Expr::Literal(Value::Integer(4))),
                    Box::new(Expr::Literal(Value::Integer(3))),
                ),
                Ok(Value::Boolean(true)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Ge,
                    Box::new(Expr::Literal(Value::Integer(3))),
                    Box::new(Expr::Literal(Value::Integer(3))),
                ),
                Ok(Value::Boolean(true)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Eq,
                    Box::new(Expr::Literal(Value::Integer(3))),
                    Box::new(Expr::Literal(Value::Integer(3))),
                ),
                Ok(Value::Boolean(true)),
            ),
            (
                Expr::Binary(
                    BinaryOp::Ne,
                    Box::new(Expr::Literal(Value::Integer(3))),
                    Box::new(Expr::Literal(Value::Integer(4))),
                ),
                Ok(Value::Boolean(true)),
            ),
        ];

        for (expr, expected) in cases {
            assert_eq!(eval(&expr, &env), expected);
        }
    }

    #[test]
    fn test_type_errors() {
        let env = HashMap::new();
        let cases = vec![
            (
                Expr::Binary(
                    BinaryOp::And,
                    Box::new(Expr::Literal(Value::Integer(1))),
                    Box::new(Expr::Literal(Value::Boolean(true))),
                ),
                Err("And operator requires boolean operands".to_string()),
            ),
            (
                Expr::Binary(
                    BinaryOp::Or,
                    Box::new(Expr::Literal(Value::Boolean(true))),
                    Box::new(Expr::Literal(Value::Integer(1))),
                ),
                Err("Or operator requires boolean operands".to_string()),
            ),
            (
                Expr::Binary(
                    BinaryOp::Add,
                    Box::new(Expr::Literal(Value::Boolean(true))),
                    Box::new(Expr::Literal(Value::Integer(1))),
                ),
                Err("Arithmetic operators require numeric operands".to_string()),
            ),
            (
                Expr::Binary(
                    BinaryOp::Lt,
                    Box::new(Expr::Literal(Value::Boolean(true))),
                    Box::new(Expr::Literal(Value::Integer(1))),
                ),
                Err("Comparison operators require numeric operands".to_string()),
            ),
            (
                Expr::Unary(UnaryOp::Not, Box::new(Expr::Literal(Value::Integer(1)))),
                Err("Not operator requires boolean operand".to_string()),
            ),
        ];

        for (expr, expected) in cases {
            assert_eq!(eval(&expr, &env), expected);
        }
    }

    #[test]
    fn test_optimize() {
        let expr = Expr::binary(
            BinaryOp::Add,
            Expr::Literal(Value::Integer(1)),
            Expr::Literal(Value::Integer(2)),
        );
        let variables = HashMap::new();
        let optimized = optimize(expr, &variables);
        assert_eq!(optimized, Expr::Literal(Value::Integer(3)));
    }

    #[test]
    fn test_optimize_with_variables() {
        let expr = Expr::binary(BinaryOp::Add, Expr::variable("x"), Expr::variable("y"));
        let mut variables = HashMap::new();
        variables.insert("x".to_string(), Value::Integer(1));
        variables.insert("y".to_string(), Value::Integer(2));
        let optimized = optimize(expr, &variables);
        assert_eq!(optimized, Expr::Literal(Value::Integer(3)));
    }

    #[test]
    fn test_optimize_with_unary() {
        let expr = Expr::unary(UnaryOp::Not, Expr::Literal(Value::Boolean(true)));
        let variables = HashMap::new();
        let optimized = optimize(expr, &variables);
        assert_eq!(optimized, Expr::Literal(Value::Boolean(false)));
    }

    #[test]
    fn test_optimize_partially() {
        let expr = Expr::binary(
            BinaryOp::Add,
            Expr::binary(
                BinaryOp::Mul,
                Expr::Literal(Value::Integer(2)),
                Expr::Literal(Value::Integer(3)),
            ),
            Expr::variable("x"),
        );
        let variables = HashMap::new();
        let optimized = optimize(expr, &variables);
        assert_eq!(
            optimized,
            Expr::binary(
                BinaryOp::Add,
                Expr::Literal(Value::Integer(6)),
                Expr::variable("x")
            )
        );
    }
}
