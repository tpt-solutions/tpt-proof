//! A restricted expression language for contracts (spec.txt §6).
//!
//! `requires` and `ensures` conditions are written as Rust-like expressions over
//! the parameters, integer and boolean literals, comparisons, `&&`, `||`, `!`,
//! unary `-`, `+`, `-`, and parentheses. A leading `*` on a name is accepted and
//! ignored, so `*result` reads the same as the closure form used by the macros.
//! Anything else is rejected with a message, so an unsupported contract is never
//! silently ignored.

use std::fmt;

use crate::vc::Expr;

/// Why a contract could not be read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecError(pub String);

impl fmt::Display for SpecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for SpecError {}

/// Parses a contract condition. `names` maps each name the condition may use to
/// the expression it stands for, such as a parameter's variable.
pub fn parse(text: &str, names: &[(&str, Expr)]) -> Result<Expr, SpecError> {
    let tokens = tokenize(text)?;
    let mut parser = Parser {
        tokens,
        position: 0,
        names,
    };
    let expr = parser.or()?;
    if parser.position != parser.tokens.len() {
        return Err(SpecError(format!(
            "unexpected `{}` in contract `{text}`",
            parser.tokens[parser.position]
        )));
    }
    Ok(expr)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Int(i64),
    Name(String),
    Op(&'static str),
    Open,
    Close,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Int(n) => write!(f, "{n}"),
            Token::Name(name) => write!(f, "{name}"),
            Token::Op(op) => write!(f, "{op}"),
            Token::Open => write!(f, "("),
            Token::Close => write!(f, ")"),
        }
    }
}

const TWO_CHAR_OPS: [&str; 6] = ["<=", ">=", "==", "!=", "&&", "||"];
const ONE_CHAR_OPS: [&str; 7] = ["<", ">", "+", "-", "!", "*", "&"];

fn tokenize(text: &str) -> Result<Vec<Token>, SpecError> {
    let chars: Vec<char> = text.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c.is_ascii_digit() {
            let start = i;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            let digits: String = chars[start..i].iter().collect();
            let value = digits
                .parse::<i64>()
                .map_err(|_| SpecError(format!("integer `{digits}` is out of range")))?;
            tokens.push(Token::Int(value));
        } else if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            tokens.push(Token::Name(chars[start..i].iter().collect()));
        } else if c == '(' {
            tokens.push(Token::Open);
            i += 1;
        } else if c == ')' {
            tokens.push(Token::Close);
            i += 1;
        } else {
            let pair: String = chars[i..(i + 2).min(chars.len())].iter().collect();
            if let Some(op) = TWO_CHAR_OPS.iter().find(|op| **op == pair) {
                tokens.push(Token::Op(op));
                i += 2;
            } else if let Some(op) = ONE_CHAR_OPS.iter().find(|op| op.starts_with(c)) {
                tokens.push(Token::Op(op));
                i += 1;
            } else {
                return Err(SpecError(format!("unexpected character `{c}` in contract")));
            }
        }
    }
    Ok(tokens)
}

struct Parser<'a> {
    tokens: Vec<Token>,
    position: usize,
    names: &'a [(&'a str, Expr)],
}

impl Parser<'_> {
    fn eat_op(&mut self, wanted: &[&str]) -> Option<&'static str> {
        match self.tokens.get(self.position) {
            Some(Token::Op(op)) if wanted.contains(op) => {
                self.position += 1;
                Some(op)
            }
            _ => None,
        }
    }

    fn or(&mut self) -> Result<Expr, SpecError> {
        let mut left = self.and()?;
        while self.eat_op(&["||"]).is_some() {
            let right = self.and()?;
            left = Expr::Or(vec![left, right]);
        }
        Ok(left)
    }

    fn and(&mut self) -> Result<Expr, SpecError> {
        let mut left = self.comparison()?;
        while self.eat_op(&["&&"]).is_some() {
            let right = self.comparison()?;
            left = Expr::And(vec![left, right]);
        }
        Ok(left)
    }

    fn comparison(&mut self) -> Result<Expr, SpecError> {
        let left = self.sum()?;
        let Some(op) = self.eat_op(&["<", "<=", ">", ">=", "==", "!="]) else {
            return Ok(left);
        };
        let right = self.sum()?;
        let (left, right) = (Box::new(left), Box::new(right));
        Ok(match op {
            "<" => Expr::Lt(left, right),
            "<=" => Expr::Le(left, right),
            ">" => Expr::Lt(right, left),
            ">=" => Expr::Le(right, left),
            "==" => Expr::Eq(left, right),
            _ => Expr::Not(Box::new(Expr::Eq(left, right))),
        })
    }

    fn sum(&mut self) -> Result<Expr, SpecError> {
        let mut left = self.product()?;
        while let Some(op) = self.eat_op(&["+", "-"]) {
            let right = self.product()?;
            left = if op == "+" {
                Expr::Add(Box::new(left), Box::new(right))
            } else {
                Expr::Sub(Box::new(left), Box::new(right))
            };
        }
        Ok(left)
    }

    fn product(&mut self) -> Result<Expr, SpecError> {
        let mut left = self.unary()?;
        while self.eat_op(&["*"]).is_some() {
            let right = self.unary()?;
            left = Expr::Mul(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn unary(&mut self) -> Result<Expr, SpecError> {
        if self.eat_op(&["!"]).is_some() {
            return Ok(Expr::Not(Box::new(self.unary()?)));
        }
        if self.eat_op(&["-"]).is_some() {
            return Ok(Expr::Sub(Box::new(Expr::Int(0)), Box::new(self.unary()?)));
        }
        if self.eat_op(&["*"]).is_some() {
            // Dereference: contract values are read through their references.
            return self.unary();
        }
        self.primary()
    }

    fn primary(&mut self) -> Result<Expr, SpecError> {
        let Some(token) = self.tokens.get(self.position).cloned() else {
            return Err(SpecError("unexpected end of contract".to_string()));
        };
        self.position += 1;
        match token {
            Token::Int(n) => Ok(Expr::Int(n)),
            Token::Name(name) => match name.as_str() {
                "true" => Ok(Expr::Bool(true)),
                "false" => Ok(Expr::Bool(false)),
                _ => self
                    .names
                    .iter()
                    .find(|(known, _)| *known == name)
                    .map(|(_, expr)| expr.clone())
                    .ok_or_else(|| SpecError(format!("unknown name `{name}` in contract"))),
            },
            Token::Open => {
                let inner = self.or()?;
                match self.tokens.get(self.position) {
                    Some(Token::Close) => {
                        self.position += 1;
                        Ok(inner)
                    }
                    _ => Err(SpecError("missing `)` in contract".to_string())),
                }
            }
            other => Err(SpecError(format!("unexpected `{other}` in contract"))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::encode;
    use crate::vc::{Sort, Vc};

    fn var(name: &str) -> Expr {
        Expr::Var(name.to_string())
    }

    fn names() -> Vec<(&'static str, Expr)> {
        vec![("x", var("_1")), ("y", var("_2"))]
    }

    #[test]
    fn comparisons_and_connectives() {
        let parsed = parse("x < 100 && y >= 1", &names()).expect("parses");
        assert_eq!(
            parsed,
            Expr::And(vec![
                Expr::Lt(Box::new(var("_1")), Box::new(Expr::Int(100))),
                Expr::Le(Box::new(Expr::Int(1)), Box::new(var("_2"))),
            ])
        );
    }

    #[test]
    fn addition_binds_tighter_than_comparison() {
        let parsed = parse("x + 1 < y", &names()).expect("parses");
        assert_eq!(
            parsed,
            Expr::Lt(
                Box::new(Expr::Add(Box::new(var("_1")), Box::new(Expr::Int(1)))),
                Box::new(var("_2")),
            )
        );
        assert_eq!(parse("(x + 1) < y", &names()).expect("parses"), parsed);
    }

    #[test]
    fn dereference_is_transparent() {
        assert_eq!(
            parse("*x >= 0", &names()).expect("parses"),
            parse("x >= 0", &names()).expect("parses"),
        );
    }

    #[test]
    fn booleans_and_negation() {
        assert_eq!(parse("true", &[]).expect("parses"), Expr::Bool(true));
        assert_eq!(
            parse("!false", &[]).expect("parses"),
            Expr::Not(Box::new(Expr::Bool(false)))
        );
        assert_eq!(
            parse("-3", &[]).expect("parses"),
            Expr::Sub(Box::new(Expr::Int(0)), Box::new(Expr::Int(3)))
        );
    }

    #[test]
    fn unknown_names_and_bad_syntax_are_rejected() {
        assert!(parse("z > 0", &names()).is_err());
        assert!(parse("x >", &names()).is_err());
        assert!(parse("(x > 0", &names()).is_err());
        assert!(parse("x > 0 )", &names()).is_err());
        assert!(parse("x @ 2", &names()).is_err());
    }

    #[test]
    fn parsed_conditions_are_well_sorted_vcs() {
        let assumption = parse("x < 100", &names()).expect("parses");
        let vc = Vc {
            name: "sorted".to_string(),
            vars: vec![("_1".to_string(), Sort::Int), ("_2".to_string(), Sort::Int)],
            assumptions: vec![assumption],
            goal: parse("x + 1 <= 100", &names()).expect("parses"),
        };
        assert!(encode(&vc).is_ok());
    }
}

#[cfg(test)]
mod multiplication_tests {
    use super::*;

    #[test]
    fn multiplication_binds_tighter_than_addition() {
        let parsed = parse(
            "x + 2 * y > 0",
            &[("x", Expr::Var("_1".into())), ("y", Expr::Var("_2".into()))],
        )
        .expect("parses");
        let product = Expr::Mul(Box::new(Expr::Int(2)), Box::new(Expr::Var("_2".into())));
        assert_eq!(
            parsed,
            Expr::Lt(
                Box::new(Expr::Int(0)),
                Box::new(Expr::Add(
                    Box::new(Expr::Var("_1".into())),
                    Box::new(product)
                )),
            )
        );
    }

    #[test]
    fn deref_still_works_at_the_start_of_an_operand() {
        let names = [("x", Expr::Var("_1".into()))];
        assert_eq!(
            parse("*x * 2 == 4", &names).expect("parses"),
            parse("x * 2 == 4", &names).expect("parses"),
        );
    }
}
