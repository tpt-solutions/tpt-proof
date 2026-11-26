//! Text syntax for propositions, so that goals can be written as strings.
//!
//! The grammar covers the propositional fragment of the kernel's [`Prop`]:
//!
//! ```text
//! prop   ::= "forall" ident "." prop | imp
//! imp    ::= atom ( "->" imp )?          right-associative
//! atom   ::= ident | "(" prop ")"
//! ident  ::= letter (letter | digit | "_" | apostrophe)*
//! ```
//!
//! `false` is an ordinary identifier to this parser; the kernel gives it its
//! constant meaning. Equalities and predicates need terms, which have no text
//! syntax yet, so they are built with the kernel API.

use tpt_proof_kernel::Prop;

/// Parses a proposition. The error names the byte position and what was expected.
///
/// ```
/// use tpt_proof::prop::parse;
/// use tpt_proof_kernel::Prop;
///
/// let p = parse("(A -> B) -> A -> B").unwrap();
/// assert_eq!(p, Prop::imp(
///     Prop::imp(Prop::atom("A"), Prop::atom("B")),
///     Prop::imp(Prop::atom("A"), Prop::atom("B")),
/// ));
/// ```
pub fn parse(text: &str) -> Result<Prop, String> {
    let tokens = tokenize(text)?;
    let mut parser = Parser { tokens, pos: 0 };
    let prop = parser.prop()?;
    match parser.peek() {
        None => Ok(prop),
        Some((at, token)) => Err(format!(
            "at byte {at}: unexpected {}, expected the end of the proposition",
            token.describe()
        )),
    }
}

/// Builds a [`Prop`] from a string literal, panicking with the parse error if the
/// text is malformed. Use [`prop::parse`](crate::prop::parse) when the text is not
/// a literal.
///
/// ```
/// use tpt_proof::prop;
/// use tpt_proof_kernel::Prop;
///
/// let p = prop!("forall p. p -> p");
/// assert_eq!(p, Prop::forall("p", Prop::imp(Prop::atom("p"), Prop::atom("p"))));
/// ```
#[macro_export]
macro_rules! prop {
    ($text:literal) => {
        match $crate::prop::parse($text) {
            Ok(prop) => prop,
            Err(message) => panic!("invalid proposition {:?}: {}", $text, message),
        }
    };
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Ident(String),
    Arrow,
    Dot,
    Open,
    Close,
}

impl Token {
    fn describe(&self) -> String {
        match self {
            Token::Ident(name) => format!("`{name}`"),
            Token::Arrow => "`->`".to_string(),
            Token::Dot => "`.`".to_string(),
            Token::Open => "`(`".to_string(),
            Token::Close => "`)`".to_string(),
        }
    }
}

fn tokenize(text: &str) -> Result<Vec<(usize, Token)>, String> {
    let mut out = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some(&(at, c)) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else if c == '(' {
            chars.next();
            out.push((at, Token::Open));
        } else if c == ')' {
            chars.next();
            out.push((at, Token::Close));
        } else if c == '.' {
            chars.next();
            out.push((at, Token::Dot));
        } else if c == '-' {
            chars.next();
            match chars.next() {
                Some((_, '>')) => out.push((at, Token::Arrow)),
                _ => return Err(format!("at byte {at}: expected `->`")),
            }
        } else if c.is_alphabetic() || c == '_' {
            let mut name = String::new();
            while let Some(&(_, d)) = chars.peek() {
                if d.is_alphanumeric() || d == '_' || d == '\'' {
                    name.push(d);
                    chars.next();
                } else {
                    break;
                }
            }
            out.push((at, Token::Ident(name)));
        } else {
            return Err(format!("at byte {at}: unexpected character `{c}`"));
        }
    }
    Ok(out)
}

struct Parser {
    tokens: Vec<(usize, Token)>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&(usize, Token)> {
        self.tokens.get(self.pos)
    }

    fn next(&mut self) -> Option<(usize, Token)> {
        let token = self.tokens.get(self.pos).cloned();
        self.pos += 1;
        token
    }

    fn prop(&mut self) -> Result<Prop, String> {
        if let Some((_, Token::Ident(word))) = self.peek() {
            if word == "forall" {
                self.pos += 1;
                let name = match self.next() {
                    Some((_, Token::Ident(name))) if name != "forall" => name,
                    Some((at, token)) => {
                        return Err(format!(
                            "at byte {at}: expected a variable after `forall`, found {}",
                            token.describe()
                        ))
                    }
                    None => {
                        return Err(
                            "expected a variable after `forall`, found the end of the text".into(),
                        )
                    }
                };
                match self.next() {
                    Some((_, Token::Dot)) => {}
                    Some((at, token)) => {
                        return Err(format!(
                            "at byte {at}: expected `.` after the variable, found {}",
                            token.describe()
                        ))
                    }
                    None => {
                        return Err(
                            "expected `.` after the variable, found the end of the text".into()
                        )
                    }
                }
                let body = self.prop()?;
                return Ok(Prop::forall(&name, body));
            }
        }
        let left = self.atom()?;
        if let Some((_, Token::Arrow)) = self.peek() {
            self.pos += 1;
            let right = self.prop()?;
            return Ok(Prop::imp(left, right));
        }
        Ok(left)
    }

    fn atom(&mut self) -> Result<Prop, String> {
        match self.next() {
            Some((_, Token::Ident(name))) if name != "forall" => Ok(Prop::atom(&name)),
            Some((_, Token::Open)) => {
                let inner = self.prop()?;
                match self.next() {
                    Some((_, Token::Close)) => Ok(inner),
                    Some((at, token)) => Err(format!(
                        "at byte {at}: expected `)`, found {}",
                        token.describe()
                    )),
                    None => Err("expected `)`, found the end of the text".into()),
                }
            }
            Some((at, token)) => Err(format!(
                "at byte {at}: expected a proposition, found {}",
                token.describe()
            )),
            None => Err("expected a proposition, found the end of the text".into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::parse;
    use tpt_proof_kernel::Prop;

    #[test]
    fn implication_is_right_associative() {
        let expected = Prop::imp(Prop::atom("A"), Prop::imp(Prop::atom("B"), Prop::atom("C")));
        assert_eq!(parse("A -> B -> C").unwrap(), expected);
        assert_eq!(parse("A -> (B -> C)").unwrap(), expected);
    }

    #[test]
    fn parentheses_group_the_left_side() {
        let expected = Prop::imp(Prop::imp(Prop::atom("A"), Prop::atom("B")), Prop::atom("C"));
        assert_eq!(parse("(A -> B) -> C").unwrap(), expected);
    }

    #[test]
    fn false_is_an_atom_for_the_parser() {
        assert_eq!(
            parse("false -> q").unwrap(),
            Prop::imp(Prop::atom("false"), Prop::atom("q"))
        );
    }

    #[test]
    fn forall_binds_a_propositional_variable() {
        assert_eq!(
            parse("forall p. p -> p").unwrap(),
            Prop::forall("p", Prop::imp(Prop::atom("p"), Prop::atom("p")))
        );
    }

    #[test]
    fn malformed_text_is_reported_with_a_position() {
        assert!(parse("A ->")
            .unwrap_err()
            .contains("expected a proposition"));
        assert!(parse("A B").unwrap_err().contains("at byte 2"));
        assert!(parse("(A -> B").unwrap_err().contains("expected `)`"));
        assert!(parse("A - B").unwrap_err().contains("expected `->`"));
        assert!(parse("A & B").unwrap_err().contains("unexpected character"));
        assert!(parse("forall . A")
            .unwrap_err()
            .contains("expected a variable"));
        assert!(parse("").unwrap_err().contains("expected a proposition"));
    }
}
