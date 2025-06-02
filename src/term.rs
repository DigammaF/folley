use std::{collections::HashMap, fmt::{self, Display}};

use crate::{formula::Formula, scope::Scope, Domain, Identifier};

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum Term {
    #[default] True, False,
    Variable(Identifier), Value(Domain),
    Function(Identifier, Vec<Term>)
}

impl Into<Formula> for Term {
    fn into(self) -> Formula { Formula::Term(self) }
}

impl Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::True => write!(f, "⊤"),
            Term::False => write!(f, "⊥"),
            Term::Variable(id) => write!(f, "${}", id),
            Term::Value(id) => write!(f, "#{}", id),
            Term::Function(id, args) => {
                write!(f, "f{}(", id)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Term {
    pub fn from_parse(scope: &Scope, source: &str) -> Result<Term, String> {
        let tokens = tokenize(source);
        return build_term(scope, tokens);
    }

    pub fn bound(&self, valuation: &HashMap<Identifier, Term>) -> Term {
        match self {
            Term::True|Term::False|Term::Value(_) => self.clone(),
            Term::Variable(variable_identifier)
                => valuation.get(variable_identifier).map_or_else(
                    || self.clone(), |term| term.clone()
                ),
            Term::Function(identifier, terms)
                => Term::Function(*identifier, terms.iter().map(|term| term.bound(valuation)).collect())
        }
    }

    pub fn evaluate(&self, scope: &Scope) -> Option<Term> {
        match self {
            Term::True|Term::False|Term::Value(_) => Some(self.clone()),
            Term::Variable(identifier) => {
                if let Some(value) = scope.get_value(identifier) {
                    Some(Term::Value(value))
                } else { None }
            },
            Term::Function(identifier, arguments) => {
                let mut argument_values: Vec<Term> = Vec::new();

                for argument in arguments.iter() {
                    if let Some(value) = argument.evaluate(scope) {
                        argument_values.push(value);
                    } else { return None }
                }

                let function = scope.get_function(identifier);
                if function.arity() != arguments.len() {
                    panic!(
                        "Function {} expects {} arguments, {} given",
                        identifier, function.arity(), arguments.len()
                    );
                }
                return Some(function.apply(argument_values));
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Token { Chars(String), OpenP, CloseP }

fn tokenize(source: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = source.chars().peekable();
    let mut buffer = String::new();

    while let Some(&c) = chars.peek() {
        match c {
            '(' => {
                if !buffer.is_empty() {
                    tokens.push(Token::Chars(buffer.clone()));
                    buffer.clear();
                }
                tokens.push(Token::OpenP);
                chars.next();
            }
            ')' => {
                if !buffer.is_empty() {
                    tokens.push(Token::Chars(buffer.clone()));
                    buffer.clear();
                }
                tokens.push(Token::CloseP);
                chars.next();
            }
            c if c.is_whitespace() || c == ',' => {
                if !buffer.is_empty() {
                    tokens.push(Token::Chars(buffer.clone()));
                    buffer.clear();
                }
                chars.next();
            }
            _ => {
                buffer.push(c);
                chars.next();
            }
        }
    }
    
    if !buffer.is_empty() {
        tokens.push(Token::Chars(buffer));
    }

    tokens
}

fn build_term(scope: &Scope, tokens: Vec<Token>) -> Result<Term, String> {
    let mut argument_stack: Vec<Vec<Term>> = vec![Vec::new()];
    let mut func_stack: Vec<Identifier> = vec![];
    let mut depth: usize = 0;

    let mut tokens = tokens.into_iter().peekable();

    while let Some(token) = tokens.next() {
        match token {
            Token::Chars(text) => {
                if text == "T" {
                    argument_stack.last_mut().expect("No ongoing context to put T into").push(Term::True);
                } else if text == "F" {
                    argument_stack.last_mut().expect("No ongoing context to put F into").push(Term::False);
                } else {
                    if let Some(identifier) = scope.get_identifier(&text) {
                        if scope.is_variable(&identifier) {
                            argument_stack.last_mut()
                                .expect(&format!("No ongoing context to put {identifier} into"))
                                .push(Term::Variable(identifier));
                        }
                        else if scope.is_function(&identifier) { func_stack.push(identifier); argument_stack.push(Vec::new()); }
                        else if scope.is_predicate(&identifier) { return Err(format!("Predicate ({identifier}) not allowed, expected Term")); }
                        else { return Err(format!("unknown identifier type: {identifier}")); }
                    } else if let Ok(value) = text.parse::<Domain>() {
                        argument_stack.last_mut()
                            .expect(&format!("No ongoing context to put {value} into"))
                            .push(Term::Value(value));
                    } else { return Err(format!("{text} could not be understood")); }
                }
            }
            Token::OpenP => {
                depth += 1;

                if depth != func_stack.len() || !argument_stack.last().expect("No function mentionned before '('").is_empty() {
                    return Err("Unexpected '('".to_string());
                }
            }
            Token::CloseP => {
                let func_id = func_stack.pop().expect("Unexpected ')': no function mentionned");
                let arguments = argument_stack.pop().expect(&format!("No argument context found for {func_id}"));
                depth -= 1;

                if depth != func_stack.len() { return Err("Unexpected ')'".to_string()); }

                argument_stack.last_mut().unwrap().push(Term::Function(func_id, arguments));
            }
        }
    }

    let mut context = argument_stack.pop().expect("No Term found");
    if !argument_stack.is_empty() { return Err("Too many Terms specified".to_string()); }
    let term = context.pop().expect("No Term found");
    if !context.is_empty() { return Err("Too many Terms specified".to_string()); }
    return Ok(term);
}

#[cfg(test)]
mod tests {
    use crate::{scope::Scope, term::{build_term, tokenize, Term, Token}};

    #[test]
    fn test_tokenize_simple() {
        let tokens = tokenize("T");
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            Token::Chars(s) => assert_eq!(s, "T"),
            _ => panic!("Expected Chars token"),
        }
    }

    #[test]
    fn test_tokenize_parens_and_whitespace() {
        let tokens = tokenize("f ( x , y )");
        let expected = vec![
            Token::Chars("f".to_string()),
            Token::OpenP,
            Token::Chars("x".to_string()),
            Token::Chars("y".to_string()),
            Token::CloseP,
        ];
        assert_eq!(tokens, expected);
    }

    #[test]
    fn test_tokenize_function() {
        let tokens = tokenize("f ( X )");
        let expected = vec![
            Token::Chars("f".to_string()),
            Token::OpenP,
            Token::Chars("X".to_string()),
            Token::CloseP,
        ];
        assert_eq!(tokens, expected);
    }

    #[test]
    fn test_build_term_true_false() {
        let scope = Scope::new();
        let term_true = build_term(&scope, tokenize("T")).unwrap();
        let term_false = build_term(&scope, tokenize("F")).unwrap();
        assert_eq!(term_true, Term::True);
        assert_eq!(term_false, Term::False);
    }

    #[test]
    fn test_build_term_variable() {
        let mut scope = Scope::new();
        let var = scope.allocate_variable("X".to_string());
        let term = build_term(&scope, tokenize("X")).unwrap();
        assert_eq!(term, var);
    }

    #[test]
    fn test_build_term_function() {
        let mut scope = Scope::new();
        let var = scope.allocate_variable("X".to_string());
        let func_id = scope.make_function(1, "f".to_string(), std::rc::Rc::new(|args| args[0].clone()));
        let input = "f ( X )";
        let term = build_term(&scope, tokenize(input)).unwrap();
        assert_eq!(term, Term::Function(func_id, vec![var]));
    }

    #[test]
    fn test_build_term_unknown_identifier() {
        let scope = Scope::new();
        let result = build_term(&scope, tokenize("Y"));
        assert!(result.is_err());
    }

    #[test]
    fn test_build_term_nested_functions() {
        let mut scope = Scope::new();
        let var_x = scope.allocate_variable("X".to_string());
        let var_y = scope.allocate_variable("Y".to_string());
        let func_g = scope.make_function(1, "g".to_string(), std::rc::Rc::new(|args| args[0].clone()));
        let func_f = scope.make_function(2, "f".to_string(), std::rc::Rc::new(|args| args[0].clone()));

        // f(g(X), Y)
        let input = "f ( g ( X ) , Y )";
        let term = build_term(&scope, tokenize(input)).unwrap();
        let expected = Term::Function(
            func_f,
            vec![
                Term::Function(func_g, vec![var_x.clone()]),
                var_y.clone(),
            ],
        );
        assert_eq!(term, expected);
    }
}

