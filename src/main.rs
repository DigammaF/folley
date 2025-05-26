#![allow(dead_code)]

use core::fmt;
use std::{collections::{HashMap, HashSet}, fmt::{Debug, Display}, io::{stdin, stdout, Write}, ops::{BitAnd, BitOr, BitXor, Not}, rc::Rc};

use once_cell::sync::Lazy;
use regex::Regex;

type Identifier = u8;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
enum Term {
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
    fn bound(&self, valuation: &HashMap<Identifier, Domain>) -> Term {
        match self {
            Term::True|Term::False|Term::Value(_) => self.clone(),
            Term::Variable(variable_identifier)
                => valuation.get(variable_identifier).map_or_else(
                    || self.clone(), |value| Term::Value(value.clone())
                ),
            Term::Function(identifier, terms)
                => Term::Function(*identifier, terms.iter().map(|term| term.bound(valuation)).collect())
        }
    }

    fn evaluate(&self, scope: &Scope) -> Option<Term> {
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
                if function.arity != arguments.len() {
                    panic!(
                        "Function {} expects {} arguments, {} given",
                        identifier, function.arity, arguments.len()
                    );
                }
                return Some((function.application)(argument_values));
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Formula {
    Term(Term),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Imply(Box<Formula>, Box<Formula>),
    Nimply(Box<Formula>, Box<Formula>),
    Nand(Box<Formula>, Box<Formula>),
    Nor(Box<Formula>, Box<Formula>),
    Xor(Box<Formula>, Box<Formula>),
    Nxor(Box<Formula>, Box<Formula>),
    A(Box<Formula>, Box<Formula>),
    B(Box<Formula>, Box<Formula>),
    NotA(Box<Formula>, Box<Formula>),
    NotB(Box<Formula>, Box<Formula>),
    Rimply(Box<Formula>, Box<Formula>),
    Nrimply(Box<Formula>, Box<Formula>),
    ForAll(Identifier, Box<Formula>),
    ThereExist(Identifier, Box<Formula>),
    Predicate(Identifier, Vec<Term>)
}

const TRUE: Formula = Formula::Term(Term::True);
const FALSE: Formula = Formula::Term(Term::False);

impl Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Term(term) => write!(f, "{}", term),
            Formula::Not(inner) => {
                match **inner {
                    Formula::Term(_) | Formula::Predicate(_, _) => write!(f, "¬{}", inner),
                    _ => write!(f, "¬({})", inner),
                }
            }
            Formula::And(a, b) => {
                let left = match **a {
                    Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", a),
                    _ => format!("{}", a),
                };
                let right = match **b {
                    Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} ∧ {}", left, right)
            }
            Formula::Or(a, b) => {
                let left = match **a {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", a),
                    _ => format!("{}", a),
                };
                let right = match **b {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} ∨ {}", left, right)
            }
            Formula::Imply(a, b) => {
                let left = match **a {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", a),
                    _ => format!("{}", a),
                };
                let right = match **b {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} → {}", left, right)
            }
            Formula::Nimply(a, b) => {
                let left = match **a {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", a),
                    _ => format!("{}", a),
                };
                let right = match **b {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} ↛  {}", left, right)
            }
            Formula::Nand(a, b) => {
                let left = match **a {
                    Formula::And(_, _) | Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", a),
                    _ => format!("{}", a),
                };
                let right = match **b {
                    Formula::And(_, _) | Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} ↑ {}", left, right)
            }
            Formula::Nor(a, b) => {
                let left = match **a {
                    Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", a),
                    _ => format!("{}", a),
                };
                let right = match **b {
                    Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} ↓ {}", left, right)
            }
            Formula::Xor(a, b) => {
                let left = match **a {
                    Formula::Xor(_, _) | Formula::Nxor(_, _) => format!("({})", a),
                    _ => format!("{}", a),
                };
                let right = match **b {
                    Formula::Xor(_, _) | Formula::Nxor(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} ⊕ {}", left, right)
            }
            Formula::Nxor(a, b) => {
                let left = match **a {
                    Formula::Xor(_, _) | Formula::Nxor(_, _) => format!("({})", a),
                    _ => format!("{}", a),
                };
                let right = match **b {
                    Formula::Xor(_, _) | Formula::Nxor(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} ⊙ {}", left, right)
            }
            Formula::A(a, b) => write!(f, "A({}, {})", a, b),
            Formula::B(a, b) => write!(f, "B({}, {})", a, b),
            Formula::NotA(a, b) => write!(f, "¬A({}, {})", a, b),
            Formula::NotB(a, b) => write!(f, "¬B({}, {})", a, b),
            Formula::Rimply(a, b) => {
                let left = match **a {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", a),
                    _ => format!("{}", a),
                };
                let right = match **b {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} ← {}", left, right)
            }
            Formula::Nrimply(a, b) => {
                let left = match **a {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", a),
                    _ => format!("{}", a),
                };
                let right = match **b {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} ↚  {}", left, right)
            }
            Formula::ForAll(id, inner) => write!(f, "∀{}.({})", id, inner),
            Formula::ThereExist(id, inner) => write!(f, "∃{}.({})", id, inner),
            Formula::Predicate(id, terms) => {
                write!(f, "P{}(", id)?;
                for (i, t) in terms.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", t)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Not for Formula {
    type Output = Self;

    fn not(self) -> Self::Output { Formula::Not(Box::new(self)) }
}

impl BitAnd for Formula {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output { Formula::And(Box::new(self), Box::new(rhs)) }
}

impl BitOr for Formula {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output { Formula::Or(Box::new(self), Box::new(rhs)) }
}

impl BitXor for Formula {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output { Formula::Xor(Box::new(self), Box::new(rhs)) }
}

impl Formula {
    fn evaluate(&self, scope: &Scope) -> Option<Formula> {
        match self {
            Formula::Term(term) => term.evaluate(scope).map(|term| Formula::Term(term)),
            Formula::Not(inner) => {
                if let Some(inner) = inner.evaluate(scope) {
                    match inner {
                        TRUE => Some(FALSE),
                        FALSE => Some(TRUE),
                        Formula::Not(a) => Some(*a),
                        _ => Some(!inner)
                    }
                } else { None }
            }
            Formula::And(a, b) => {
                if let Some(a) = a.evaluate(scope) {
                    if let Some(b) = b.evaluate(scope) {
                        match (&a, &b) {
                            (&TRUE, &TRUE) => Some(TRUE),
                            (&FALSE, _) | (_, &FALSE) => Some(FALSE),
                            (&TRUE, f) | (f, &TRUE) => Some(f.clone()),
                            _ => Some(a & b)
                        }
                    } else { None }
                } else { None }
            }
            Formula::Or(a, b) => {
                if let Some(a) = a.evaluate(scope) {
                    if let Some(b) = b.evaluate(scope) {
                        match (&a, &b) {
                            (&FALSE, &FALSE) => Some(FALSE),
                            (&TRUE, _) | (_, &TRUE) => Some(TRUE),
                            (&FALSE, f) | (f, &FALSE) => Some(f.clone()),
                            _ => Some(a | b)
                        }
                    } else { None }
                } else { None }
            }
            Formula::Imply(a, b) => {
                if let Some(a) = a.evaluate(scope) {
                    if let Some(b) = b.evaluate(scope) {
                        match (&a, &b) {
                            (&FALSE, _) | (_, &TRUE) => Some(TRUE),
                            (&TRUE, &FALSE) => Some(FALSE),
                            (&TRUE, f) => Some(f.clone()),
                            (a, b) if a == b => Some(TRUE),
                            _ => Some(Formula::Imply(Box::new(a), Box::new(b)))
                        }
                    } else { None }
                } else { None }
            }
            Formula::Nimply(a, b) => {
                if let Some(a) = a.evaluate(scope) {
                    if let Some(b) = b.evaluate(scope) {
                        match (&a, &b) {
                            (&FALSE, _) | (_, &TRUE) => Some(FALSE),
                            (&TRUE, &FALSE) => Some(TRUE),
                            (&TRUE, f) => Some(!f.clone()),
                            (a, b) if a == b => Some(FALSE),
                            _ => Some(Formula::Nimply(Box::new(a), Box::new(b)))
                        }
                    } else { None }
                } else { None }
            }
            Formula::Nand(a, b) => {
                if let Some(a) = a.evaluate(scope) {
                    if let Some(b) = b.evaluate(scope) {
                        match (&a, &b) {
                            (&TRUE, &TRUE) => Some(FALSE),
                            (&FALSE, _) | (_, &FALSE) => Some(TRUE),
                            (&TRUE, f) | (f, &TRUE) => Some(!f.clone()),
                            _ => Some(Formula::Nand(Box::new(a), Box::new(b)))
                        }
                    } else { None }
                } else { None }
            }
            Formula::Nor(a, b) => {
                if let Some(a) = a.evaluate(scope) {
                    if let Some(b) = b.evaluate(scope) {
                        match (&a, &b) {
                            (&FALSE, &FALSE) => Some(TRUE),
                            (&TRUE, _) | (_, &TRUE) => Some(FALSE),
                            (&FALSE, f) | (f, &FALSE) => Some(!f.clone()),
                            _ => Some(Formula::Nor(Box::new(a), Box::new(b)))
                        }
                    } else { None }
                } else { None }
            }
            Formula::Xor(a, b) => {
                if let Some(a) = a.evaluate(scope) {
                    if let Some(b) = b.evaluate(scope) {
                        match (&a, &b) {
                            (&TRUE, &TRUE) | (&FALSE, &FALSE) => Some(FALSE),
                            (&TRUE, &FALSE) | (&FALSE, &TRUE) => Some(TRUE),
                            (&TRUE, f) | (f, &TRUE) => Some(!f.clone()),
                            (&FALSE, f) | (f, &FALSE) => Some(f.clone()),
                            (a, b) if a == b => Some(FALSE),
                            _ => Some(Formula::Xor(Box::new(a), Box::new(b)))
                        }
                    } else { None }
                } else { None }
            }
            Formula::Nxor(a, b) => {
                if let Some(a) = a.evaluate(scope) {
                    if let Some(b) = b.evaluate(scope) {
                        match (&a, &b) {
                            (&TRUE, &TRUE) | (&FALSE, &FALSE) => Some(TRUE),
                            (&TRUE, &FALSE) | (&FALSE, &TRUE) => Some(FALSE),
                            (&TRUE, f) | (f, &TRUE) => Some(f.clone()),
                            (&FALSE, f) | (f, &FALSE) => Some(!f.clone()),
                            (a, b) if a == b => Some(TRUE),
                            _ => Some(Formula::Nxor(Box::new(a), Box::new(b)))
                        }
                    } else { None }
                } else { None }
            }
            Formula::A(a, _) => {
                if let Some(a) = a.evaluate(scope) {
                    Some(a)
                } else { None }
            }
            Formula::B(_, b) => {
                if let Some(b) = b.evaluate(scope) {
                    Some(b)
                } else { None }
            }
            Formula::NotA(a, _) => {
                if let Some(a) = (!*a.clone()).evaluate(scope) {
                    Some(a)
                } else { None }
            }
            Formula::NotB(_, b) => {
                if let Some(b) = (!*b.clone()).evaluate(scope) {
                    Some(b)
                } else { None }
            }
            Formula::Rimply(b, a) => {
                if let Some(a) = a.evaluate(scope) {
                    if let Some(b) = b.evaluate(scope) {
                        match (&a, &b) {
                            (&FALSE, _) | (_, &TRUE) => Some(TRUE),
                            (&TRUE, &FALSE) => Some(FALSE),
                            (&TRUE, f) => Some(f.clone()),
                            (a, b) if a == b => Some(TRUE),
                            _ => Some(Formula::Rimply(Box::new(b), Box::new(a)))
                        }
                    } else { None }
                } else { None }
            }
            Formula::Nrimply(a, b) => {
                if let Some(a) = a.evaluate(scope) {
                    if let Some(b) = b.evaluate(scope) {
                        match (&a, &b) {
                            (&FALSE, _) | (_, &TRUE) => Some(FALSE),
                            (&TRUE, &FALSE) => Some(TRUE),
                            (&TRUE, f) => Some(!f.clone()),
                            (a, b) if a == b => Some(FALSE),
                            _ => Some(Formula::Nrimply(Box::new(b), Box::new(a)))
                        }
                    } else { None }
                } else { None }
            }
            Formula::ForAll(identifier, f)
                => f.evaluate(scope).map(|f| Formula::ForAll(*identifier, Box::new(f))),
            Formula::ThereExist(identifier, f)
                => f.evaluate(scope).map(|f| Formula::ThereExist(*identifier, Box::new(f))),
            Formula::Predicate(identifier, terms) => {
                let predicate = scope.get_predicate(identifier);
                
                if predicate.arity != terms.len() {
                    panic!(
                        "Predicate {} expects {} arguments, {} given",
                        identifier, predicate.arity, terms.len()
                    );
                }

                let mut term_values: Vec<Term> = Vec::new();

                for term in terms.iter() {
                    if let Some(value) = term.evaluate(scope) {
                        term_values.push(value);
                    } else { return None; }
                }

                return Some(Formula::Predicate(*identifier, term_values));
            }
        }
    }

    fn transform<F, C, T: Copy>(&mut self, fun: &F, collapse: &C, initial: T) -> T
    where
        F: Fn(&mut Formula) -> Option<T>,
        C: Fn(T, T) -> T
    {
        if let Some(value) = fun(self) { return value; }

        match self {
            Formula::Term(_)|Formula::Predicate(_, _) => initial,
            Formula::Not(inner)
            |Formula::ForAll(_, inner)
            |Formula::ThereExist(_, inner) => inner.transform(fun, collapse, initial),
            Formula::And(a, b)
            |Formula::Or(a, b)
            |Formula::Imply(a, b)
            |Formula::Nimply(a, b)
            |Formula::Nand(a, b)
            |Formula::Nor(a, b)
            |Formula::Xor(a, b)
            |Formula::Nxor(a, b)
            |Formula::A(a, b)
            |Formula::B(a, b)
            |Formula::NotA(a, b)
            |Formula::NotB(a, b)
            |Formula::Rimply(a, b)
            |Formula::Nrimply(a, b) => collapse(
                a.transform(fun, collapse, initial), b.transform(fun, collapse, initial)
            )
        }
    }

    fn rewrite(&mut self, truth: &Formula) -> bool {
        self.transform(
            &|formula| {
                if *formula == *truth {
                    *formula = Formula::Term(Term::True);
                    Some(true)
                } else { None }
            },
            &|a, b| a || b,
            false,
        )
    }

    fn bound(&self, valuation: &HashMap<Identifier, Domain>) -> Formula {
        match self {
            Formula::Term(term) => Formula::Term(term.bound(valuation)),
            Formula::Predicate(identifier, terms)
                => Formula::Predicate(*identifier, terms.iter().map(|term| term.bound(valuation)).collect()),
            Formula::Not(inner) => Formula::Not(Box::new(inner.bound(valuation))),
            Formula::ForAll(identifier, inner) => {
                let mut sub_valuation = valuation.clone();
                sub_valuation.remove(identifier);
                Formula::ForAll(*identifier, Box::new(inner.bound(&sub_valuation)))
            }
            Formula::ThereExist(identifier, inner) => {
                let mut sub_valuation = valuation.clone();
                sub_valuation.remove(identifier);
                Formula::ThereExist(*identifier, Box::new(inner.bound(&sub_valuation)))
            }
            Formula::And(a, b) => Formula::And(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::Or(a, b) => Formula::Or(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::Imply(a, b) => Formula::Imply(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::Nimply(a, b) => Formula::Nimply(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::Nand(a, b) => Formula::Nand(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::Nor(a, b) => Formula::Nor(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::Xor(a, b) => Formula::Xor(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::Nxor(a, b) => Formula::Nxor(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::A(a, b) => Formula::A(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::B(a, b) => Formula::B(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::NotA(a, b) => Formula::NotA(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::NotB(a, b) => Formula::NotB(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::Rimply(a, b) => Formula::Rimply(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
            Formula::Nrimply(a, b) => Formula::Nrimply(Box::new(a.bound(valuation)), Box::new(b.bound(valuation))),
        }
    }

    fn description(&self) -> &str {
        match self {
            Formula::Term(_) => "Term",
            Formula::Predicate(_, _) => "Predicate",
            Formula::Not(_) => "Negation",
            Formula::ForAll(_, _) => "ForAll",
            Formula::ThereExist(_, _) => "ThereExist",
            Formula::And(_, _) => "Conjunction",
            Formula::Or(_, _) => "Disjunction",
            Formula::Imply(_, _) => "Implication",
            Formula::Nimply(_, _) => "NegativeImplication",
            Formula::Nand(_, _) => "NegativeConjunction",
            Formula::Nor(_, _) => "NegativeDisjunction",
            Formula::Xor(_, _) => "ExclusiveDisjunction",
            Formula::Nxor(_, _) => "NegativeExclusiveDisjunction",
            Formula::A(_, _) => "First",
            Formula::B(_, _) => "Second",
            Formula::NotA(_, _) => "NegativeFirst",
            Formula::NotB(_, _) => "NegativeSecond",
            Formula::Rimply(_, _) => "ReverseImplication",
            Formula::Nrimply(_, _) => "NegativeReverseImplication",
        }
    }
}

#[derive(Clone)]
struct Function {
    arity: usize, application: Rc<dyn Fn(Vec<Term>) -> Term>
}

impl Debug for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Function")
            .field("arity", &self.arity)
            .field("application id", &format_args!("{:p}", Rc::as_ptr(&self.application)))
            .finish()
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Function(arity: {})", self.arity)
    }
}

#[derive(Clone, Debug)]
struct Predicate {
    arity: usize
}

impl Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Predicate(arity: {})", self.arity)
    }
}

#[derive(Clone, Debug)]
struct Scope {
    last_allocated_id: Identifier,
    bindings: HashMap<Identifier, Domain>,
    variables: HashSet<Identifier>,
    functions: HashMap<Identifier, Function>,
    predicates: HashMap<Identifier, Predicate>,
    reprs: HashMap<Identifier, String>, rev_reprs: HashMap<String, Identifier>
}

impl Display for Scope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "  Variables: ")?;
        for id in &self.variables {
            if let Some(repr) = self.reprs.get(id) { write!(f, "{repr} ({id}), ")?; }
            else { write!(f, "{}, ", id)?; }
        }
        writeln!(f, "")?;
        writeln!(f, "  Bindings: ")?;
        for (key, value) in &self.bindings {
            let key_repr = if let Some(repr) = self.reprs.get(key) { format!("{repr} ({key})") } else { format!("{key}") };
            let value_repr = value.to_string();
            write!(f, "{key_repr} -> {value_repr}, ")?;
        }
        writeln!(f, "")?;
        writeln!(f, "  Functions:")?;
        for (id, func) in &self.functions {
            if let Some(repr) = self.reprs.get(id) { writeln!(f, "    f{} {}: {}", id, repr, func)?; }
            else { writeln!(f, "    f{}: {}", id, func)?; }
        }
        write!(f, "  Predicates:")?;
        for (id, pred) in &self.predicates {
            if let Some(repr) = self.reprs.get(id) { write!(f, "\n    P{} {}: {}", id, repr, pred)?; }
            else { write!(f, "\n    P{}: {}", id, pred)?; }
        }
        Ok(())
    }
}

impl Scope {
    fn new() -> Self {
        Scope {
            last_allocated_id: 0,
            bindings: HashMap::new(),
            variables: HashSet::new(), functions: HashMap::new(),
            predicates: HashMap::new(),
            reprs: HashMap::new(), rev_reprs: HashMap::new()
        }
    }

    fn format_term(&self, term: &Term) -> String {
        match term {
            Term::True => "⊤".to_string(),
            Term::False => "⊥".to_string(),
            Term::Variable(id) => {
                if let Some(repr) = self.reprs.get(id) {
                    format!("{}", repr)
                } else {
                    format!("${}", id)
                }
            }
            Term::Value(id) => { id.to_string() }
            Term::Function(id, args) => {
                let name = if let Some(repr) = self.reprs.get(id) {
                    format!("{}", repr)
                } else {
                    format!("f{}", id)
                };
                let args_str = args.iter().map(|t| self.format_term(t)).collect::<Vec<_>>().join(", ");
                format!("{}({})", name, args_str)
            }
        }
    }

    fn format_formula(&self, formula: &Formula) -> String {
        match formula {
            Formula::Term(term) => self.format_term(term),
            Formula::Predicate(id, terms) => {
                let name = if let Some(repr) = self.reprs.get(id) {
                    format!("{}", repr)
                } else {
                    format!("P{}", id)
                };
                let args_str = terms.iter().map(|t| self.format_term(t)).collect::<Vec<_>>().join(", ");
                format!("{}({})", name, args_str)
            }
            Formula::Not(inner) => {
                let inner_str = self.format_formula(inner);
                match **inner {
                    Formula::Term(_) | Formula::Predicate(_, _) => format!("¬{}", inner_str),
                    _ => format!("¬({})", inner_str),
                }
            }
            Formula::And(a, b) => {
                let left = match **a {
                    Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(a)),
                    _ => self.format_formula(a),
                };
                let right = match **b {
                    Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(b)),
                    _ => self.format_formula(b),
                };
                format!("{} ∧ {}", left, right)
            }
            Formula::Or(a, b) => {
                let left = match **a {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(a)),
                    _ => self.format_formula(a),
                };
                let right = match **b {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(b)),
                    _ => self.format_formula(b),
                };
                format!("{} ∨ {}", left, right)
            }
            Formula::Imply(a, b) => {
                let left = match **a {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(a)),
                    _ => self.format_formula(a),
                };
                let right = match **b {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(b)),
                    _ => self.format_formula(b),
                };
                format!("{} → {}", left, right)
            }
            Formula::Nimply(a, b) => {
                let left = match **a {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(a)),
                    _ => self.format_formula(a),
                };
                let right = match **b {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(b)),
                    _ => self.format_formula(b),
                };
                format!("{} ↛  {}", left, right)
            }
            Formula::Nand(a, b) => {
                let left = match **a {
                    Formula::And(_, _) | Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(a)),
                    _ => self.format_formula(a),
                };
                let right = match **b {
                    Formula::And(_, _) | Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(b)),
                    _ => self.format_formula(b),
                };
                format!("{} ↑ {}", left, right)
            }
            Formula::Nor(a, b) => {
                let left = match **a {
                    Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(a)),
                    _ => self.format_formula(a),
                };
                let right = match **b {
                    Formula::Or(_, _) | Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Nand(_, _) | Formula::Nor(_, _) | Formula::Xor(_, _) | Formula::Nxor(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(b)),
                    _ => self.format_formula(b),
                };
                format!("{} ↓ {}", left, right)
            }
            Formula::Xor(a, b) => {
                let left = match **a {
                    Formula::Xor(_, _) | Formula::Nxor(_, _) => format!("({})", self.format_formula(a)),
                    _ => self.format_formula(a),
                };
                let right = match **b {
                    Formula::Xor(_, _) | Formula::Nxor(_, _) => format!("({})", self.format_formula(b)),
                    _ => self.format_formula(b),
                };
                format!("{} ⊕ {}", left, right)
            }
            Formula::Nxor(a, b) => {
                let left = match **a {
                    Formula::Xor(_, _) | Formula::Nxor(_, _) => format!("({})", self.format_formula(a)),
                    _ => self.format_formula(a),
                };
                let right = match **b {
                    Formula::Xor(_, _) | Formula::Nxor(_, _) => format!("({})", self.format_formula(b)),
                    _ => self.format_formula(b),
                };
                format!("{} ⊙ {}", left, right)
            }
            Formula::A(a, b) => format!("A({}, {})", self.format_formula(a), self.format_formula(b)),
            Formula::B(a, b) => format!("B({}, {})", self.format_formula(a), self.format_formula(b)),
            Formula::NotA(a, b) => format!("¬A({}, {})", self.format_formula(a), self.format_formula(b)),
            Formula::NotB(a, b) => format!("¬B({}, {})", self.format_formula(a), self.format_formula(b)),
            Formula::Rimply(a, b) => {
                let left = match **a {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(a)),
                    _ => self.format_formula(a),
                };
                let right = match **b {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(b)),
                    _ => self.format_formula(b),
                };
                format!("{} ← {}", left, right)
            }
            Formula::Nrimply(a, b) => {
                let left = match **a {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(a)),
                    _ => self.format_formula(a),
                };
                let right = match **b {
                    Formula::Imply(_, _) | Formula::Nimply(_, _) | Formula::Rimply(_, _) | Formula::Nrimply(_, _) => format!("({})", self.format_formula(b)),
                    _ => self.format_formula(b),
                };
                format!("{} ↚  {}", left, right)
            }
            Formula::ForAll(id, inner) => {
                let name = if let Some(repr) = self.reprs.get(id) {
                    repr.clone()
                } else {
                    id.to_string()
                };
                format!("∀{}.({})", name, self.format_formula(inner))
            }
            Formula::ThereExist(id, inner) => {
                let name = if let Some(repr) = self.reprs.get(id) {
                    repr.clone()
                } else {
                    id.to_string()
                };
                format!("∃{}.({})", name, self.format_formula(inner))
            }
        }
    }

    fn is_variable(&self, identifier: &Identifier) -> bool { self.variables.contains(identifier) }
    fn is_function(&self, identifier: &Identifier) -> bool { self.functions.contains_key(identifier) }
    fn is_predicate(&self, identifier: &Identifier) -> bool { self.predicates.contains_key(identifier) }

    fn allocate(&mut self) -> Identifier {
        if let Some(identifier) = self.last_allocated_id.checked_add(1) {
            self.last_allocated_id = identifier;
            return identifier;
        } else { panic!("Can't allocate: no more space in identifier space"); }
    }

    fn bind_repr(&mut self, identifier: Identifier, repr: String) {
        if let Some(existing_repr) = self.reprs.get(&identifier) { panic!("{repr} ({identifier}) already bound to {existing_repr}, cannot bind to {repr}"); }
        self.reprs.insert(identifier, repr.clone());
        self.rev_reprs.insert(repr, identifier);
    }

    fn get_identifier(&self, repr: &str) -> Option<Identifier> { self.rev_reprs.get(repr).cloned() }

    fn allocate_lambda_variable(&mut self) -> Term {
        let identifier = self.allocate();
        self.variables.insert(identifier);
        return Term::Variable(identifier);
    }

    fn allocate_variable(&mut self, repr: String) -> Term {
        let identifier = self.allocate();
        self.variables.insert(identifier);
        self.bind_repr(identifier, repr);
        return Term::Variable(identifier);
    }

    fn allocate_lambda_variables(&mut self, count: Identifier) -> Vec<Term> {
        (0..count).map(|_| self.allocate_lambda_variable()).collect()
    }

    fn allocate_variables(&mut self, count: Identifier, repr: fn(Identifier) -> String) -> Vec<Term> {
        (0..count).map(|n| self.allocate_variable(repr(n))).collect()
    }

    fn make_predicate(&mut self, arity: usize, repr: String) -> Identifier {
        let identifier = self.allocate();
        self.predicates.insert(identifier, Predicate { arity });
        self.bind_repr(identifier, repr);
        return identifier;
    }

    fn make_function(&mut self, arity: usize, repr: String, application: Rc<dyn Fn(Vec<Term>) -> Term>) -> Identifier {
        let identifier = self.allocate();
        self.functions.insert(identifier, Function { arity, application });
        self.bind_repr(identifier, repr);
        return identifier;
    }

    fn bind(&mut self, variable: Identifier, value: Domain) {
        self.variables.get(&variable).expect(&format!("Can only bind to variable, not {variable}"));
        self.bindings.insert(variable, value);
    }

    fn unbind(&mut self, variable: Identifier) {
        self.variables.get(&variable).expect(&format!("Can only unbind from variables, not {variable}"));
        self.bindings.remove(&variable);
    }

    fn get_value(&self, variable: &Identifier) -> Option<Domain> {
        self.bindings.get(variable).cloned()
    }

    fn get_function(&self, identifier: &Identifier) -> &Function {
        self.functions.get(identifier).expect(&format!("Unknown function: {identifier}"))
    }

    fn get_predicate(&self, identifier: &Identifier) -> &Predicate {
        self.predicates.get(identifier).expect(&format!("Unknown predicate: {identifier}"))
    }
}

#[derive(Debug)]
enum Operation {
    Instantiate(usize, Vec<Domain>),
    ModusPonens(usize), ModusPonensGoal,
    Name(Vec<Domain>),
    Rewrite(usize),
    Eval,
    QED,
    Contradict,
    Combine(usize, usize),
    Simplify(usize)
}

impl Operation {
    fn parse(source: &str) -> Result<Self, String> {
        if let Some(captures) = INSTANTIATE_RE.captures(source) {
            
            let mut values: Vec<Domain> = Vec::new();

            for hit in VALUE_RE.find_iter(&captures["values"]) {
                if let Ok(value) = hit.as_str().parse::<Domain>() {
                    values.push(value);
                } else { return Err(format!("Unable to parse {} to a domain value", hit.as_str()).to_string()); }
            }

            if let Ok(key) = captures["theorem"].parse::<usize>() {
                Ok(Operation::Instantiate(key, values))
            } else { Err(format!("Cannot parse {} as a key", &captures["theorem"]).to_string()) }

        } else if let Some(captures) = MODUS_PONENS_RE.captures(source) {
            
            if captures["theorem"].starts_with("G") { Ok(Operation::ModusPonensGoal) } else {
                if let Ok(key) = captures["theorem"].parse::<usize>() {
                    Ok(Operation::ModusPonens(key))
                } else { Err(format!("Cannot parse {} as a key", &captures["theorem"]).to_string()) }
            }    
        
        } else if let Some(captures) = NAME_RE.captures(source) {
            
            let mut values: Vec<Domain> = Vec::new();

            for hit in VALUE_RE.find_iter(&captures["values"]) {
                if let Ok(value) = hit.as_str().parse::<Domain>() {
                    values.push(value);
                } else { return Err(format!("Unknown symbol {}", hit.as_str()).to_string()); }
            }

            Ok(Operation::Name(values))
        
        } else if let Some(captures) = REWRITE_RE.captures(source) {

            if let Ok(key) = captures["theorem"].parse::<usize>() {
                Ok(Operation::Rewrite(key))
            } else { Err(format!("Cannot parse {} as a key", &captures["theorem"]).to_string()) } 

        } else if EVAL_RE.is_match(&source) {

            Ok(Operation::Eval)

        } else if QED_RE.is_match(&source) {

            Ok(Operation::QED)

        } else if CONTRADICT_RE.is_match(&source) {

            Ok(Operation::Contradict)

        } else if let Some(captures) = COMBINE_RE.captures(source) {

            if let Ok(a) = captures["a"].parse::<usize>() {
                if let Ok(b) = captures["b"].parse::<usize>() {
                    Ok(Operation::Combine(a, b))
                } else { Err(format!("Cannot parse {} as a key", &captures["b"]).to_string()) }
            } else { Err(format!("Cannot parse {} as a key", &captures["a"]).to_string()) }

        } else if let Some(captures) = SIMPLIFY_RE.captures(source) {

            if let Ok(theorem) = captures["theorem"].parse::<usize>() {
                Ok(Operation::Simplify(theorem))
            } else { Err(format!("Cannot parse {} as a key", &captures["theorem"]).to_string()) }

        } else { Err("Couldn't parse source".to_string()) }
    }
}

static IDENTIFIER_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\d+").unwrap());
static REPR_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\w+").unwrap());
static VALUE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"[^,]").unwrap());

static INSTANTIATE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"instantiate *(?<theorem>\d+) *(?:with *(?<values>[^,]+ *(?:, *[^,]+ *)*))? *").unwrap());
static MODUS_PONENS_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"modus ponens *(?<theorem>\d+|G) *").unwrap());
static NAME_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"name *(?<values>[^,]+ *(?:, *[^,]+ *)*) *").unwrap());
static REWRITE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"rewrite with *(?<theorem>\d+) *").unwrap());
static EVAL_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"eval").unwrap());
static QED_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"qed").unwrap());
static CONTRADICT_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"contradict").unwrap());
static COMBINE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"combine *(?<a>\d+) *with *(?<b>\d+) *").unwrap());
static SIMPLIFY_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"simplify *(?<theorem>\d+) *").unwrap());

fn read_text(prompt: &str) -> String {
    print!("{prompt}");
    stdout().flush().expect("Could not flush stdout");
    let mut input = String::new();
    stdin().read_line(&mut input).expect("Could not read stdin");
    input = input.trim().to_string();
    input
}

#[derive(Clone, Debug)]
struct Context {
    theorems: Vec<Formula>, goals: Vec<Formula>, scope: Scope, mutated: bool
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Theorems:")?;
        for (i, theorem) in self.theorems.iter().enumerate() {
            writeln!(f, "  [{i}] {}", self.scope.format_formula(theorem))?;
        }
        write!(f, "Goals:")?;
        for (i, goal) in self.goals.iter().enumerate() {
            write!(f, "\n  [{i}] {}", self.scope.format_formula(goal))?;
        }
        Ok(())
        // writeln!(f, "Scope:")?;
        // write!(f, "{}", self.scope)
    }
}

impl Context {
    fn mainloop(&mut self) {
        self.mutated = true;

        while !self.goals.is_empty() {
            if self.mutated { println!("{}", self); self.mutated = false; }
            let command = read_text("(?) ");

            match Operation::parse(&command) {
                Ok(operation) => {
                    println!("(...) applying {operation:?}");

                    match self.apply(operation) {
                        Ok(message) => println!("(+) {message}"),
                        Err(message) => println!("(!) {message}")
                    }
                }
                Err(message) => {
                    println!("(!) {message}");
                }
            }
        }

        println!("All is solved! ^-^");
    }

    fn solved(&self) -> bool { self.goals.is_empty() }

    fn remove_solved_goals(&mut self) {
        self.goals = self.goals
            .iter().cloned()
            .filter(|goal| goal != &TRUE)
            .collect();
    }

    fn apply(&mut self, operation: Operation) -> Result<String, String> {
        match operation {
            Operation::Instantiate(theorem_key, values) => {
                let mut theorem = self.theorems.get(theorem_key).ok_or(format!("invalid theorem key: {theorem_key}"))?;
                let mut valuation: HashMap<Identifier, Domain> = HashMap::new();

                for value in values.into_iter() {
                    if let Formula::ForAll(variable, formula) = theorem {
                        valuation.insert(*variable, value);
                        theorem = &*formula;
                    } else { return Err(format!("outermost Formula is not ForAll, it is {}", theorem.description()).to_string()); }
                }

                self.theorems.push(theorem.bound(&valuation));
                self.mutated = true;
                Ok(format!("instantiated with valuation {valuation:?}").to_string())
            }
            Operation::ModusPonens(theorem_key) => {
                let theorem = self.theorems.get(theorem_key).ok_or(format!("invalid theorem key: {theorem_key}"))?;

                if let Formula::Imply(a, b) = theorem.clone() {
                    self.theorems.push(*b);
                    self.goals.push(*a);
                    self.mutated = true;
                    Ok("done".to_string())
                } else { Err(format!("outermost Formula is not an Implication, it is {}", theorem.description()).to_string()) }
            }
            Operation::ModusPonensGoal => {
                let goal = self.goals.pop().ok_or("no goal in this context")?;

                if let Formula::Imply(a, b) = goal {
                    self.theorems.push(*a);
                    self.goals.push(*b);
                    self.mutated = true;
                    Ok("done".to_string())
                } else {
                    let text = format!("outermost Formula is not an Implication, it is {}", goal.description()).to_string();
                    self.goals.push(goal);
                    Err(text)
                }
            }
            Operation::Name(values) => {
                let mut goal = self.goals.pop().ok_or("no goal in this context")?;
                let backup = goal.clone();
                let mut valuation: HashMap<Identifier, Domain> = HashMap::new();

                for value in values.into_iter() {
                    if let Formula::ThereExist(variable, formula) = goal {
                        valuation.insert(variable, value);
                        goal = *formula;
                    } else {
                        self.goals.push(backup);
                        return Err(format!("outermost Formula is not ThereExist, it is {}", goal.description()).to_string());
                    }
                }

                self.goals.push(goal.bound(&valuation));
                self.mutated = true;
                Ok("instantiated".to_string())
            }
            Operation::Rewrite(theorem_key) => {
                let goal = self.goals.last_mut().ok_or("no goal in this context")?;
                let theorem = self.theorems.get(theorem_key).ok_or(format!("invalid theorem key: {theorem_key}"))?;

                if goal.rewrite(theorem) { self.mutated = true; Ok("rewritten".to_string()) }
                else { Ok("nothing to rewrite".into()) }
            }
            Operation::Eval => {
                let goal = self.goals.pop().ok_or("no goal in this context")?;

                if let Some(new_goal) = goal.evaluate(&self.scope) {
                    self.goals.push(new_goal);
                    self.mutated = true;
                    Ok("evaluated".to_string())
                } else {
                    self.goals.push(goal);
                    Ok("not evaluable".to_string())
                }
            }
            Operation::QED => {
                let goal = self.goals.pop().ok_or("no goal in this context")?;

                if goal == TRUE {
                    self.mutated = true;
                    Ok("∎ proved".to_string()) }
                else {
                    let text = format!("goal is not ⊤, goal is {}", goal.description());
                    self.goals.push(goal);
                    Ok(text)
                }
            }
            Operation::Contradict => {
                let goal = self.goals.pop().ok_or("no goal in this context")?;
                self.goals.push(!!goal);
                self.mutated = true;
                Ok("added double negation".to_string())
            }
            Operation::Combine(a, b) => {
                let theorem_a = self.theorems.get(a).ok_or(format!("invalid theorem key: {a}"))?;
                let theorem_b = self.theorems.get(b).ok_or(format!("invalid theorem key: {b}"))?;
                let mut new_theorem = theorem_a.clone();
                
                if new_theorem.rewrite(theorem_b) {
                    self.theorems.push(new_theorem);
                    self.mutated = true;
                    Ok("added new theorem".to_string())
                } else { Ok("nothing new to add to theorems".to_string()) }
            }
            Operation::Simplify(theorem_key) => {
                let theorem = self.theorems.get(theorem_key).ok_or(format!("invalid theorem key: {theorem_key}"))?;

                if let Some(new_theorem) = theorem.evaluate(&self.scope) {
                    self.theorems.push(new_theorem);
                    self.mutated = true;
                    Ok("evaluated to a new theorem".to_string())
                } else {
                    Ok("not evaluable".to_string())
                }
            }
        }
    }
}

mod notation {
    use crate::{Formula, Identifier, Term, Domain};

    pub fn var(v: &Term) -> Term { v.clone() }
    pub fn value(v: Domain) -> Term { Term::Value(v) }
    pub fn term(t: &Term) -> Formula { Formula::Term(t.clone()) }
    pub fn imply(a: Formula, b: Formula) -> Formula { Formula::Imply(Box::new(a), Box::new(b)) }
    pub fn and(a: Formula, b: Formula) -> Formula { Formula::And(Box::new(a), Box::new(b)) }
    pub fn or(a: Formula, b: Formula) -> Formula { Formula::Or(Box::new(a), Box::new(b)) }
    pub fn not(a: Formula) -> Formula { Formula::Not(Box::new(a)) }
    pub fn iff(a: Formula, b: Formula) -> Formula { Formula::Nxor(Box::new(a), Box::new(b)) }
    pub fn for_all(variable: &Term, f: Formula) -> Formula {
        match variable {
            Term::Variable(identifier) => Formula::ForAll(*identifier, Box::new(f)),
            _ => panic!("Cannot quantify (∀) over non-variable {variable}")
        }
    }
    pub fn there_exist(variable: &Term, f: Formula) -> Formula {
        match variable {
            Term::Variable(identifier) => Formula::ThereExist(*identifier, Box::new(f)),
            _ => panic!("Cannot quantify (∃) over non-variable {variable}")
        }
    }
    pub fn p(identifier: Identifier, arguments: Vec<&Term>) -> Formula {
        Formula::Predicate(identifier, arguments.into_iter().cloned().collect())
    }
    pub fn f(identifier: Identifier, arguments: Vec<&Term>) -> Term {
        Term::Function(identifier, arguments.into_iter().cloned().collect())
    }
}

// working on positive integers
type Domain = u128;

fn main() {
    use crate::notation::*;

    let mut scope = Scope::new();

    // --- Variables ------------------------------
    // a general purpose variable and its string representation
    let x = &scope.allocate_variable("X".into());
    let y = &scope.allocate_variable("Y".into());
    let z = &scope.allocate_variable("Z".into());

    // --- Predicates -----------------------------
    // the '=' predicate
    let eq_id = scope.make_predicate(2, "Eq".into());
    let eq = |a: Term, b: Term| { p(eq_id, vec![&a, &b]) };

    let t_id = scope.make_predicate(1, "T".into());
    let t = |a: Term| { p(t_id, vec![&a]) };

    // --- Functions ------------------------------
    // the successor function, computes +1
    let successor_id = scope.make_function(
        1, "S".into(),
        Rc::new(|terms| {
            if let Term::Value(value) = terms.first().unwrap() {
                Term::Value(*value + 1)
            } else { panic!() }
        })
    );
    let successor = |term: Term| { f(successor_id, vec![&term]) };

    let sum_id = scope.make_function(
        2, "+".into(),
        Rc::new(|terms| {
            let mut terms = terms.into_iter();
            let a = terms.next().unwrap();
            let b = terms.next().unwrap();
            if let (Term::Value(a), Term::Value(b)) = (a, b) {
                Term::Value(a + b)
            } else { panic!() }
        })
    );
    let sum = |a: Term, b: Term| { f(sum_id, vec![&a, &b]) };

    let product_id = scope.make_function(
        2, "*".into(),
        Rc::new(|terms| {
            let mut terms = terms.into_iter();
            let a = terms.next().unwrap();
            let b = terms.next().unwrap();
            if let (Term::Value(a), Term::Value(b)) = (a, b) {
                Term::Value(a * b)
            } else { panic!() }
        })
    );
    let product = |a: Term, b: Term| { f(product_id, vec![&a, &b]) };

    // --- Theorems -------------------------------
    let theorems = vec![
        // --- Axioms -------------------------------------------------------
        // ∀X.Eq(X, X)
        for_all(x, eq(var(x), var(x))),
        // ∀X.∀Y.Eq(X, Y) <-> Eq(Y, X)
        for_all(x, for_all(y,
            iff(eq(var(x), var(y)), eq(var(y), var(x)))
        )),
        // ∀X.∀Y.∀Z.(Eq(X, Y) ∧ Eq(Y, Z)) -> Eq(X, Z)
        for_all(x, for_all(y, for_all(z,
            imply(eq(var(x), var(y)) & eq(var(y), var(z)), eq(var(x), var(z)))
        ))),
        // ∀X.¬Eq(0, S(X))
        for_all(x, !eq(value(0), successor(var(x)))),
        // ∀X.∀Y.Eq(S(X), S(Y)) -> Eq(X, Y)
        for_all(x, for_all(y, 
            imply(eq(successor(var(x)), successor(var(y))), eq(var(x), var(y)))
        )),
        // ∀X.Eq(+(X, 0), X)
        for_all(x, eq(sum(var(x), value(0)), var(x))),
        // ∀X.∀Y.Eq(+(X, S(Y)), S(+(X, Y)))
        for_all(x, for_all(y,
            eq(sum(var(x), successor(var(y))), successor(sum(var(x), var(y))))
        )),
        // ∀X.Eq(*(X, 0), 0)
        for_all(x, eq(product(var(x), value(0)), value(0))),
        // ∀X.∀Y.Eq(*(X, S(Y)), +(*(X, Y), X))
        for_all(x, for_all(y,
            eq(
                product(var(x), successor(var(y))),
                sum(product(var(x), var(y)), var(x))
            )
        )),
        iff(t(value(2)), t(value(4))),
        // --- Situation ----------------------------------------------------
    ];

    // --- Goals -----------------------------------
    let goals = vec![
        imply(t(value(2)), t(value(4))),
    ];

    // --------------------------------------------
    let mut context = Context { theorems, goals, scope, mutated: true };
    context.mainloop();
}
