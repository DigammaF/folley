use std::{collections::HashMap, fmt::{self, Display}, ops::{BitAnd, BitOr, BitXor, Not}};

use crate::{scope::Scope, term::Term, Domain, Identifier};


#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
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

pub const TRUE: Formula = Formula::Term(Term::True);
pub const FALSE: Formula = Formula::Term(Term::False);

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
    pub fn evaluate(&self, scope: &Scope) -> Option<Formula> {
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
                
                if predicate.arity() != terms.len() {
                    panic!(
                        "Predicate {} expects {} arguments, {} given",
                        identifier, predicate.arity(), terms.len()
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

    pub fn transform<F, C, T: Copy>(&mut self, fun: &F, collapse: &C, initial: T) -> T
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

    pub fn rewrite(&mut self, truth: &Formula) -> bool {
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

    pub fn bound(&self, valuation: &HashMap<Identifier, Domain>) -> Formula {
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

    pub fn description(&self) -> &str {
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
