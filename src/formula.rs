use std::{collections::HashMap, fmt::{self, Display}, ops::{BitAnd, BitOr, BitXor, Not}};

use crate::{scope::Scope, term::Term, Identifier};


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
    pub fn evaluate(&self, scope: &Scope) -> Formula {
        match self {
            Formula::Term(term) => Formula::Term(term.evaluate(scope)),
            Formula::Not(inner) => {
                match inner.evaluate(scope) {
                    TRUE => FALSE,
                    FALSE => TRUE,
                    Formula::Not(a) => *a,
                    inner => !inner
                }
            }
            Formula::And(a, b) => {
                let a = a.evaluate(scope);
                let b = b.evaluate(scope);
                match (a, b) {
                    (TRUE, TRUE) => TRUE,
                    (FALSE, _) | (_, FALSE) => FALSE,
                    (TRUE, f) | (f, TRUE) => f,
                    (a, b) => a & b
                }
            }
            Formula::Or(a, b) => {
                let a = a.evaluate(scope);
                let b = b.evaluate(scope);
                match (a, b) {
                    (FALSE, FALSE) => FALSE,
                    (TRUE, _) | (_, TRUE) => TRUE,
                    (FALSE, f) | (f, FALSE) => f,
                    (a, b) => a | b
                }
            }
            Formula::Imply(a, b) => {
                let a = a.evaluate(scope);
                let b = b.evaluate(scope);
                match (a, b) {
                    (FALSE, _) | (_, TRUE) => TRUE,
                    (TRUE, FALSE) => FALSE,
                    (TRUE, f) => f,
                    (a, b) if a == b => TRUE,
                    (a, b) => Formula::Imply(Box::new(a), Box::new(b))
                }
            }
            Formula::Nimply(a, b) => {
                let a = a.evaluate(scope);
                let b = b.evaluate(scope);
                match (a, b) {
                    (FALSE, _) | (_, TRUE) => FALSE,
                    (TRUE, FALSE) => TRUE,
                    (TRUE, f) => f,
                    (a, b) if a == b => FALSE,
                    (a, b) => Formula::Nimply(Box::new(a), Box::new(b))
                }
            }
            Formula::Nand(a, b) => {
                let a = a.evaluate(scope);
                let b = b.evaluate(scope);
                match (a, b) {
                    (TRUE, TRUE) => FALSE,
                    (FALSE, _) | (_, FALSE) => TRUE,
                    (TRUE, f) | (f, TRUE) => !f,
                    (a, b) => Formula::Nand(Box::new(a), Box::new(b))
                }
            }
            Formula::Nor(a, b) => {
                let a = a.evaluate(scope);
                let b = b.evaluate(scope);
                match (a, b) {
                    (FALSE, FALSE) => TRUE,
                    (TRUE, _) | (_, TRUE) => FALSE,
                    (FALSE, f) | (f, FALSE) => !f,
                    (a, b) => Formula::Nor(Box::new(a), Box::new(b))
                }
            }
            Formula::Xor(a, b) => {
                let a = a.evaluate(scope);
                let b = b.evaluate(scope);
                match (a, b) {
                    (TRUE, TRUE) | (FALSE, FALSE) => FALSE,
                    (TRUE, FALSE) | (FALSE, TRUE) => TRUE,
                    (TRUE, f) | (f, TRUE) => !f,
                    (FALSE, f) | (f, FALSE) => f,
                    (a, b) if a == b => FALSE,
                    (a, b) => Formula::Xor(Box::new(a), Box::new(b))
                }
            }
            Formula::Nxor(a, b) => {
                let a = a.evaluate(scope);
                let b = b.evaluate(scope);
                match (a, b) {
                    (TRUE, TRUE) | (FALSE, FALSE) => TRUE,
                    (TRUE, FALSE) | (FALSE, TRUE) => FALSE,
                    (TRUE, f) | (f, TRUE) => f,
                    (FALSE, f) | (f, FALSE) => !f,
                    (a, b) if a == b => TRUE,
                    (a, b) => Formula::Nxor(Box::new(a), Box::new(b))
                }
            }
            Formula::A(a, _) => { a.evaluate(scope) }
            Formula::B(_, b) => { b.evaluate(scope) }
            Formula::NotA(a, _) => { !a.evaluate(scope) }
            Formula::NotB(_, b) => { !b.evaluate(scope) }
            Formula::Rimply(b, a) => {
                let a = a.evaluate(scope);
                let b = b.evaluate(scope);
                match (a, b) {
                    (FALSE, _) | (_, TRUE) => TRUE,
                    (TRUE, FALSE) => FALSE,
                    (TRUE, f) => f,
                    (a, b) if a == b => TRUE,
                    (a, b) => Formula::Rimply(Box::new(b), Box::new(a))
                }
            }
            Formula::Nrimply(a, b) => {
                let a = a.evaluate(scope);
                let b = b.evaluate(scope);
                match (a, b) {
                    (FALSE, _) | (_, TRUE) => FALSE,
                    (TRUE, FALSE) => TRUE,
                    (TRUE, f) => !f,
                    (a, b) if a == b => FALSE,
                    (a, b) => Formula::Nrimply(Box::new(b), Box::new(a))
                }
            }
            Formula::ForAll(identifier, f) => Formula::ForAll(*identifier, Box::new(f.evaluate(scope))),
            Formula::ThereExist(identifier, f) => Formula::ThereExist(*identifier, Box::new(f.evaluate(scope))),
            Formula::Predicate(identifier, terms) => {
                let predicate = scope.get_predicate(identifier);
                
                if predicate.arity() != terms.len() {
                    panic!(
                        "Predicate {} expects {} arguments, {} given",
                        identifier, predicate.arity(), terms.len()
                    );
                }

                let term_values: Vec<Term> = terms.iter().map(|term| term.evaluate(scope)).collect();
                return Formula::Predicate(*identifier, term_values);
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

    pub fn bound(&self, valuation: &HashMap<Identifier, Term>) -> Formula {
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

    pub fn make_from_binop(base: BinOpBase, a: Formula, b: Formula) -> Formula {
        match base {
            BinOpBase::And => Formula::And(Box::new(a), Box::new(b)),
            BinOpBase::Or => Formula::Or(Box::new(a), Box::new(b)),
            BinOpBase::Imply => Formula::Imply(Box::new(a), Box::new(b)),
            BinOpBase::Nimply => Formula::Nimply(Box::new(a), Box::new(b)),
            BinOpBase::Nand => Formula::Nand(Box::new(a), Box::new(b)),
            BinOpBase::Nor => Formula::Nor(Box::new(a), Box::new(b)),
            BinOpBase::Xor => Formula::Xor(Box::new(a), Box::new(b)),
            BinOpBase::Nxor => Formula::Nxor(Box::new(a), Box::new(b)),
            BinOpBase::A => Formula::A(Box::new(a), Box::new(b)),
            BinOpBase::B => Formula::B(Box::new(a), Box::new(b)),
            BinOpBase::NotA => Formula::NotA(Box::new(a), Box::new(b)),
            BinOpBase::NotB => Formula::NotB(Box::new(a), Box::new(b)),
            BinOpBase::Rimply => Formula::Rimply(Box::new(a), Box::new(b)),
            BinOpBase::Nrimply => Formula::Nrimply(Box::new(a), Box::new(b)),
            BinOpBase::True => TRUE,
            BinOpBase::False => FALSE,
        }
    }

    pub fn weakens_to(&self, formula: &Formula) -> Option<bool> {
        if let (Ok(a), Ok(b)) = (BinOp::try_from(self.clone()), BinOp::try_from(formula.clone())) {
            if a.a != b.a || a.b != b.b { return None; }
            return Some(a.base.weakens_to(&b.base));
        } else { return None; }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BinOpBase {
    True, False,
    And, Or, Imply, Nimply, Nand, Nor, Xor, Nxor, A, B, NotA, NotB, Rimply, Nrimply
}

impl Display for BinOpBase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinOpBase::True => "True",
            BinOpBase::False => "False",
            BinOpBase::And => "And",
            BinOpBase::Or => "Or",
            BinOpBase::Imply => "Imply",
            BinOpBase::Nimply => "NegativeImply",
            BinOpBase::Nand => "NegativeAnd",
            BinOpBase::Nor => "NegativeOr",
            BinOpBase::Xor => "ExclusiveOr",
            BinOpBase::Nxor => "NegativeExclusiveOr",
            BinOpBase::A => "A",
            BinOpBase::B => "B",
            BinOpBase::NotA => "NotA",
            BinOpBase::NotB => "NotB",
            BinOpBase::Rimply => "ReverseImply",
            BinOpBase::Nrimply => "NegativeReverseImply",
        };
        write!(f, "{}", s)
    }
}

pub struct BinOp { pub base: BinOpBase, pub a: Formula, pub b: Formula }

impl TryFrom<Formula> for BinOp {
    type Error = ();

    fn try_from(value: Formula) -> Result<Self, Self::Error> {
        match value {
            Formula::And(a, b) => Ok(BinOp { base: BinOpBase::And, a: *a, b: *b }),
            Formula::Or(a, b) => Ok(BinOp { base: BinOpBase::Or, a: *a, b: *b }),
            Formula::Imply(a, b) => Ok(BinOp { base: BinOpBase::Imply, a: *a, b: *b }),
            Formula::Nimply(a, b) => Ok(BinOp { base: BinOpBase::Nimply, a: *a, b: *b }),
            Formula::Nand(a, b) => Ok(BinOp { base: BinOpBase::Nand, a: *a, b: *b }),
            Formula::Nor(a, b) => Ok(BinOp { base: BinOpBase::Nor, a: *a, b: *b }),
            Formula::Xor(a, b) => Ok(BinOp { base: BinOpBase::Xor, a: *a, b: *b }),
            Formula::Nxor(a, b) => Ok(BinOp { base: BinOpBase::Nxor, a: *a, b: *b }),
            Formula::A(a, b) => Ok(BinOp { base: BinOpBase::A, a: *a, b: *b }),
            Formula::B(a, b) => Ok(BinOp { base: BinOpBase::B, a: *a, b: *b }),
            Formula::NotA(a, b) => Ok(BinOp { base: BinOpBase::NotA, a: *a, b: *b }),
            Formula::NotB(a, b) => Ok(BinOp { base: BinOpBase::NotB, a: *a, b: *b }),
            Formula::Rimply(a, b) => Ok(BinOp { base: BinOpBase::Rimply, a: *a, b: *b }),
            Formula::Nrimply(a, b) => Ok(BinOp { base: BinOpBase::Nrimply, a: *a, b: *b }),
            _ => Err(()),
        }
    }
}

impl TryFrom<&str> for BinOpBase {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "and" | "∧" | "&" => Ok(BinOpBase::And),
            "or" | "∨" | "|" => Ok(BinOpBase::Or),
            "imply" | "→" | "->" => Ok(BinOpBase::Imply),
            "nimply" | "↛" | "-/>" => Ok(BinOpBase::Nimply),
            "nand" | "↑" | "!&" => Ok(BinOpBase::Nand),
            "nor" | "↓" | "!|" => Ok(BinOpBase::Nor),
            "xor" | "⊕" | "x|" => Ok(BinOpBase::Xor),
            "nxor" | "⊙" | "!x|" => Ok(BinOpBase::Nxor),
            "a" | "left" => Ok(BinOpBase::A),
            "b" | "right" => Ok(BinOpBase::B),
            "nota" | "!a" | "!left" => Ok(BinOpBase::NotA),
            "notb" | "!b" | "!reight" => Ok(BinOpBase::NotB),
            "rimply" | "←" | "<-" => Ok(BinOpBase::Rimply),
            "nrimply" | "↚" | "</-" => Ok(BinOpBase::Nrimply),
            _ => Err(()),
        }
    }
}

impl BinOpBase {
    pub fn weakens_to(&self, weaker: &BinOpBase) -> bool {
        match self {
            BinOpBase::Nor => match weaker {
                BinOpBase::NotA|BinOpBase::NotB|BinOpBase::Nand|BinOpBase::Nxor|BinOpBase::Imply|BinOpBase::Rimply|BinOpBase::True|BinOpBase::Nor => true,
                _ => false
            },
            BinOpBase::Nrimply => match weaker {
                BinOpBase::NotA|BinOpBase::Xor|BinOpBase::Nand|BinOpBase::B|BinOpBase::Imply|BinOpBase::Or|BinOpBase::True|BinOpBase::Nrimply => true,
                _ => false
            },
            BinOpBase::Nimply => match weaker {
                BinOpBase::NotB|BinOpBase::Xor|BinOpBase::Nand|BinOpBase::A|BinOpBase::Rimply|BinOpBase::Or|BinOpBase::True|BinOpBase::Nimply => true,
                _ => false
            },
            BinOpBase::And => match weaker {
                BinOpBase::Nxor|BinOpBase::B|BinOpBase::Imply|BinOpBase::A|BinOpBase::Rimply|BinOpBase::Or|BinOpBase::True|BinOpBase::And => true,
                _ => false
            },
            BinOpBase::NotA => match weaker {
                BinOpBase::Nand|BinOpBase::Imply|BinOpBase::True|BinOpBase::NotA => true,
                _ => false
            },
            BinOpBase::NotB => match weaker {
                BinOpBase::Nand|BinOpBase::Rimply|BinOpBase::True|BinOpBase::NotB => true,
                _ => false
            }
            BinOpBase::Xor => match weaker {
                BinOpBase::Nand|BinOpBase::Or|BinOpBase::True|BinOpBase::Xor => true,
                _ => false
            },
            BinOpBase::Nxor => match weaker {
                BinOpBase::Imply|BinOpBase::Rimply|BinOpBase::True|BinOpBase::Nxor => true,
                _ => false
            },
            BinOpBase::B => match weaker {
                BinOpBase::Imply|BinOpBase::Or|BinOpBase::True|BinOpBase::B => true,
                _ => false
            }
            BinOpBase::A => match weaker {
                BinOpBase::Rimply|BinOpBase::Or|BinOpBase::True|BinOpBase::A => true,
                _ => false
            },
            BinOpBase::Nand|BinOpBase::Imply|BinOpBase::Rimply|BinOpBase::Or => match weaker {
                BinOpBase::True => true,
                _ if self == weaker => true,
                _ => false
            },
            BinOpBase::False => true,
            BinOpBase::True => matches!(weaker, BinOpBase::True),
        }
    }
}
