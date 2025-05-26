use std::fmt::{self, Display};


#[derive(Clone, Debug)]
pub struct Predicate {
    arity: usize
}

impl Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Predicate(arity: {})", self.arity)
    }
}

impl Predicate {
    pub fn new(arity: usize) -> Self { Predicate { arity } }

    pub fn arity(&self) -> usize { self.arity }
}
