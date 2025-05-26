use std::rc::Rc;
use std::fmt::{self, Debug, Display};

use crate::term::Term;


#[derive(Clone)]
pub struct Function {
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

impl Function {
    pub fn new(arity: usize, application: Rc<dyn Fn(Vec<Term>) -> Term>) -> Self {
        Function { arity, application }
    }

    pub fn arity(&self) -> usize { self.arity }

    pub fn apply(&self, terms: Vec<Term>) -> Term { (self.application)(terms) }
}
