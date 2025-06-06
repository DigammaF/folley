use std::rc::Rc;
use std::fmt::{self, Debug, Display};

use crate::Domain;


#[derive(Clone)]
pub struct Function {
    arity: usize, application: Rc<dyn Fn(Vec<Domain>) -> Domain>
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
    pub fn new(arity: usize, application: Rc<dyn Fn(Vec<Domain>) -> Domain>) -> Self {
        Function { arity, application }
    }

    pub fn arity(&self) -> usize { self.arity }

    pub fn apply(&self, terms: Vec<Domain>) -> Domain { (self.application)(terms) }
}
