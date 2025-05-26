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
    pub fn bound(&self, valuation: &HashMap<Identifier, Domain>) -> Term {
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
