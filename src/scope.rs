use std::{collections::{HashMap, HashSet}, fmt::{self, Display}, rc::Rc};

use crate::{formula::Formula, function::Function, predicate::Predicate, term::Term, Domain, Identifier};


#[derive(Clone, Debug)]
pub struct Scope {
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
    pub fn new() -> Self {
        Scope {
            last_allocated_id: 0,
            bindings: HashMap::new(),
            variables: HashSet::new(), functions: HashMap::new(),
            predicates: HashMap::new(),
            reprs: HashMap::new(), rev_reprs: HashMap::new()
        }
    }

    pub fn format_term(&self, term: &Term) -> String {
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

    pub fn format_formula(&self, formula: &Formula) -> String {
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

    pub fn is_variable(&self, identifier: &Identifier) -> bool { self.variables.contains(identifier) }
    pub fn is_function(&self, identifier: &Identifier) -> bool { self.functions.contains_key(identifier) }
    pub fn is_predicate(&self, identifier: &Identifier) -> bool { self.predicates.contains_key(identifier) }

    fn allocate(&mut self) -> Identifier {
        if let Some(identifier) = self.last_allocated_id.checked_add(1) {
            self.last_allocated_id = identifier;
            return identifier;
        } else { panic!("Can't allocate: no more space in identifier space"); }
    }

    pub fn bind_repr(&mut self, identifier: Identifier, repr: &str) {
        if let Some(existing_repr) = self.reprs.get(&identifier) { panic!("{identifier} already bound to {existing_repr}, cannot bind to {repr}"); }
        self.reprs.insert(identifier, repr.into());
        self.rev_reprs.insert(repr.into(), identifier);
    }

    pub fn set_id_for_repr(&mut self, repr: &str, identifier: Identifier) {
        if let Some(existing_id) = self.rev_reprs.get(repr) { panic!("{repr} already bound to {existing_id}, cannot bind to {identifier}"); }
        self.rev_reprs.insert(repr.into(), identifier);
    }

    pub fn get_identifier(&self, repr: &str) -> Option<Identifier> { self.rev_reprs.get(repr).cloned() }
    pub fn get_repr(&self, identifier: &Identifier) -> Option<String> { self.reprs.get(identifier).cloned() }

    pub fn allocate_lambda_variable(&mut self) -> Term {
        let identifier = self.allocate();
        self.variables.insert(identifier);
        return Term::Variable(identifier);
    }

    pub fn allocate_silent_variable(&mut self, name: &str) -> Term {
        let identifier = self.allocate();
        self.variables.insert(identifier);
        self.reprs.insert(identifier, name.to_string());
        return Term::Variable(identifier);
    }

    pub fn allocate_variable(&mut self, repr: &str) -> Term {
        let identifier = self.allocate();
        self.variables.insert(identifier);
        self.bind_repr(identifier, repr);
        return Term::Variable(identifier);
    }

    pub fn allocate_lambda_variables(&mut self, count: Identifier) -> Vec<Term> {
        (0..count).map(|_| self.allocate_lambda_variable()).collect()
    }

    pub fn allocate_variables(&mut self, count: Identifier, repr: fn(Identifier) -> String) -> Vec<Term> {
        (0..count).map(|n| self.allocate_variable(&repr(n))).collect()
    }

    pub fn make_predicate(&mut self, arity: usize, repr: &str) -> Identifier {
        let identifier = self.allocate();
        self.predicates.insert(identifier, Predicate::new(arity));
        self.bind_repr(identifier, repr);
        return identifier;
    }

    pub fn make_function(&mut self, arity: usize, repr: &str, application: Rc<dyn Fn(Vec<Domain>) -> Domain>) -> Identifier {
        let identifier = self.allocate();
        self.functions.insert(identifier, Function::new(arity, application));
        self.bind_repr(identifier, repr);
        return identifier;
    }

    pub fn bind(&mut self, variable: Identifier, value: Domain) {
        self.variables.get(&variable).expect(&format!("Can only bind to variable, not {variable}"));
        self.bindings.insert(variable, value);
    }

    pub fn unbind(&mut self, variable: Identifier) {
        self.variables.get(&variable).expect(&format!("Can only unbind from variables, not {variable}"));
        self.bindings.remove(&variable);
    }

    pub fn get_value(&self, variable: &Identifier) -> Option<Domain> {
        self.bindings.get(variable).cloned()
    }

    pub fn get_function(&self, identifier: &Identifier) -> &Function {
        self.functions.get(identifier).expect(&format!("Unknown function: {identifier}"))
    }

    pub fn get_predicate(&self, identifier: &Identifier) -> &Predicate {
        self.predicates.get(identifier).expect(&format!("Unknown predicate: {identifier}"))
    }

    pub fn parse_term(&self, source: &str) -> Result<Term, String> {
        Term::from_parse(self, source)
    }

    pub fn forall<T: Fn(&Term) -> Formula>(&mut self, name: &str, fun: T) -> Formula {
        let identifier = self.allocate();
        self.variables.insert(identifier);
        self.reprs.insert(identifier, name.to_string());
        let variable = Term::Variable(identifier);
        return Formula::ForAll(identifier, Box::new(fun(&variable)));
    }

    pub fn exist<T: Fn(&Term) -> Formula>(&mut self, name: &str, fun: T) -> Formula {
        let identifier = self.allocate();
        self.variables.insert(identifier);
        self.reprs.insert(identifier, name.to_string());
        let variable = Term::Variable(identifier);
        return Formula::ThereExist(identifier, Box::new(fun(&variable)));
    }
}
