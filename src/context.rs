use std::{collections::HashMap, fmt::{self, Display}, io::{stdin, stdout, Write}};

use crate::{formula::{BinOp, Formula, TRUE}, operation::Operation, scope::Scope, term::Term, Identifier};


fn read_text(prompt: &str) -> String {
    print!("{prompt}");
    stdout().flush().expect("Could not flush stdout");
    let mut input = String::new();
    stdin().read_line(&mut input).expect("Could not read stdin");
    input = input.trim().to_string();
    input
}

#[derive(Clone, Debug)]
pub struct Context {
    theorems: Vec<Formula>, goals: Vec<Formula>, scope: Scope, mutated: bool
}

impl Display for Context {
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
	pub fn new(theorems: Vec<Formula>, goals: Vec<Formula>, scope: Scope) -> Self {
		Context { theorems, goals, scope, mutated: true }
	}

    pub fn mainloop(&mut self) {
        self.mutated = true;

        while !self.goals.is_empty() {
            if self.mutated { println!("{}", self); self.mutated = false; }
            let command = read_text("(?) ");

            match Operation::parse(&self.scope, &command) {
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

    pub fn solved(&self) -> bool { self.goals.is_empty() }

    fn remove_solved_goals(&mut self) {
        self.goals = self.goals
            .iter().cloned()
            .filter(|goal| goal != &TRUE)
            .collect();
    }

    fn apply(&mut self, operation: Operation) -> Result<String, String> {
        match operation {
            Operation::Instantiate(theorem_key, terms) => {
                let mut theorem = self.theorems.get(theorem_key).ok_or(format!("invalid theorem key: {theorem_key}"))?;
                let mut valuation: HashMap<Identifier, Term> = HashMap::new();

                for value in terms.into_iter() {
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
            Operation::Name(terms) => {
                let mut goal = self.goals.pop().ok_or("no goal in this context")?;
                let backup = goal.clone();
                let mut valuation: HashMap<Identifier, Term> = HashMap::new();

                for term in terms.into_iter() {
                    if let Formula::ThereExist(variable, formula) = goal {
                        valuation.insert(variable, term);
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

                let new_goal = goal.evaluate(&self.scope);
                self.goals.push(new_goal);
                self.mutated = true;
                Ok("evaluated".to_string())
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
                let new_theorem = theorem.evaluate(&self.scope);
                self.theorems.push(new_theorem);
                self.mutated = true;
                Ok("evaluated to a new theorem".to_string())
            }
            Operation::Intro => {
                let mut goal = self.goals.pop().ok_or("no goal in this context")?;
                let mut variables: Vec<String> = vec![];

                while let Formula::ForAll(identifier, inner) = goal {
                    goal = *inner;
                    variables.push(self.scope.format_term(&Term::Variable(identifier)));

                    if let Some(repr) = self.scope.get_repr(&identifier) { self.scope.set_id_for_repr(repr, identifier); }
                }

                self.goals.push(goal);
                if variables.len() > 0 { self.mutated = true; }
                Ok(format!("introduced variables: {variables:?}"))
            }
            Operation::Weaken(theorem_key, new_theorem_binop) => {
                let theorem = self.theorems.get(theorem_key).ok_or(format!("invalid theorem key: {theorem_key}"))?;
                
                if let Ok(theorem_binop) = BinOp::try_from(theorem.clone()) {
                    if theorem_binop.base.weakens_to(&new_theorem_binop) {
                        let new_theorem = Formula::make_from_binop(new_theorem_binop, theorem_binop.a, theorem_binop.b);
                        self.theorems.push(new_theorem.evaluate(&self.scope));
                        self.mutated = true;
                        return Ok("introduced weaker theorem".to_string());
                    } else { return Err(format!("{} cannot be weakened to {}", theorem_binop.base, new_theorem_binop)) }
                } else { return Err(format!("outermost Formula is not a binary operation ({})", theorem.description()).to_string()); }
            }
        }
    }
}
