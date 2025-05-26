#![allow(dead_code)]

use std::rc::Rc;

use context::Context;
use scope::Scope;
use term::Term;

type Identifier = u8;

mod term;
mod formula;
mod function;
mod predicate;
mod scope;
mod operation;
mod context;

mod notation {
    use crate::{formula::Formula, term::Term, Domain, Identifier};

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

    let even_id = scope.make_predicate(1, "Even".into());
    let even = |a: Term| { p(even_id, vec![&a]) };

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
        // ∀X.(∃Y.2Y = X) -> Even(X)
        for_all(x,
            imply(there_exist(y, eq(product(value(2), var(y)), var(x))),
                even(var(x))
            )
        ),
        // --- Situation ----------------------------------------------------
    ];

    // --- Goals -----------------------------------
    let goals = vec![
        imply(even(var(x)) & even(var(y)),
            even(sum(var(x), var(y)))
        )
    ];

    // --------------------------------------------
    let mut context = Context::new(theorems, goals, scope);
    context.mainloop();
}
