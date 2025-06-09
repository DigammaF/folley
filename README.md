# Folley

Folley is a Rust-based First Order Logic proof assistant. It provides a REPL interface for working with logical formulas, terms, and proof steps interactively.

Folley relies on a built-in extensive deductive apparatus. The working Domain, axioms and goals are defined by the user.

## Prerequisites

- [Rust](https://www.rust-lang.org/tools/install) (latest stable version recommended)

## Building

1. Clone the repository or download the source code.
2. Open a terminal in the project root directory.
3. Build the project using Cargo:

```sh
cargo build --release
```

This will create an optimized executable in the `target/release` directory.

## Running

You can run the project directly with Cargo:

```sh
cargo run
```

Or, after building, run the executable directly:

- On Windows:
  ```sh
  .\target\release\folley.exe
  ```
- On Linux/macOS:
  ```sh
  ./target/release/folley
  ```

## REPL

When you run the program, you will enter an interactive REPL where you can:
- View current theorems and goals
- Enter commands to transform the context

Theorems are what's been proven until now.

Commands work with the current goal only, which is the last goal added.

When there are no more goals, the initial goal(s) can be considered proved.

Commands:
- `instantiate <theorem> with <value>`

  Creates a copy of a theorem with a variable replaced by a value.
  
  For instance, `[0] ∀X.Some(X)`
  becomes `[0] ∀X.Some(X) [1] Some(v)`
  after `instantiate 0 with v`.

  You can also give values to multiple variables with
  `with a, b, c` if the theorem is of the form `∀A.∀B.∀C.Some(A, B, C)`.
  The instantiated theorem will be `Some(a, b, c)`

  Errors out if the outermost layer of the formula is not `∀`, or if the
  specified symbols are not valid values.

- `modus ponens <theorem|G>`

  If the theorem is of the form `A → B`, B is added to theorems and A to goals.
  If `G` is supplied, applies to the current goal: A is added to theorems, and B to goals.

- `rewrite with <theorem>`

  Rewrites the current goal with respect to a given theorem.

- `eval`

  Changes the current goal in two ways:
  - Functions are evaluated
  - Deductive apparatus is applied

- `qed`

  If the current goal is `T`, it is removed from goals,
  and the next goal in the list becomes the current goal.

- `contradict`

  Transforms the current goal by wrapping it in two negations:
  `Some(...)` becomes `⊥⊥Some(...)`.

- `combine <theorem_a> with <theorem_b>`

  Introduces a rewritten version of theorem_a in theorems.

- `simplify <theorem>`

  Introduces an evaluated version of a theorem in theorems.

Follow the on-screen prompts for guidance.

## Apparatus

Take `A ∧ B` for instance. The deductive apparatus will transform it according to the following rules:

- Both are `⊤`: evaluates to `⊤`
- Either is `⊥`: evaluates to `⊥`
- One is `⊤`: evaluates to the other one
- If no rule applies, simply evaluates to `A ∧ B`

The full apparatus can be read in `formula.rs` at `Formula::evaluate`.

## Defining axioms, values, predicates, functions, and goals

Defining axioms, values, predicates, functions and goals is done through modifying `main.rs`.

The `notation` module provides the following helper functions, to make it convenient to construct common logic gates.

```rust
pub fn var(v: &Term) -> Term
fn value(v: Domain) -> Term
fn term(t: &Term) -> Formula
fn imply(a: Formula, b: Formula) -> Formula
fn and(a: Formula, b: Formula) -> Formula
// can also use a & b
fn or(a: Formula, b: Formula) -> Formula
// can also use a | b
fn not(a: Formula) -> Formula
// can also use !a
fn for_all(variable: &Term, f: Formula) -> Formula
fn there_exist(variable: &Term, f: Formula) -> Formula
fn p(identifier: Identifier, arguments: Vec<&Term>) -> Formula
// predicate
fn f(identifier: Identifier, arguments: Vec<&Term>) -> Term
// function
```

However, all the 16 binary logic gates are implemented (alongside the corresponding apparatus transformations)
and can be used by direct construction.

```rust
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
```

Here's an example of defining something that looks like Peano's arithmetic, in order to prove that 1 + 1 = 2.

Please note that the working Domain must be a type that implements `Clone, Debug, PartialEq, Eq`.

```rust
// working on positive integers
type Domain = u128;

fn main() {
    use crate::notation::*;

    let mut scope = Scope::new();
    
    // --- Predicates -----------------------------
    // the '=' predicate
    let eq_id = scope.make_predicate(2, "Eq".into());
    let eq = |a: Term, b: Term| { p(eq_id, vec![&a, &b]) };

    // --- Functions ------------------------------
    // the successor function, computes +1
    let successor_id = scope.make_function(
        1, "S".into(),
        Rc::new(|terms| terms.first().unwrap() + 1)
    );
    let successor = |term: Term| { f(successor_id, vec![&term]) };

    // --- Theorems -------------------------------
    let theorems = vec![
        // --- Axioms -------------------------------------------------------
        // ∀X.Eq(X, X)
        {
            let x = &scope.allocate_silent_variable("X");
            for_all(x, eq(var(x), var(x)))
        },
        // --- Situation ----------------------------------------------------
    ];

    // --- Goals -----------------------------------
    let goals = vec![
        // 2 = 1 + 1
        // Eq(2, S(1))
        eq(value(2), successor(value(1))),
    ];

    // --------------------------------------------
    let mut context = Context { theorems, goals, scope };
    context.mainloop();
}
```

Here's what proving this goal in the REPL looks like:

```
Theorems:
  [0] ∀X.(Eq(X, X))
Goals:
  [0] Eq(2, S(1))
(?) eval
(...) applying Eval
(+) evaluated
Theorems:
  [0] ∀X.(Eq(X, X))
Goals:
  [0] Eq(2, 2)
(?) instantiate 0 with 2
(...) applying Instantiate(0, [2])
(+) instantiated with valuation {1: 2}
Theorems:
  [0] ∀X.(Eq(X, X))
  [1] Eq(2, 2)
Goals:
  [0] Eq(2, 2)
(?) rewrite with 1
(...) applying Rewrite(1)
(+) rewritten
Theorems:
  [0] ∀X.(Eq(X, X))
  [1] Eq(2, 2)
Goals:
  [0] ⊤
(?) qed
(...) applying QED
(+) ∎
All is solved! ^-^
```

## Use of Artificial Intelligence

Parts of the code used to display the formulas on screen is AI generated, and tweeked by hand.

## License

This project is provided as-is for educational and experimental purposes.
