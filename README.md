# Folley

Folley is a Rust-based logic proof assistant. It provides a REPL interface for working with logical formulas, terms, and proof steps interactively.

Folley limits itself to theories with a finite domain of discourse. It relies on an extensive deductive apparatus.

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

  Create a copy of a theorem with a variable replaced by a value.
  
  For instance, `[0] ∀X.Some(X)`
  becomes `[0] ∀X.Some(X) [1] Some(v)`
  after `instantiate 0 with v`.

  You can also give values to multiple variables with
  `with a, b, c` if the theorem is of the form `∀A.∀B.∀C.Some(A, B, C)`.
  The instantiated theorem will be `Some(a, b, c)`

  Errors out if the outermost layer of the formula is not `∀`, or if the
  specified symbols are not valid values.

- `modus ponens <theorem>`

  If the theorem is of the form `A → B`, B is added to theorems and A to goals.

- `rewrite with <theorem>`

  Rewrite the current goal with respect to a given theorem.

- `eval`

  Change the current goal in two ways:
  - Functions are evaluated
  - Deductive apparatus is applied

- `qed`

  If the current goal is `T`, it is removed from goals,
  and the next goal in the list becomes the current goal.

- `contradict`

  Transforms the current goal by wrapping it in two negations
  `Some(...)` becomes `⊥⊥Some(...)`.

Follow the on-screen prompts for guidance.

## Apparatus

Take `A ∧ B` for instance. The deductive apparatus will transform it according to the following rules:

- Both are `⊤`: evaluates to `⊤`
- Either is `⊥`: evaluates to `⊥`
- One is `⊤`: evaluates to the other one
- If no rule applies, simply evaluates to `A ∧ B`

The full apparatus can be read in `main.rs` at `Formula::evaluate`.

## Defining axioms, values, predicates, functions, and goals

Defining axioms, values, predicates, functions and goals is done through modifying `main.rs`.

Here's an example of defining something that looks like Peano's arithmetic, in order to prove that 1 + 1 = 2.

```rust
use folley::{Formula, Context};

fn main() {
    use crate::notation::*;

    let mut scope = Scope::new();

    // --- Variables ------------------------------
	// a general purpose variable and its string representation
    let x = scope.allocate_variable("X".into());

    // --- Values ---------------------------------
	// restraining ourselves to 'only' 30 naturals (way more than we need though)
	// the closure describes how to name each value
    let naturals = scope.allocate_values(30, |n| n.to_string());
    
    // --- Predicates -----------------------------
	// the '=' predicate
    let eq = scope.make_predicate(2, "Eq".into());

    // --- Functions ------------------------------
	// the successor function, computes +1
    let successor = scope.make_function(
        1, "S".into(),
        Rc::new({
            let naturals = naturals.clone();
            move |terms| {
                let term = terms.first().unwrap();
                let index = naturals.iter().position(|natural| natural == term).expect("Can't process non natural");
                let new_index = index + 1;
                return naturals[new_index].clone();
            }
        })
    );

    // --- Theorems -------------------------------
    let theorems = vec![
        // --- Axioms -------------------------------------------------------
        // ∀X.Eq(X, X)
        for_all(&x, p(eq, vec![&x, &x])),
    ];

    // --- Goals -----------------------------------
    let goals = vec![
        // 2 = 1 + 1
        // Eq(2, S(1))
        p(eq, vec![&naturals[2], &f(successor, vec![&naturals[1]])]),
    ];

    // --------------------------------------------
    let mut context = Context { theorems, goals, scope };
    context.mainloop();
}
```

## Project Structure

- `src/main.rs`: Main source file containing all logic and REPL implementation
- `Cargo.toml`: Rust project manifest

## License

This project is provided as-is for educational and experimental purposes.
