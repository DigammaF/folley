# Folley

Folley is a Rust-based logic proof assistant. It provides a REPL interface for working with logical formulas, terms, and proof steps interactively.

Folley limits itself to theories with a finite domain of discourse.

## Prerequisites

- [Rust](https://www.rust-lang.org/tools/install) (latest stable version recommended)

## Building the Project

1. Clone the repository or download the source code.
2. Open a terminal in the project root directory.
3. Build the project using Cargo:

```sh
cargo build --release
```

This will create an optimized executable in the `target/release` directory.

## Running the Project

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
- Enter commands to transform the current context

Theorems are what's been proven until now
Commands work with the current goal only, which is the last goal added
When there are no more goals, the initial goal(s) can be considered proved

Commands:
- `instantiate <theorem> with <value>`
  Create a copy of a theorem with a variable replaced by a value
  
  For instance: `[0] ∀X.Some(X)`
  Becomes: `[0] ∀X.Some(X) [1] Some(v)`
  after `instantiate 0 with v`

  You can also give values to multiple variables with
  `with a, b, c` if the theorem is of the form `∀A.∀B.∀C.Some(A, B, C)`
  The instantiated theorem will be `Some(a, b, c)`

  Errors out if the outermost layer of the formula is not `∀`, or if the
  specified symbols are not valid values

- `modus ponens <theorem>`
  If the theorem is of the form `A → B`, B is added to theorems and A to goals

- `rewrite with <theorem>`
  Rewrite the current goal with respect to a given theorem

- `eval`
  Change the current goal in two ways:
  - Functions are evaluated
  - Deductive apparatus is applied

- `qed`
  If the current goal is `T`, it is removed from goals,
  and the next goal in the list becomes the current goal

- `contradict`
  Transforms the current goal by wrapping it in two negations
  `Some(...)` becomes `⊥⊥Some(...)`

Follow the on-screen prompts for guidance.

## Defining axioms, values, predicates, functions, and goals

## Project Structure

- `src/main.rs`: Main source file containing all logic and REPL implementation
- `Cargo.toml`: Rust project manifest

## License

This project is provided as-is for educational and experimental purposes.
