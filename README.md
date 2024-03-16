# Kind2: a parallel proof & programming language

Kind2 is a general-purpose programming language made from scratch to harness
[HVM](https://github.com/HigherOrderCO/HVM)'s **massive parallelism** and
computational advantages (no garbage collection, optimal β-reduction). Its type
system is a minimal core based on the Calculus of Constructions, making it
inherently secure. In short, Kind2 aims to be:

- As *friendly* as **Python**

- As *efficient* as **Rust**

- As *high-level* as **Haskell**

- As *parallel* as **CUDA**

- As *formal* as **Lean**

And it seeks to accomplish that goal by relying on the solid foundations of [Interaction Combinators](https://www.semanticscholar.org/paper/Interaction-Combinators-Lafont/6cfe09aa6e5da6ce98077b7a048cb1badd78cc76).

## Usage

1. Install [Rust](https://www.rust-lang.org/) and (optionally) [Haskell](https://www.haskell.org/) in your system.

2. Clone this repository and install it:

    ```
    git clone https://github.com/HigherOrderCO/Kind2
    cargo install --path .
    ```

3. Type-check a Kind2 definition:

    ```
    kind2 check name_here
    ```

4. Test it with the interpreter:

    ```
    kind2 run name
    ```

5. Compile and run in parallel, powered by HVM!

    ```
    kind2 compile name
    ./name
    ```

## Syntax

Kind2's syntax aims to be as friendly as Python's, while still exposing the
high-level functional idioms that result in fast, parallel HVM binaries.
Function application (`(f x y z ...)`) follows a Lisp-like style and
pattern-matching `(match x { ctr: .. })` feels like Haskell; but control-flow is
more Python-like. In short, it can be seen as *"Haskell inside, Python
outside"*: a friendly syntax on top of a powerful functional core.

### Functions:

```javascript
// The Fibonacci function
fib (n: U60) : U60 =
  switch n {
    0: 0
    1: 1
    _: (+ (fib (- n 1)) (fib (- n 2)))
  }
```

### Datatypes (ADTs):

```javascript
// Polymorphic Lists
data List T
| cons (head: T) (tail: (List T))
| nil

// Applies a function to all elements of a list
map <A> <B> (xs: (List A)) (f: A -> B) : (List B) =
  fold xs {
    ++: (f xs.head) ++ xs.tail
    []: []
  }
```

### Theorems and Proofs:

```javascript
use Nat/{succ,zero,half,double}

// Proof that `∀n. n*2/2 = n`
bft (n: Nat) : (half (double n)) == n =
  match n {
    succ: (Equal/apply succ (bft n.pred))
    zero: {=}
  }
```

### More Examples:

There are countless examples on the [`Book/`](book) directory. Check it!
