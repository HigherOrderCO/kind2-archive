# Kind2: a parallel proof & programming language

Kind2 is a minimalist proof language based on [Self
types](https://cse.sc.edu/~pfu/document/papers/rta-tlca.pdf), a simple extension
to the Calculus of Constructions that allows encoding inductive types without a
complex, hardcoded datatype system. It compiles to
[Bend](https://github.com/HigherOrderCO/Bend).

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

## Examples

```javascript
// The Fibonacci function
fib (n: U48) : U48 =
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

There are countless examples on the [`Book/`](book) directory.
