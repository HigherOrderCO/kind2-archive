## Kind2's Equality Algorithm

Since Kind2 is based on Self Types, that allows us to dispense a native
datatype system in favor of existing λ-Encodings. We can represent ANY
inductive family by taking the dependent eliminator of that family and
replacing the witness by a self type. For example, Nats are just:

```javascript
Nat
: *
= $self
  ∀(P: ∀(n: Nat) *)
  ∀(succ: ∀(n: Nat) (P (Nat.succ n)))
  ∀(zero: (P Nat.zero))
  (P self)

Nat.succ : ∀(n: Nat) Nat
= λn ~λP λsucc λzero (succ n)

Nat.zero : Nat
= ~λP λsucc λzero zero
```

Notice, though, there are many degrees of recursion in this representation:

1. The Nat.succ constructor stores a Nat.

2. The Nat motive, P, refers to Nat.

3. The Nat constructors Nat.succ and Nat.zero refer to Nat, and vice-versa.

This kind of self-reference is inevitable, because the dependent eliminator
of an inductive datatype refers to the type being eliminated. This truth is
universal: even in langauges like Coq, this effect is present, it is merely
hidden within the type-checker of dependent eliminators.

Since we can't rely on a hard-coded datatype system, that means conversion
checking must be capable of dealing with the degree of mutual recursion seen
in these encodings, otherwise, it would fail to halt. Most dependent type
checkers are NOT capable of handling even simple recursive types; for
example, it is impossible to represent Scott Nats *directly* (without
wrappers) in Coq, Lean, Agda, and even Haskell. Given that the type above is
an *inductive* view of Scott Nats, there would be no hope to type-check it in
existing proof assistants.

In Kind1, the solution we adopted for this was to keep a map of "seen"
equations. If, during the recursion process, we arrive to an equation that we
previously visited, we just return true, short-cutting the recursion. This
approach works, but is also complex and slow. Thankfully, Kind2's approach is
much simpler, faster, but it is also subtler, in the sense we rely on
reductions being performed in a precise order, otherwise it would fall into
infinite recursive limbos. The way it works is straightforward:

```javascript
// Equal
A == B ::=
  If A and B are identical:
    return true
  Otherwise:
    reduce A and B to weak normal
    check if A and B are similar

// Similar
A ~~ B ::=
  check if the fields of A and B are equal

// Identical
A <> B ::=
  check if A and B are "textually" the same
```

So, for example, to check if `(pair 1 4) == (pair 1 (+ 2 2))`, we would first
check of both sides are identical. They're not, as evidenced by the fact they
have different writings. We then reduce A and B to weak normal, and check if 
they're similar. This will recursivelly check if `1 == 1` and `4 == (+ 2 2)`.
The first is already identical. The second becomes identical after a single
reduction. And that's it!

As you can see, this is obvious enough. So, what's the catch? Suppose we
wanted to check a self-encoded type like `(List #U60) == (List Char)`, where
`Char` is just an alias to `#U60`. In this case, we'd have something like:

```javascript
(List #U60) == (List Char)
------------------------------------------------------------------------ // not identical; reduce
$self ∀(P: ∀(x:(List #U60)) *) ... ~~ $self ∀(P: ∀(x:(List Char)) *) ...
------------------------------------------------------------------------ // recurse on components
∀(P: ∀(x:(List #U60)) *) ... == ∀(P: ∀(x:(List Char)) *) ...
------------------------------------------------------------------------ // not identical; reduce
∀(P: ∀(x:(List #U60)) *) ... ~~ ∀(P: ∀(x:(List Char)) *) ...
------------------------------------------------------------------------ // recurse on components
(List #U60) == (List Char)
------------------------------------------------------------------------ // not identical; reduce
... infinite loop ...
```

Now, as inoffensive as this problem may look, solving it often lead us to
undesirable directions. It may be a good exercise to pause here and think
about how you'd solve it. For example, an obvious idea could be to have a
special flag for "constructors" (like `List` and `Char`), and never reduce
these during the equality. This would cause the algorithm to check if both
sides are component-wise equal BEFORE reducing, which would work on this
case. Yet, in other cases where we need to expand a constructor, such as
`(not true) == false`, that would fail. Kind1's approach was a solution,
albeit over-engineered. There are many "wrong" ways one might approach this
problem, that inevitably lead to complexity bloat and alterations on the
"natural" equality algorithm that inevitably come to bite us later.

So, how do we solve it on Kind2? First, we must note that this algorithm is,
obviously, undecidable in general. So, our first goal must be to cover, at
least, the same set of instances that a classical checker like Coq would. The
algorithm above accomplishes exactly that. After all, if two terms have the same
normal form, this algorithm *will* identify them as equal, as can be easily
seen. Coq only deals with normalizable terms, thus, this already covers the same
set of programs and proofs!

The only problem is how we deal with terms that are NOT expressive in Coq. In
most cases, we don't care! After all, if Kind isn't capable of handling a term
that no other checker would, then it doesn't matter. The problem is, the example
above IS an instance the algorithm above can't handle, and we NEED it to,
because, otherwise, we'd not have a way to encode inductive datatypes! So, how
do we modify our equality checker just enough to make it not drown in that
specific case, without making it complex, slow or, worse, wrong?

First, notice that this problem is non-existant in existing proof checkers,
because they can NOT reduce `(List #U60)` further; `List` is an axiom. Sadly, we
can **not** prevent it from unrolling in Kind, since this mechanism is necessary
to check constructors properly (otherwise, `λP λt λf t :: Bool` would be a
`non-function-application`). So, it is unavoidable that self-types will,
depending on the situation, unroll during conversion checking. 

**As such, what we need is not a mechanism to block reduction, but a mechanism
to undo a reduction.**

In general, this looks like a terrible idea and a massive complication. But, for
self-types specifically, there is a quite straight-forward way to do it: **just
annotate the `self` binder**! For example, `List` would be written as:

```javascript
List = λT
  $(self: (List T))
  ∀(P: ∀(xs: (List T)) *)
  ∀(cons: ∀(head: T) ∀(tail: (List T)) (P (List.cons T head tail)))
  ∀(nil: (P (List.nil T)))
  (P self)
```

This looks like a small redundancy, but it allows us to modify the `similar`
algorithm to do exactly that: "undo" the reduction on the `self` case. That is,
instead of:

```
($x A) ~~ ($y B) ::= (A x) == (B y)
```

We have:

```
($(x:X) A) ~~ ($(y:Y) B) ::= X ~~ Y
```
Note that we do NOT recurse to `==` (equality), but to `~~` (similarity), which
will NOT reduce `X` and `Y` and will, instead, check each component separately.
This simple change effectively gives a mechanism for the conversion checker to
move from the complex expansion of a self-type to its compact applicative form,
and proceed to compare it component-wise.

This is correct, because type constructors are injective, so, no false positive
can occur by doing this; it merely provides the checker a simpler route. Yet,
this WILL result in a false negative: two "identical" self-types (such as `Bit`
and `Bool`) will no longer pass the type-checker, because it will **not** try
expanding these references. Which may even be seen as a feature, as it gives us
a `newtype` functionality for free. (Note that a checker must not give false
positives; false negatives are fine.)

This article turned out to be way more verbose, but this is a big problem that
deserves to be documented in details. Not in the sense that it is hard, but in
the sense that it is really easy to get wrong; so much that Kind1 operated for
years with an inefficient solution that was one of its one of its main
drawbacks. So, I'm glad to have made some progress in that front, and the new
approach looks promising. Now, this all is just for conversion checking; now, on
to actual unification. 💀
