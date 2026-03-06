# Article 1: The Big Picture — What Is This Project?

## What you learned in calculus class

In a standard calculus course, you define the derivative of a function like this:

    f'(x) = lim_{h→0} [f(x+h) - f(x)] / h

This definition involves a *limit* — an infinite process where h gets closer and closer
to 0 but never actually reaches it. You then spend weeks proving that this limit exists
for various functions, that it behaves well under addition, multiplication, composition,
and eventually you build up enough machinery to do useful things.

This works. But it's complicated. The epsilon-delta definition of a limit is famously
hard to internalize, and the proofs are full of estimation arguments ("choose delta =
epsilon / 3...").

## What if h could just *be* zero-ish?

Historically, Newton and Leibniz didn't use limits. They used *infinitesimals* —
quantities that are smaller than any positive number but not zero. They'd write things
like "let dx be an infinitely small quantity" and compute:

    f(x + dx) = f(x) + f'(x) * dx

No limits needed. You just plug in an infinitesimal and read off the derivative.

The problem was that nobody could make this rigorous. What *is* an infinitely small
nonzero number? In the 1800s, Weierstrass replaced infinitesimals with limits, and
that became the standard approach.

But in the 1960s-70s, several mathematicians found ways to make infinitesimals
rigorous after all. One approach is **Smooth Infinitesimal Analysis (SIA)**, developed
by Lawvere, Kock, and others.

## The key idea of SIA

SIA says: there exist elements `d` of our number line where `d * d = 0`, but `d` is
not *provably* equal to zero. These are called **nilsquare infinitesimals**, and the
set of all of them is called **Delta** (written as the Greek letter Delta).

The central axiom — the **Kock-Lawvere axiom** — says:

> Every function from Delta to R is a straight line.

More precisely: for any function `f : Delta -> R`, there exists a *unique* number `b`
such that for all `d` in Delta:

    f(d) = f(0) + b * d

That's it. This single axiom gives you derivatives, makes every function smooth
(infinitely differentiable), and makes every function continuous. No limits, no
epsilons, no deltas.

**"Every function is smooth" — really?** This is a natural point to object: surely
you can define a step function like "f(x) = 1 if x > 0, else 0," and that's not
smooth. The answer is that you *can't* define that function in SIA. A step function
requires deciding, for every x, whether x > 0 or not. But an infinitesimal d is
neither provably positive nor provably negative nor provably zero, so the step
function has no well-defined value at d. The same applies to absolute value, max,
min, and any other function defined by cases on such an undecidable property. SIA
trades the ability to define such functions for a world where everything you *can*
define is automatically smooth. (The next section explains *why* these case splits
are unavailable, and [Article 7](07-continuity.md) returns to this in full detail.)

## The catch: no Law of the Excluded Middle

There's a price. In classical logic, for any proposition P, either P is true or P is
false. This is called the **Law of the Excluded Middle** (LEM). Classical mathematics
uses this everywhere, often without even noticing. Among other things, LEM is what
makes "proof by contradiction" work: to prove P, you assume not-P and derive a
contradiction, concluding P must be true. That reasoning requires that P or not-P are
the only two options.

SIA is *incompatible* with LEM. Here's the intuitive reason: if you could decide, for
every `d` in Delta, whether `d = 0` or `d != 0`, you could prove that Delta = {0}
(that the only nilsquare is zero itself). But the Kock-Lawvere axiom requires Delta to
be bigger than {0}. So LEM must fail.

This is exactly what makes the step function from the previous section impossible to
define. LEM would let you case-split on "x > 0 or not" for every x — including
infinitesimals. Without LEM, that case split is unavailable, and functions like the
step function, absolute value, and max simply cannot be written down.

We don't just avoid LEM as a matter of taste — we actually *prove* that it leads to a
contradiction within SIA. This is one of the theorems in our code
(`not_lem_on_delta`).

## What is Lean?

Lean is a **theorem prover** — a programming language where you state mathematical
theorems and write proofs that a computer checks for correctness. If the code
compiles, the proofs are correct. No human error, no gaps, no hand-waving.

The key concepts you need to know:

- **Types**: Everything in Lean has a type. Numbers have a type (like `Nat` or `R`),
  functions have types (like `R -> R`), and even *propositions* are types (the type
  `a < b` is the type of all proofs that a < b).

- **Terms**: Values that inhabit types. The number 3 is a term of type `Nat`. A proof
  of `a < b` is a term of type `a < b`.

- **Theorems**: A theorem statement is a type. Proving the theorem means constructing
  a term of that type. If Lean accepts your construction, the proof is correct.

- **Classes**: A way to package up a bunch of related axioms. When we write
  `class CommRing R`, we're saying "R is a type that has addition, multiplication,
  etc., satisfying the ring axioms." When we write `[CommRing R]`, we're saying
  "assume R is a commutative ring."

- **Tactics**: Commands that help you construct proofs step by step. `rw [add_comm]`
  rewrites using commutativity of addition. `intro h` introduces a hypothesis. `exact`
  provides the final proof term.

## What is this project?

This project formalizes SIA in Lean 4. We:

1. **Build algebra from scratch** (no external libraries) so we have complete control
   over which logical axioms are used.

2. **Define the SIA axiom system**: a constructive ordered field plus the Kock-Lawvere
   axiom.

3. **Prove the core theorems**: infinitesimals are "near zero" but not provably zero,
   LEM is refutable, every function is continuous, derivatives exist and satisfy the
   usual rules (sum, product, chain rule).

4. **Verify no classical logic is used**: Lean can inspect which foundational axioms a
   theorem depends on. We check that none of our theorems use `Classical.choice`
   (which is the axiom that gives you LEM in Lean).

## The files, in order

The rest of these articles walk through each file line by line:

- **Article 1b: Lean as a Proof Language** — Why propositions are types and proofs are programs
- **Article 2: Algebra.lean** — Building a number system from scratch
- **Article 3: Order.lean** — What does "less than" mean without LEM?
- **Article 4: Field.lean** — Connecting order with arithmetic
- **Article 5: Axioms.lean** — The SIA axioms and the Kock-Lawvere axiom
- **Article 6: Delta.lean** — The main theorems (LEM refutation, microcancellation, etc.)
- **Article 7: Continuity.lean** — Every function is continuous
- **Article 8: Derivative.lean** — Derivatives without limits
- **Article 9: CheckAxioms.lean** — Verifying we never used classical logic
