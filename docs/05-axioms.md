# Article 5: Axioms.lean — The Heart of Smooth Infinitesimal Analysis

*Corresponds to Bell, Chapter 1 (Principle of Microaffineness).*

Everything we have built so far — commutative rings, fields, strict orders,
constructive ordered fields — has been preparation. This file is where we state
the axioms that make Smooth Infinitesimal Analysis what it is. It is short (45
lines), but every line carries weight.

We will define two things:

1. **Delta** — the set of nilsquare infinitesimals (elements whose square is zero).
2. **The SIA class** — a constructive ordered field equipped with the Kock-Lawvere
   axiom, which says every function on Delta is a straight line.

But before we can state the Kock-Lawvere axiom, we need a piece of logical
machinery that Lean 4 does not provide out of the box.

---

## Preamble

```lean
import SIA.Field

universe u

namespace SIA
```

We import `SIA.Field`, which gives us `ConstructiveOrderedField` — the structure
from Article 4 that combines a field with a well-behaved strict order. The
`universe u` and `namespace SIA` lines are the same boilerplate we have seen
before.

---

## Unique existence: why we need our own definition

```lean
-- Unique existence (not in Lean 4 core)
def ExistsUnique {α : Sort u} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x
```

In everyday math, "there exists a unique x such that P(x)" is so common that
you rarely stop to think about what it means formally. But Lean 4's core library
does not include a definition for it (Lean 3 had one, `∃!`, but it was dropped
in Lean 4). So we define it ourselves.

Let us unpack the definition piece by piece.

`ExistsUnique` takes a predicate `p : α → Prop` — a function that takes a value
of type `α` and returns a proposition. For example, `p` might be "x is even" or
"x squared equals 4."

The definition says `ExistsUnique p` is:

    ∃ x, p x ∧ ∀ y, p y → y = x

Reading this from left to right:

- `∃ x` — there exists some `x`...
- `p x` — such that `x` satisfies `p`...
- `∧` — AND...
- `∀ y, p y → y = x` — for every `y` that also satisfies `p`, `y` must equal
  `x`.

The first part (`p x`) gives you **existence**: at least one witness exists. The
second part (`∀ y, p y → y = x`) gives you **uniqueness**: anything else that
satisfies the same property must be the same as that witness.

Together: exactly one thing satisfies `p`.

The curly braces around `{α : Sort u}` mean `α` is an *implicit* argument —
Lean figures it out from context rather than requiring you to write it out. And
`Sort u` is the most general kind of type, so this definition works for
propositions, natural numbers, elements of a ring, or anything else.

---

## Two helper theorems

The definition alone does not do much. We also need ways to *use* it — to
extract the existence part and the uniqueness part separately.

### Extracting existence

```lean
theorem ExistsUnique.exists {α : Sort u} {p : α → Prop} (h : ExistsUnique p) : ∃ x, p x :=
  let ⟨x, hpx, _⟩ := h
  ⟨x, hpx⟩
```

If you know that `ExistsUnique p` holds (that is, you have a proof `h`), then
in particular `∃ x, p x` holds — at least one witness exists. This theorem
extracts that fact.

The proof destructures `h`. Remember, `h` is a proof that `∃ x, p x ∧ ∀ y, p y → y = x`.
The angle brackets `⟨x, hpx, _⟩` pull it apart:

- `x` is the witness.
- `hpx` is the proof that `p x` holds.
- `_` is the uniqueness part, which we discard (the underscore means "I don't
  need this").

Then `⟨x, hpx⟩` packages `x` and `hpx` back up as a proof of `∃ x, p x`.

### Extracting uniqueness

```lean
theorem ExistsUnique.unique {α : Sort u} {p : α → Prop} (h : ExistsUnique p)
    {a b : α} (ha : p a) (hb : p b) : a = b :=
  let ⟨_, _, huniq⟩ := h
  (huniq a ha).trans (huniq b hb).symm
```

This is the more interesting half. It says: if `ExistsUnique p` holds, and you
have two values `a` and `b` that both satisfy `p`, then `a = b`. This is exactly
the meaning of uniqueness — you cannot have two different things satisfying the
property.

The proof again destructures `h`:

- `_` — the witness (we do not need it by name).
- `_` — the proof that the witness satisfies `p` (also not needed).
- `huniq` — the function `∀ y, p y → y = x`, which says anything satisfying
  `p` must equal the witness `x`.

Now we apply `huniq` to both `a` and `b`:

- `huniq a ha` gives us `a = x` (since `a` satisfies `p`).
- `huniq b hb` gives us `b = x` (since `b` satisfies `p`).

Then `.trans` and `.symm` chain these together: `a = x` and `x = b` (flipping
the second one with `.symm`), giving us `a = b`. This is just transitivity of
equality: if two things are both equal to a third, they are equal to each other.

---

## Why unique existence matters here

You might wonder why we go to the trouble of defining `ExistsUnique` rather
than just using plain existence (`∃`). The answer is that the Kock-Lawvere
axiom — the axiom we are building toward — does not just say "there is a slope."
It says "there is a *unique* slope."

If we only required existence, a function on Delta might have multiple slopes.
Then you could not define "the derivative" of a function, because which slope
would you pick? Uniqueness is what makes the derivative *well-defined*. When we
later prove the sum rule, the product rule, and the chain rule, every step
relies on the fact that the slope is unique.

---

## Delta: the nilsquare infinitesimals

```lean
-- Delta: the set of nilsquare infinitesimals
def Delta (R : Type u) [Mul R] [Zero R] := { d : R // d * d = 0 }
```

This is one of the most important definitions in the entire project. Delta is
the set of **nilsquare infinitesimals** — elements of R whose square is zero.

In traditional mathematical notation, you would write:

    Delta = { d in R : d^2 = 0 }

In Lean, `{ d : R // d * d = 0 }` is a **subtype**. A subtype is a type formed
by taking all elements of some type that satisfy a given property. The syntax
uses a double slash `//` to separate the variable from the condition.

What does an element of `Delta R` actually look like? It is a *pair*:

- **The value**: an element `d` of `R`. You access this with `.val`.
- **The proof**: a proof that `d * d = 0`. You access this with `.property`.

So if you have `δ : Delta R`, then `δ.val` is an element of `R`, and
`δ.property` is a proof that `δ.val * δ.val = 0`.

This is a key pattern in Lean: a subtype bundles data (the value) with evidence
(the proof that the value satisfies the condition). You cannot construct an
element of `Delta R` without providing both pieces.

Notice the typeclass constraints: `[Mul R]` and `[Zero R]`. The definition only
needs multiplication (to write `d * d`) and zero (to state the equation
`d * d = 0`). It does not require the full ring structure, though in practice
we will always use it with a `CommRing` or stronger.

---

## Zero is in Delta

```lean
-- Zero is always in Delta
def Delta.zero (R : Type u) [CommRing R] : Delta R :=
  ⟨0, CommRing.mul_zero 0⟩
```

Zero is a nilsquare infinitesimal because `0 * 0 = 0`. The proof uses
`CommRing.mul_zero 0`, which is the ring axiom that says `a * 0 = 0` for any
`a`, applied to `a = 0`.

The angle brackets `⟨0, CommRing.mul_zero 0⟩` construct a subtype pair: the
value is `0`, and the proof is `CommRing.mul_zero 0`.

So Delta always contains at least one element. The interesting question —
the one that drives all of SIA — is whether Delta contains anything *else*.
Classically, the answer would be no: if `d * d = 0` in a field, then `d = 0`.
But in constructive logic, we cannot prove that. And the Kock-Lawvere axiom
(coming shortly) actually requires Delta to be "big enough" for nontrivial
functions to exist on it.

### Registering zero as an instance

```lean
instance {R : Type u} [CommRing R] : Zero (Delta R) where
  zero := Delta.zero R
```

This `instance` declaration tells Lean's typeclass system that `Delta R` has a
zero element. After this line, you can write `(0 : Delta R)` and Lean knows
what you mean — it is the pair `⟨0, CommRing.mul_zero 0⟩`.

Without this instance, you would have to write `Delta.zero R` every time. The
instance lets you use the familiar `0` notation.

### A simplification lemma

```lean
@[simp]
theorem Delta.zero_val {R : Type u} [CommRing R] : (0 : Delta R).val = 0 := rfl
```

This says: if you take the zero of `Delta R` and extract its underlying value
(with `.val`), you get the zero of `R`. The proof is `rfl` — reflexivity —
because this is true by definition. The `@[simp]` tag tells Lean's
simplification engine to use this fact automatically whenever it encounters
`(0 : Delta R).val`.

---

## Closing the namespace

```lean
end SIA
```

We close the `SIA` namespace before defining the `SIA` class itself. This is a
technical requirement in Lean: you cannot define a class named `SIA` while
inside the `SIA` namespace, because Lean would interpret the name as
`SIA.SIA`. By closing the namespace first, the class gets the clean name `SIA`.

---

## The SIA class: the heart of everything

```lean
-- The SIA class
class SIA (R : Type u) extends ConstructiveOrderedField R where
  kock_lawvere : ∀ (f : SIA.Delta R → R),
    SIA.ExistsUnique fun (b : R) => ∀ (d : SIA.Delta R), f d = f 0 + b * d.val
```

This is the definition that the entire project revolves around. Let us take it
apart very carefully.

### The class declaration

```lean
class SIA (R : Type u) extends ConstructiveOrderedField R where
```

This says: `SIA` is a typeclass for a type `R` that **extends**
`ConstructiveOrderedField R`. In other words, any `R` that is an `SIA` is
automatically a constructive ordered field — it inherits all the ring axioms,
the field operations, and the strict order from Articles 2, 3, and 4. On top
of all that inherited structure, it adds one more thing.

### The Kock-Lawvere axiom

```lean
  kock_lawvere : ∀ (f : SIA.Delta R → R),
    SIA.ExistsUnique fun (b : R) => ∀ (d : SIA.Delta R), f d = f 0 + b * d.val
```

This single axiom is the engine of SIA. Let us read it layer by layer.

**Layer 1: "For any function f from Delta to R..."**

```lean
∀ (f : SIA.Delta R → R),
```

Take *any* function whose input is an element of Delta (a nilsquare
infinitesimal) and whose output is an element of R. No assumptions about
continuity, differentiability, smoothness, or anything else. Just: any function
at all.

**Layer 2: "...there exists a unique b in R..."**

```lean
SIA.ExistsUnique fun (b : R) => ...
```

There exists exactly one element `b` of `R` satisfying the property that
follows. This uses the `ExistsUnique` we defined earlier in this very file.

**Layer 3: "...such that for all d in Delta, f(d) = f(0) + b * d."**

```lean
∀ (d : SIA.Delta R), f d = f 0 + b * d.val
```

For every nilsquare infinitesimal `d`, the value of `f` at `d` equals
`f(0) + b * d`. Here `d.val` extracts the underlying element of `R` from the
subtype `Delta R` (so we can multiply it by `b`, which lives in `R`).

And `f 0` means `f` applied to the zero of `Delta R` — the zero element we
defined and registered earlier with our instance declaration. Since `0` is in
Delta, this is well-typed.

### What this axiom is really saying

In the language of traditional calculus: every function on Delta is **affine**.
An affine function is one of the form `y = mx + c` — a straight line. Here:

- The "c" (y-intercept) is `f(0)`.
- The "m" (slope) is `b`.
- The "x" is `d`.

So the Kock-Lawvere axiom says: if you zoom in to the infinitesimal
neighborhood of zero (that is, if you restrict your attention to Delta), every
function looks like a straight line. There is no curvature, no wobble, no
discontinuity. Just a line.

And the slope `b` of that line is **unique**. There is exactly one number that
works. This is what lets us define the derivative: given any function
`f : Delta R → R`, its derivative at 0 is that unique `b`.

### An example to build intuition

Imagine you have the function `f(x) = x^2` and you want its derivative at some
point `a`. In SIA, you would look at the function `g(d) = f(a + d) = (a + d)^2`
for `d` in Delta. Expanding:

    g(d) = a^2 + 2ad + d^2

But `d` is in Delta, so `d^2 = 0`. Therefore:

    g(d) = a^2 + 2a * d

This is already in the form `g(0) + b * d` with `g(0) = a^2` and `b = 2a`.
The Kock-Lawvere axiom guarantees this `b` is unique, so the derivative of
`x^2` at `a` is `2a`. No limits. No epsilon-delta arguments. The squared term
just *vanishes* because infinitesimals are nilsquare.

### Why uniqueness is the key

If the axiom only said "there exists some b," you could imagine a pathological
situation where `f(d) = f(0) + 3d` AND `f(d) = f(0) + 5d` both hold. That
would mean `3d = 5d` for all `d` in Delta — which is fine if Delta is only
`{0}` (since `3 * 0 = 5 * 0 = 0`). But uniqueness forces Delta to be "big
enough" that different slopes give different functions. This is what the later
file Delta.lean exploits to prove microcancellation: if `a * d = b * d` for
all `d` in Delta, then `a = b`.

Microcancellation is the contrapositive of what we just said. And
microcancellation is what lets us cancel infinitesimals in derivative
calculations, which is something Newton and Leibniz did informally but could
never justify.

---

## Why this is so powerful

In traditional calculus, defining the derivative requires:

1. The concept of a limit.
2. Proving the limit exists for the function in question.
3. An epsilon-delta argument (or equivalent) to handle the "approaches but
   never reaches" issue.

In SIA, none of this is needed. The Kock-Lawvere axiom directly declares that
every function on infinitesimals is linear. The derivative is just the slope
`b` — no limiting process, no estimation, no careful bounding.

This is not a trick or a shortcut. It is a different *foundation*. Classical
calculus builds on the completeness axiom (every bounded increasing sequence has
a limit). SIA builds on the Kock-Lawvere axiom (every function on Delta is
affine). Different axioms, different consequences, but both give you a
fully rigorous theory of calculus.

---

## The philosophical point: axioms vs. theorems

Notice that we are not *proving* the Kock-Lawvere axiom. We are *assuming* it.
The `class SIA` declaration says: "If R is a type where all these things hold
— the ring axioms, the field axioms, the order axioms, AND the Kock-Lawvere
axiom — then we can derive the following consequences."

This is the same relationship that classical calculus has with the completeness
axiom for the real numbers. You do not prove that every bounded increasing
sequence converges — you assume it, and then you derive everything else
(intermediate value theorem, extreme value theorem, etc.) from it.

What makes SIA distinctive is *which* axiom it assumes and *which* axiom it
gives up. Classical analysis assumes completeness and the Law of the Excluded
Middle. SIA assumes the Kock-Lawvere axiom but rejects LEM — and as we will
see in Article 6, rejecting LEM is not a choice but a *consequence*. The
Kock-Lawvere axiom is actually *incompatible* with LEM. If you assume both,
you get a contradiction.

This means SIA is not just a different presentation of the same mathematics.
It is a genuinely different logical world, where some classical theorems fail
and some new theorems become provable. The payoff is that calculus becomes
dramatically simpler: derivatives, continuity, and smoothness all come for
free from one axiom.

---

## What we have after this file

At this point, the full axiom system is in place. We have:

- From Article 2 (Algebra.lean): `CommRing` and `CField` — the algebraic
  structure of a number system with +, *, -, /, and their laws.
- From Article 3 (Order.lean): `StrictOrder` — a well-behaved less-than
  relation, with apartness instead of trichotomy.
- From Article 4 (Field.lean): `ConstructiveOrderedField` — connecting the
  order with the arithmetic.
- From this file: `SIA` — a constructive ordered field plus the Kock-Lawvere
  axiom.

The next articles will *use* this axiom system to derive real theorems:

- **Article 6 (Delta.lean)**: LEM is refutable, infinitesimals are "not not
  zero," and microcancellation holds.
- **Article 7 (Continuity.lean)**: Every function is continuous.
- **Article 8 (Derivative.lean)**: Derivatives exist and satisfy the sum rule,
  product rule, and chain rule.

We have laid the foundation. Now we build on it.
