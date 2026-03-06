# Article 10: HigherOrder.lean --- Higher-Order Infinitesimals

So far, every infinitesimal in the project has been **nilsquare**: an element
`d` whose square is zero. That single condition --- `d * d = 0` --- powered
all of our results. The Kock-Lawvere axiom says every function on nilsquare
infinitesimals is a straight line. From that, we derived derivatives, the sum
rule, the product rule, the chain rule, continuity, and the refutation of LEM.

But there is a natural question: what about elements whose *cube* is zero?
Or whose fourth power is zero? In classical calculus, Taylor's theorem gives
you a polynomial approximation of degree `n` by looking at higher-order
derivatives. The SIA analogue would say: if you zoom in on a "fatter"
infinitesimal neighborhood --- one where `d^(k+1) = 0` rather than just
`d^2 = 0` --- then every function looks like a polynomial of degree at most
`k`.

This file lays the groundwork for that generalization. It defines
exponentiation by natural numbers, embeds the natural numbers into `R`, and
introduces `Delta_k` --- a hierarchy of infinitesimal sets indexed by their
order of nilpotency. The file is shorter and more infrastructure-focused
than the previous ones. There are no deep theorems here, just careful
definitions and the structural facts that connect them.

---

## Setup

```lean
import SIA.Delta

universe u

namespace SIA

open CommRing
```

We import `SIA.Delta`, which brings in the entire algebraic hierarchy plus
the Kock-Lawvere axiom and all the theorems from Articles 2 through 6. The
`open CommRing` line brings the ring lemma names into scope.

---

## Natural number exponentiation

We need to talk about `d^3`, `d^(k+1)`, and so on. Since we do not use
Mathlib, we have no built-in exponentiation for elements of our ring. So we
define our own.

```lean
def npow {R : Type u} [CommRing R] (a : R) : Nat → R
  | 0 => 1
  | n + 1 => a * npow a n
```

This is our first use of Lean's **pattern-matching recursion** on natural
numbers. The definition says:

- **Base case**: `npow a 0 = 1`. Anything to the zeroth power is 1.
- **Recursive case**: `npow a (n + 1) = a * npow a n`. To compute `a^(n+1)`,
  multiply `a` by `a^n`.

Every natural number is either `0` or `n + 1` for some `n`, so these two
cases cover everything. Lean automatically verifies that the recursion
terminates because `n` is strictly smaller than `n + 1`.

Note the type signature: `npow` takes an element `a` of any `CommRing R` and
a natural number, and returns an element of `R`. The curly braces around
`{R : Type u}` and the square brackets around `[CommRing R]` mean these are
implicit arguments --- Lean infers them from context.

### Basic lemmas

```lean
variable {R : Type u} [SIA R]
open CField StrictOrder ConstructiveOrderedField

@[simp] theorem npow_zero (a : R) : npow a 0 = 1 := rfl
@[simp] theorem npow_succ (a : R) (n : Nat) : npow a (n + 1) = a * npow a n := rfl
```

The `variable` line says everything below works for any type `R` with the
full SIA structure. Then we state the two defining equations as theorems.
Both are proved by `rfl` (reflexivity) because they are literally the
definition --- Lean just unfolds `npow` and sees both sides are identical.
The `@[simp]` tag registers them for the simplifier.

```lean
theorem npow_one (a : R) : npow a 1 = a := by
  show a * npow a 0 = a; rw [npow_zero, mul_one]
```

`a^1 = a`. The proof unfolds the definition: `npow a 1 = a * npow a 0 = a * 1 = a`.
The `show` tactic replaces the goal with a definitionally equal expression
(here, unfolding `npow a 1` to `a * npow a 0`), and then `rw` rewrites
`npow a 0` to `1` and `a * 1` to `a`.

```lean
theorem npow_two (a : R) : npow a 2 = a * a := by
  show a * npow a 1 = a * a; rw [npow_one]
```

`a^2 = a * a`. Same technique: unfold the definition to `a * npow a 1`,
then rewrite `npow a 1` to `a` using the previous lemma.

This lemma is important because our original `Delta` was defined using
`d * d = 0`, not `npow d 2 = 0`. The `npow_two` lemma bridges that gap.

```lean
theorem zero_npow_succ (n : Nat) : npow (0 : R) (n + 1) = 0 := by
  show (0 : R) * npow 0 n = 0; rw [zero_mul]
```

`0^(n+1) = 0` for any `n`. The proof unfolds the definition and uses the
ring axiom `0 * anything = 0`. This is needed later to prove that zero
belongs to every `Delta_k`.

### Induction: a new proof technique

```lean
theorem one_npow (n : Nat) : npow (1 : R) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => show (1 : R) * npow 1 n = 1; rw [ih, mul_one]
```

`1^n = 1` for all `n`. This is our first use of the `induction` tactic in
the project, so let us explain how it works.

The natural numbers are defined inductively: every natural number is either
`zero` or `succ n` (the successor of some other natural number). The
`induction n with` tactic says: "I will prove the statement for all `n` by
handling these two cases separately."

- **`| zero =>`**: The base case. We need to show `npow 1 0 = 1`. By
  definition, `npow 1 0 = 1`, so `rfl` closes the goal.

- **`| succ n ih =>`**: The inductive step. We assume the statement holds
  for `n` (this assumption is called `ih`, the **induction hypothesis**),
  and we prove it for `n + 1`. The goal is `npow 1 (n + 1) = 1`. We unfold
  the definition with `show` to get `1 * npow 1 n = 1`, then rewrite
  `npow 1 n` to `1` using `ih`, and finally rewrite `1 * 1` to `1` using
  `mul_one`.

This is the standard pattern of proof by induction. You prove the base case,
then prove that if the statement holds for `n`, it also holds for `n + 1`.
Lean guarantees this covers all natural numbers.

---

## Embedding natural numbers into R

When we write Taylor's theorem, we will need coefficients like factorials:
`n!`, `1/n!`, and so on. For that, we need to talk about natural numbers
like 2, 3, and 6 as elements of our abstract ring `R`. But `R` is not the
natural numbers --- it is an arbitrary SIA. We need a function that converts
a natural number into the corresponding element of `R`.

```lean
def natCast {R : Type u} [CommRing R] : Nat → R
  | 0 => 0
  | n + 1 => natCast n + 1
```

The definition is recursive, just like `npow`:

- `natCast 0 = 0` (the zero of `R`).
- `natCast (n + 1) = natCast n + 1` (add the multiplicative identity of `R`).

So `natCast 1 = 0 + 1 = 1`, `natCast 2 = (0 + 1) + 1 = 1 + 1`,
`natCast 3 = ((0 + 1) + 1) + 1`, and so on. Each natural number maps to the
result of adding `1` to itself that many times.

### Lemmas

```lean
@[simp] theorem natCast_zero : (natCast 0 : R) = 0 := rfl
@[simp] theorem natCast_succ (n : Nat) : (natCast (n + 1) : R) = natCast n + 1 := rfl
```

The defining equations, registered for the simplifier. Both are `rfl`.

```lean
theorem natCast_one : (natCast 1 : R) = 1 := by
  show (natCast 0 : R) + 1 = 1; rw [natCast_zero, zero_add]
```

`natCast 1 = 1`. Unfold: `natCast 1 = natCast 0 + 1 = 0 + 1 = 1`.

```lean
theorem natCast_two : (natCast 2 : R) = 1 + 1 := by
  show (natCast 1 : R) + 1 = 1 + 1; rw [natCast_one]
```

`natCast 2 = 1 + 1`. Unfold: `natCast 2 = natCast 1 + 1 = 1 + 1`.

These lemmas are infrastructure. They are not deep, but they are necessary.
In future work, `natCast` would be used to express factorial denominators in
Taylor coefficients.

---

## Delta_k: the hierarchy of infinitesimals

Now we arrive at the main definition of the file.

```lean
def Delta_k (R : Type u) [CommRing R] (k : Nat) := { d : R // npow d (k + 1) = 0 }
```

`Delta_k R k` is the set of elements `d` in `R` such that `d^(k+1) = 0`.
The parameter `k` controls the **order of nilpotency**. Let us see what
each value of `k` gives us:

- **`Delta_k R 0`** = `{ d : R // d^1 = 0 }` = `{ d : R // d = 0 }`.
  The only element is zero. This is the trivial case.

- **`Delta_k R 1`** = `{ d : R // d^2 = 0 }`. These are the nilsquare
  infinitesimals --- exactly our original `Delta`.

- **`Delta_k R 2`** = `{ d : R // d^3 = 0 }`. These are the **nilcube**
  infinitesimals. Their cube vanishes, but their square might not.

- **`Delta_k R 3`** = `{ d : R // d^4 = 0 }`. Fourth power vanishes.

And so on. As `k` increases, the condition becomes weaker (a higher power
must vanish), so the set gets *larger*. `Delta_k R 0` is just `{0}`.
`Delta_k R 1` is `Delta`, which we know is non-degenerate. `Delta_k R 2`
contains everything in `Delta_k R 1` plus potentially more elements ---
those whose square is nonzero but whose cube is zero.

Think of it as a sequence of nested neighborhoods around zero:

    {0} = Delta_k 0  ⊆  Delta_k 1  ⊆  Delta_k 2  ⊆  Delta_k 3  ⊆  ...

Each one is a "fatter" infinitesimal neighborhood. The fatter the
neighborhood, the more terms of a Taylor expansion you can see.

### Zero belongs to every Delta_k

```lean
instance (k : Nat) : Zero (Delta_k R k) where
  zero := ⟨0, zero_npow_succ k⟩

@[simp]
theorem Delta_k.zero_val (k : Nat) : (0 : Delta_k R k).val = 0 := rfl
```

Zero is in `Delta_k R k` for every `k`, because `0^(k+1) = 0`. The proof
uses `zero_npow_succ`, which we proved earlier. The `instance` declaration
registers this so that `(0 : Delta_k R k)` works as notation. The `@[simp]`
lemma tells the simplifier that extracting the value of the zero element
gives `0`.

This mirrors exactly what we did for `Delta` in Article 5. The pattern is
the same: define a subtype, show that zero belongs to it, register the zero
as an instance, and add a simp lemma.

---

## Connecting Delta and Delta_k

Mathematically, `Delta` and `Delta_k R 1` are the same set: both consist of
elements whose square is zero. But in Lean, they are different types.
`Delta R` is `{ d : R // d * d = 0 }`, and `Delta_k R 1` is
`{ d : R // npow d 2 = 0 }`. The conditions `d * d = 0` and `npow d 2 = 0`
are the same *mathematically* (since `npow d 2 = d * d`), but they are not
the same *definitionally* in Lean. We need explicit conversion functions.

```lean
def toDelta (d : Delta_k R 1) : Delta R :=
  ⟨d.val, by rw [← npow_two]; exact d.property⟩
```

To convert from `Delta_k R 1` to `Delta R`, we keep the same underlying
value `d.val`. For the proof obligation, we need to show `d.val * d.val = 0`.
We know `npow d.val 2 = 0` (that is `d.property`), and `npow_two` tells us
`npow d.val 2 = d.val * d.val`. The `← npow_two` rewrite goes right-to-left,
replacing `d.val * d.val` with `npow d.val 2` in the goal, and then
`d.property` closes it.

```lean
def fromDelta (d : Delta R) : Delta_k R 1 :=
  ⟨d.val, by rw [npow_two]; exact d.property⟩
```

The reverse direction. We need to show `npow d.val 2 = 0`. Rewrite
`npow d.val 2` to `d.val * d.val` using `npow_two`, then use `d.property`.

```lean
@[simp] theorem toDelta_val (d : Delta_k R 1) : (toDelta d).val = d.val := rfl
@[simp] theorem fromDelta_val (d : Delta R) : (fromDelta d).val = d.val := rfl
```

Both conversions preserve the underlying value. These are `rfl` because
the conversions only change the proof component, not the value.

This kind of bookkeeping is a recurring theme in formal mathematics. Two
types that are "obviously the same" in informal math require explicit
functions to convert between them in Lean. The `toDelta` and `fromDelta`
functions are mathematically trivial --- they are the identity on the
underlying values --- but Lean needs them to reconcile the two different
formulations of "square is zero."

---

## Inclusion: the nested chain

One of the most important structural facts about `Delta_k` is that the sets
form a nested chain: if `d` is in `Delta_k k`, then `d` is also in
`Delta_k (k + 1)`.

```lean
def Delta_k.incl {k : Nat} (d : Delta_k R k) : Delta_k R (k + 1) :=
  ⟨d.val, by show d.val * npow d.val (k + 1) = 0; rw [d.property, mul_zero]⟩
```

The argument is simple. We need to show `d^(k+2) = 0`. By the recursive
definition, `d^(k+2) = d * d^(k+1)`. We know `d^(k+1) = 0` (that is
`d.property`, since `d` is in `Delta_k k`). So `d * d^(k+1) = d * 0 = 0`.

The proof uses `show` to unfold `npow d.val (k + 2)` into
`d.val * npow d.val (k + 1)`, then rewrites `npow d.val (k + 1)` to `0`
using `d.property`, and finishes with `mul_zero`.

This means we can always "promote" an infinitesimal to a higher order. If
your cube vanishes (`Delta_k 2`), then your fourth power also vanishes
(`Delta_k 3`), your fifth power also vanishes (`Delta_k 4`), and so on. The
chain is:

    Delta_k 0  ⊆  Delta_k 1  ⊆  Delta_k 2  ⊆  Delta_k 3  ⊆  ...

Each inclusion is witnessed by the `incl` function.

---

## Every nilsquare infinitesimal is in all higher Delta_k

The inclusion `Delta_k.incl` moves one step up the chain. But our original
nilsquare infinitesimals (from `Delta`) satisfy a much stronger property:
they are in `Delta_k k` for *every* `k >= 1`. If `d^2 = 0`, then
`d^3 = 0`, and `d^4 = 0`, and `d^n = 0` for all `n >= 2`.

```lean
theorem delta_in_delta_k (d : Delta R) (k : Nat) : npow d.val (k + 2) = 0 := by
  induction k with
  | zero =>
    show d.val * npow d.val 1 = 0
    rw [npow_one, d.property]
  | succ n ih =>
    show d.val * npow d.val (n + 2) = 0
    rw [ih, mul_zero]
```

This is our first *real* use of induction in the project. (The `one_npow`
proof earlier used induction too, but for a simpler statement.) Let us trace
through it carefully.

We want to prove: for all natural numbers `k`, `d^(k+2) = 0`.

**Base case** (`k = 0`): We need `d^2 = 0`. Unfold: `d^2 = d * d^1 = d * d`.
And `d * d = 0` is exactly `d.property` --- the defining property of `Delta`.
The proof unfolds `npow d.val 2` to `d.val * npow d.val 1`, rewrites
`npow d.val 1` to `d.val` using `npow_one`, and then the goal is
`d.val * d.val = 0`, which is `d.property`.

**Inductive step** (`k = n + 1`): We assume `d^(n+2) = 0` (this is `ih`,
the induction hypothesis) and we need to show `d^(n+3) = 0`. Unfold:
`d^(n+3) = d * d^(n+2)`. By the induction hypothesis, `d^(n+2) = 0`. So
`d * d^(n+2) = d * 0 = 0`.

The intuition is clear: once a power of `d` is zero, all higher powers are
also zero, because each higher power is `d` times something that is already
zero.

### The wrapper function

```lean
def Delta.toDelta_k (d : Delta R) (k : Nat) : Delta_k R (k + 1) :=
  ⟨d.val, delta_in_delta_k d k⟩
```

This packages the theorem into a conversion function. Given any element `d`
of `Delta` and any natural number `k`, we get an element of `Delta_k R (k+1)`.
The underlying value is `d.val`, and the proof that `d^(k+2) = 0` is
`delta_in_delta_k d k`.

Notice the index: `Delta.toDelta_k` maps into `Delta_k R (k + 1)`, not
`Delta_k R k`. This is because the theorem proves `d^(k+2) = 0`, which is
the membership condition for `Delta_k R (k+1)`. When `k = 0`, we get
`Delta_k R 1`, which is `Delta` itself. When `k = 1`, we get `Delta_k R 2`
(nilcubes). And so on.

---

## What is still to come

This file is infrastructure. It defines the pieces but does not yet state
the axiom that would make them useful. The two missing ingredients are:

### The generalized Kock-Lawvere axiom

The original Kock-Lawvere axiom says: every function `f : Delta -> R` is
affine. That is, `f(d) = f(0) + b * d` for a unique `b`. The generalized
version would say: every function `f : Delta_k R k -> R` is a polynomial of
degree at most `k`. That is:

    f(d) = a_0 + a_1 * d + a_2 * d^2 + ... + a_k * d^k

for unique coefficients `a_0, a_1, ..., a_k`. When `k = 1`, this reduces to
the original axiom (a polynomial of degree at most 1 is an affine function).
When `k = 2`, it says every function on nilcube infinitesimals is a quadratic.

This is a natural generalization. In the original axiom, all terms of degree
2 and above vanish because `d^2 = 0`. In the generalized axiom for
`Delta_k k`, all terms of degree `k+1` and above vanish because
`d^(k+1) = 0`. What remains is a polynomial of degree at most `k`.

### Taylor's theorem

With the generalized Kock-Lawvere axiom, Taylor's theorem becomes an
algebraic identity rather than an approximation. In classical calculus,
Taylor's theorem says:

    f(x + h) = f(x) + f'(x) * h + (1/2) * f''(x) * h^2 + ... + remainder

The remainder term is a nuisance --- you need to bound it, argue that it
goes to zero, and handle convergence issues. In SIA, if `h` is in
`Delta_k k`, then `h^(k+1) = 0`, which means the "remainder" is exactly
zero. The Taylor expansion becomes an exact equality:

    f(x + d) = f(x) + f'(x) * d + (1/2!) * f''(x) * d^2 + ... + (1/k!) * f^(k)(x) * d^k

No approximation, no remainder, no convergence argument. This is why we need
`natCast` --- to express the factorial denominators `1/2!`, `1/3!`, etc. as
elements of `R`.

The infrastructure in this file --- `npow` for the powers of `d`, `natCast`
for the coefficients, and `Delta_k` for the domain --- is exactly what would
be needed to state and prove this generalized Taylor theorem.

---

## Summary

This file adds three pieces of infrastructure to the project:

1. **`npow`**: Exponentiation by natural numbers, defined by recursion.
   `npow a 0 = 1`, `npow a (n+1) = a * npow a n`. Basic lemmas for special
   cases and a proof by induction that `1^n = 1`.

2. **`natCast`**: Embedding natural numbers into `R`. `natCast 0 = 0`,
   `natCast (n+1) = natCast n + 1`. Needed for expressing coefficients in
   polynomial expansions.

3. **`Delta_k`**: The hierarchy of higher-order nilpotent infinitesimals.
   `Delta_k R k = { d : R // d^(k+1) = 0 }`. Comes with conversions to and
   from the original `Delta`, an inclusion `Delta_k k -> Delta_k (k+1)`, and
   a proof that every nilsquare infinitesimal belongs to all higher levels.

The file also introduces two Lean proof techniques that had not appeared
before: pattern-matching recursion (for defining `npow` and `natCast`) and
the `induction` tactic (for proving `one_npow` and `delta_in_delta_k`).

No deep theorems here --- just the definitions and structural lemmas that
would support a future generalized Kock-Lawvere axiom and Taylor's theorem.
The relationship to the existing development is clean: `Delta_k 1` is
exactly `Delta`, the higher levels form a nested chain, and every original
nilsquare infinitesimal lives in all of them.
