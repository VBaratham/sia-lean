# Article 6: Delta.lean — The Main Theorems

*Corresponds to Bell, Chapter 1.*

This is the heart of the formalization. Everything we built in the previous articles
-- the commutative ring, the field, the constructive order, the Kock-Lawvere axiom --
was scaffolding for the theorems in this file. Here we prove the deepest results of
Smooth Infinitesimal Analysis:

- Infinitesimals are "between 0 and 0" (they are infinitely small)
- Every function R -> R has a unique derivative at every point (microaffinity)
- Delta is non-degenerate (it contains more than just 0)
- LEM (the Law of the Excluded Middle) is refutable
- Microcancellation (a universal cancellation law for infinitesimals)
- Delta is not closed under addition

Let's go line by line.

## Setup

```lean
import SIA.Axioms

universe u

namespace SIA

variable {R : Type u} [SIA R]
open CommRing CField StrictOrder ConstructiveOrderedField
```

By now this preamble should be familiar. We import `SIA.Axioms`, which brings in
everything: the ring, the field, the order, and the Kock-Lawvere axiom. The line
`variable {R : Type u} [SIA R]` says "for the rest of this file, R is some type
equipped with the full SIA structure." The `open` line brings all the lemma names
from our algebraic hierarchy into scope so we can use them without prefixes.

## Negation preserves Delta membership

```lean
theorem neg_delta (d : Delta R) : (-d.val) * (-d.val) = 0 := by
  rw [neg_mul_neg]; exact d.property
```

Recall that `Delta R` is the set of elements whose square is zero: `{ d : R // d * d = 0 }`.
Given any `d` in Delta, we need to show that `-d` also squares to zero. The proof is
one line: `(-d) * (-d)` equals `d * d` by the algebraic identity `(-a)(-b) = ab`
(which we proved as `neg_mul_neg` in Algebra.lean), and `d * d = 0` is exactly the
defining property of Delta membership, accessed as `d.property`.

```lean
instance : Neg (Delta R) where
  neg d := ⟨-d.val, neg_delta d⟩
```

This registers negation as an operation on Delta itself. In Lean, `instance` means
"teach the system that this type supports this operation." The angle brackets
`⟨-d.val, neg_delta d⟩` build a new Delta element: the underlying value is `-d.val`,
and the proof that it squares to zero is `neg_delta d`.

```lean
@[simp]
theorem neg_delta_val (d : Delta R) : (-d).val = -d.val := rfl
```

This is a bookkeeping lemma. It says "the underlying value of `-d` (as a Delta element)
is the same as the negation of the underlying value of `d`." The proof is `rfl`
(reflexivity) because this is true by definition. The `@[simp]` tag tells Lean's
simplifier to use this fact automatically.

## Scaling preserves Delta membership

```lean
theorem mul_delta_sq (d : Delta R) (a : R) : (d.val * a) * (d.val * a) = 0 := by
  have h := d.property
  calc (d.val * a) * (d.val * a)
      = d.val * (a * (d.val * a)) := by rw [mul_assoc]
    _ = d.val * ((a * d.val) * a) := by rw [mul_assoc a]
    _ = d.val * ((d.val * a) * a) := by rw [mul_comm a d.val]
    _ = d.val * (d.val * (a * a)) := by rw [mul_assoc d.val]
    _ = (d.val * d.val) * (a * a) := by rw [mul_assoc]
    _ = 0 * (a * a) := by rw [h]
    _ = 0 := by rw [zero_mul]
```

If `d` is in Delta and `a` is any element of R, then `d * a` is also in Delta. The
idea is simple: `(d*a)^2 = d^2 * a^2 = 0 * a^2 = 0`. But we are working in a
non-commutative-until-proven-commutative setting (actually our ring IS commutative,
but the proof is instructive about how Lean handles algebraic manipulation).

The `calc` block is a chain of equalities. Each step rewrites the expression using
one algebraic law:

1. `(da)(da) = d(a(da))` -- associativity
2. `= d((ad)a)` -- associativity again, grouping the inner `a * (d*a)` as `(a*d) * a`
3. `= d((da)a)` -- commutativity of `a` and `d`
4. `= d(d(aa))` -- associativity, turning `(da)a` into `d(aa)`
5. `= (dd)(aa)` -- associativity, pulling the `d`s together
6. `= 0(aa)` -- substituting `d*d = 0`
7. `= 0` -- zero times anything is zero

The key move is step 3, where we swap `a` and `d` so that the two copies of `d` end
up next to each other, allowing us to use `d * d = 0`.

## Infinitesimals are between 0 and 0

```lean
theorem delta_near_zero (d : Delta R) : (0 : R) ≤ d.val ∧ d.val ≤ 0 := by
```

This is the formal statement that every infinitesimal is "infinitely small." It says
that `d` is both greater-than-or-equal-to 0 AND less-than-or-equal-to 0. In ordinary
math with real numbers, the only number that satisfies both conditions is 0 itself.
But in SIA, Delta elements satisfy both conditions without being provably equal to 0.

Remember from Article 3 that `a ≤ b` is defined as `¬ (b < a)` -- "it is not the case
that b is strictly less than a." So `0 ≤ d` means "d is not strictly negative" and
`d ≤ 0` means "d is not strictly positive." The proof handles each direction separately.

```lean
  constructor
  · -- 0 ≤ d.val, i.e., ¬ (d.val < 0)
    intro h_neg
    have h_pos_neg : (0 : R) < -d.val := neg_pos h_neg
    have h1 : (-d.val) * 0 < (-d.val) * (-d.val) :=
      lt_mul_pos_left h_pos_neg h_pos_neg
    rw [mul_zero, neg_mul_neg] at h1
    rw [d.property] at h1
    exact StrictOrder.lt_irrefl 0 h1
```

For the first half, we assume `d < 0` and derive a contradiction. The reasoning:

1. If `d < 0`, then `-d > 0` (by `neg_pos`).
2. Since `-d > 0`, we can multiply both sides of `0 < -d` by `-d` (a positive number)
   to get `(-d) * 0 < (-d) * (-d)`.
3. The left side simplifies: `(-d) * 0 = 0`.
4. The right side simplifies: `(-d) * (-d) = d * d = 0` (by `neg_mul_neg` and
   `d.property`).
5. So we have `0 < 0`, which contradicts irreflexivity.

```lean
  · -- d.val ≤ 0, i.e., ¬ (0 < d.val)
    intro h_pos
    have h1 : d.val * 0 < d.val * d.val :=
      lt_mul_pos_left h_pos h_pos
    rw [mul_zero, d.property] at h1
    exact StrictOrder.lt_irrefl 0 h1
```

The second half is even simpler. Assume `0 < d`. Since `d` is positive, multiply
both sides of `0 < d` by `d` to get `d * 0 < d * d`. That is, `0 < d * d`. But
`d * d = 0`, so `0 < 0` -- contradiction.

The intuition: an infinitesimal cannot be positive (because then its square would be
positive, but its square is zero). It cannot be negative (because then its negation
would be positive and we get the same contradiction). So it is trapped between 0 and 0,
neither provably positive nor provably negative.

## Microaffinity: every function has a derivative

```lean
theorem microaffinity (f : R → R) (x : R) :
    ExistsUnique fun (a : R) => ∀ (d : Delta R), f (x + d.val) = f x + a * d.val := by
```

This is the bridge between the Kock-Lawvere axiom (which talks about functions on
Delta) and calculus (which talks about functions on all of R). The statement says:
for any function `f : R -> R` and any point `x`, there exists a unique number `a`
such that for all infinitesimals `d`:

    f(x + d) = f(x) + a * d

That number `a` IS the derivative of `f` at `x`. Notice: no limits, no epsilons, no
deltas. You just zoom in on `x` by adding an infinitesimal, and the function is
exactly linear there. Not approximately linear -- *exactly* linear.

```lean
  let g : Delta R → R := fun d => f (x + d.val)
  have hg : g 0 = f x := by simp [g, add_zero]
```

The proof strategy is to reduce this to the Kock-Lawvere axiom. We define a helper
function `g : Delta R -> R` by `g(d) = f(x + d)`. This "shifts" f so that we are
looking at its behavior near `x`. We verify that `g(0) = f(x)` (since `x + 0 = x`).

```lean
  obtain ⟨b, hb, huniq⟩ := SIA.kock_lawvere g
```

Now we apply the Kock-Lawvere axiom to `g`. This gives us:
- `b` : the unique slope
- `hb` : a proof that `g(d) = g(0) + b * d` for all `d` in Delta
- `huniq` : a proof that `b` is the only number with this property

```lean
  exact ⟨b,
    fun d => by
      have := hb d
      rw [hg] at this
      exact this,
    fun y hy => huniq y (fun d => by
      have := hy d
      rw [hg]
      exact this)⟩
```

We return `b` as our witness, along with two proofs. The first proof says `b` works:
for any `d`, we know `g(d) = g(0) + b*d` from Kock-Lawvere, and since `g(0) = f(x)`,
this becomes `f(x + d) = f(x) + b*d`. The second proof says `b` is unique: if some
other `y` also satisfies `f(x + d) = f(x) + y*d` for all `d`, then `g(d) = g(0) + y*d`,
and by the uniqueness clause of Kock-Lawvere, `y = b`.

The elegance here is worth pausing over. In standard calculus, you need to prove that
a limit exists, which requires showing that a certain quantity gets arbitrarily close
to a target. Here, the derivative just *exists* by axiom, for every function, at every
point. And it is unique. This is why SIA is sometimes called "automatic differentiation"
-- not in the computer science sense, but in the mathematical sense that derivatives
are built into the fabric of the number system.

## Delta is non-degenerate

```lean
theorem delta_nondegenerate : ¬ (∀ (x y : Delta R), x.val = y.val) := by
```

This theorem says Delta cannot consist of a single point. If all elements of Delta
were equal (and since 0 is in Delta, that would mean they are all 0), we derive a
contradiction. This is important: if Delta were just {0}, the Kock-Lawvere axiom
would be trivially true (any slope would work when the only infinitesimal is 0) and
we would get no useful information.

```lean
  intro deg
  have d_eq_zero : ∀ (d : Delta R), (0 : R) = d.val := fun d => deg 0 d
```

Assume for contradiction that all Delta elements are equal. Since 0 is in Delta,
every Delta element equals 0.

```lean
  let f : R → R := id
  have micro := microaffinity f 0
```

Consider the identity function `f(x) = x` and apply microaffinity at the point `x = 0`.
This tells us there is a unique `a` such that `f(0 + d) = f(0) + a * d` for all `d`,
i.e., `d = a * d` for all `d` in Delta.

```lean
  have pf_zero : ∀ (d : Delta R), f (0 + d.val) = f 0 + 0 * d.val := by
    intro d; simp [f, zero_add, zero_mul, add_zero]
    exact (d_eq_zero d).symm
```

Here is the trick. If every `d` in Delta is 0, then the equation `f(0 + d) = f(0) + a*d`
becomes `0 = 0 + a*0 = 0`, which is true for ANY value of `a`. In particular, `a = 0`
works: `f(0 + d) = d = 0 = 0 + 0*d = f(0) + 0*d`. (We need `d = 0` here, which is
our degeneracy assumption.)

```lean
  have pf_one : ∀ (d : Delta R), f (0 + d.val) = f 0 + 1 * d.val := by
    intro d; simp [f, zero_add, one_mul]
```

And `a = 1` also works: `f(0 + d) = d = 0 + 1*d = f(0) + 1*d`. This one does NOT
need the degeneracy assumption -- it is always true for the identity function.

```lean
  have h01 : (0 : R) = 1 := micro.unique pf_zero pf_one
  exact absurd h01 (StrictOrder.lt_ne zero_lt_one)
```

But microaffinity says the slope is *unique*. Both 0 and 1 are valid slopes, so
`0 = 1`. However, we know `0 < 1` (from the ordered field axioms), which means
`0 ≠ 1`. Contradiction.

This proof is beautiful in its economy. The identity function has derivative 1
everywhere -- that is obviously true. But if Delta were degenerate, the derivative
would not be unique, because any slope would fit a function evaluated only at a single
point. The uniqueness clause of Kock-Lawvere is what gives Delta its teeth, and
uniqueness is only meaningful when Delta has more than one element.

## Infinitesimals are indistinguishable from zero

```lean
theorem delta_indistinguishable_zero (d : Delta R) : ¬¬ (d.val = 0) := by
  intro h
  have ⟨h_ge, h_le⟩ := delta_near_zero d
  exact (StrictOrder.ne_lt h).elim (fun h_lt => h_ge h_lt) (fun h_gt => h_le h_gt)
```

This says: for any `d` in Delta, it is not the case that `d ≠ 0`. Written in logical
notation: `¬¬(d = 0)`. We cannot prove `d = 0` (that would make Delta degenerate),
but we also cannot prove `d ≠ 0`.

The proof: assume `d ≠ 0` (that is, assume `¬(d = 0)`, which is our `h`). By the
apartness axiom (`ne_lt`), `d ≠ 0` implies `d < 0 ∨ 0 < d`. But `delta_near_zero`
told us `d` is not negative (`0 ≤ d`, i.e., `¬(d < 0)`) and not positive (`d ≤ 0`,
i.e., `¬(0 < d)`). So both branches of the disjunction lead to contradictions.

Think about what this means. An infinitesimal `d` lives in a strange twilight zone:
- We cannot prove `d = 0` (because Delta is non-degenerate)
- We cannot prove `d ≠ 0` (because that would force `d < 0` or `d > 0`, and neither is possible)

This is where constructive logic diverges from classical logic. Classically, for any
number, either it equals zero or it does not. There is no middle ground. In SIA, the
infinitesimals occupy precisely that forbidden middle ground.

## The refutation of LEM

```lean
theorem not_lem_on_delta : ¬ (∀ (d : Delta R), d.val = 0 ∨ d.val ≠ 0) := by
```

This is THE key theorem. It says: it is NOT the case that for every `d` in Delta,
we can decide whether `d = 0` or `d ≠ 0`. The Law of the Excluded Middle (LEM) says
that for any proposition `P`, either `P` or `¬P`. Applied to the proposition `d = 0`,
LEM would give us `d = 0 ∨ d ≠ 0` for every `d`. This theorem says that is false.

Let's walk through the proof very carefully, because the chain of reasoning is the
crown jewel of the formalization.

```lean
  intro lem
```

Assume, for contradiction, that LEM holds on Delta: for every `d`, either `d = 0` or
`d ≠ 0`.

```lean
  have all_zero : ∀ (d : Delta R), d.val = 0 := by
    intro d
    exact (lem d).elim id (fun h => absurd h (delta_indistinguishable_zero d))
```

For any `d` in Delta, LEM gives us two cases:
- Case 1: `d = 0`. Then we are done, `d = 0`.
- Case 2: `d ≠ 0`. But `delta_indistinguishable_zero` says `¬¬(d = 0)`, which means
  `¬(d ≠ 0)`. So `d ≠ 0` contradicts `¬(d ≠ 0)`. This case is impossible.

Either way, `d = 0`. So every element of Delta is zero.

```lean
  have all_eq : ∀ (x y : Delta R), x.val = y.val := by
    intro x y; rw [all_zero x, all_zero y]
```

If every Delta element is 0, then any two Delta elements are equal (they are both 0).

```lean
  exact delta_nondegenerate all_eq
```

But `delta_nondegenerate` says this is impossible. Contradiction.

Here is the chain in full:

1. **Assume LEM** on Delta: every `d` satisfies `d = 0 ∨ d ≠ 0`.
2. **Kill the second case**: `delta_indistinguishable_zero` says `¬(d ≠ 0)`, so the
   `d ≠ 0` branch is always contradictory.
3. **Conclude all `d` are 0**: only the `d = 0` branch survives.
4. **Contradiction**: `delta_nondegenerate` says not all Delta elements are equal.

This is why SIA requires constructive logic. LEM is not just "avoided" or "unused" --
it is *provably false* within the system. If you tried to add LEM as an axiom, you
could derive `False` (a contradiction), making the entire theory inconsistent. The
infinitesimals can only exist in a logical world where some questions ("is this
infinitesimal zero?") genuinely have no answer.

## Microcancellation

```lean
theorem microcancellation {a b : R} (h : ∀ (d : Delta R), a * d.val = b * d.val) : a = b := by
```

This theorem says: if `a * d = b * d` for every infinitesimal `d`, then `a = b`. You
might think this is obvious -- just cancel `d` from both sides. But you cannot divide
by an infinitesimal (they might be zero!). Instead, the proof uses the uniqueness
clause of Kock-Lawvere.

```lean
  let f : Delta R → R := fun d => a * d.val
  have kl := SIA.kock_lawvere f
```

Define `f(d) = a * d`. Apply Kock-Lawvere to get a unique slope for this function.

```lean
  have pf_a : ∀ (d : Delta R), f d = f 0 + a * d.val := by
    intro d; simp [f, mul_zero, zero_add]
```

The slope `a` works: `f(d) = a*d = 0 + a*d = f(0) + a*d`.

```lean
  have pf_b : ∀ (d : Delta R), f d = f 0 + b * d.val := by
    intro d; simp [f, mul_zero, zero_add]; exact h d
```

The slope `b` also works: `f(d) = a*d = b*d = 0 + b*d = f(0) + b*d`. The step
`a*d = b*d` is our hypothesis `h`.

```lean
  exact kl.unique pf_a pf_b
```

By the uniqueness clause of Kock-Lawvere, both slopes must be the same: `a = b`.

This is a powerful cancellation principle. In ordinary algebra, you can cancel a
nonzero factor from both sides of an equation. Here, you cannot cancel a single
infinitesimal (it might be zero), but you can cancel ALL infinitesimals at once. If
two numbers agree when multiplied by every infinitesimal, they must be equal. The
collective behavior of all infinitesimals is enough to distinguish any two distinct
numbers.

## Microstability and the culminating theorem

The rest of the file builds toward a surprising result: Delta is NOT closed under
addition. If `d1` and `d2` are both infinitesimals (both square to zero), it does
NOT follow that `d1 + d2` is also an infinitesimal. The proof is indirect and
involves several intermediate steps.

### Defining microstability

```lean
def Microstable (A : R → Prop) : Prop :=
  ∀ (a : { x : R // A x }), ∀ (d : Delta R), A (a.val + d.val)
```

A property `A` is "microstable" if shifting any element satisfying `A` by any
infinitesimal produces another element satisfying `A`. In other words, `A` is closed
under infinitesimal perturbation. The claim we will prove is that the property
"squares to zero" is NOT microstable.

### Products of infinitesimals are not all zero

```lean
theorem microproduct_not_zero : ¬ (∀ (e n : Delta R), e.val * n.val = 0) := by
  intro h
  have : ∀ (d e : Delta R), d.val = e.val := by
    intro d e
    apply microcancellation
    intro n
    rw [h d n, h e n]
  exact delta_nondegenerate this
```

This intermediate result says: it is NOT the case that the product of any two
infinitesimals is zero. The proof by contradiction is elegant:

1. Assume `e * n = 0` for all `e, n` in Delta.
2. Then for any `d, e` in Delta and any `n` in Delta: `d * n = 0 = e * n`.
3. By microcancellation, `d = e`.
4. So all Delta elements are equal, contradicting `delta_nondegenerate`.

This is somewhat surprising. Each infinitesimal squares to zero, but the product
of two DIFFERENT infinitesimals need not be zero.

### A helper lemma about cancellation

```lean
theorem mul_eq_zero_of_ne_zero {c x : R} (hc : c ≠ 0) (h : c * x = 0) : x = 0 :=
  calc x = 1 * x := by rw [one_mul]
    _ = (c⁻¹ * c) * x := by rw [CField.inv_mul hc]
    _ = c⁻¹ * (c * x) := by rw [mul_assoc]
    _ = c⁻¹ * 0 := by rw [h]
    _ = 0 := by rw [mul_zero]
```

If `c ≠ 0` and `c * x = 0`, then `x = 0`. This is standard algebra: multiply both
sides by `c⁻¹`. We can take the inverse because `c ≠ 0` and we are in a field.
The proof chains the equalities: `x = 1*x = (c⁻¹ * c) * x = c⁻¹ * (c * x) = c⁻¹ * 0 = 0`.

### Delta is not microstable

```lean
theorem delta_not_microstable : ¬ Microstable (fun (r : R) => r * r = 0) := by
  intro h_micro
```

Assume for contradiction that Delta is microstable: for any `a` in Delta and any `d`
in Delta, `(a + d)^2 = 0`.

```lean
  have : ∀ (a b : Delta R), a.val * b.val = 0 := by
    intro a b
    have a_sq := a.property  -- a² = 0
    have b_sq := b.property  -- b² = 0
    have sum_sq : (a.val + b.val) * (a.val + b.val) = 0 := h_micro a b
```

Take any two Delta elements `a` and `b`. We know `a*a = 0`, `b*b = 0`, and (by our
microstability assumption) `(a+b)*(a+b) = 0`.

```lean
    have expand : a.val * a.val + a.val * b.val + (b.val * a.val + b.val * b.val) =
        (a.val + b.val) * (a.val + b.val) := by
      calc a.val * a.val + a.val * b.val + (b.val * a.val + b.val * b.val)
          = a.val * a.val + (a.val * b.val + (b.val * a.val + b.val * b.val)) := by
            rw [add_assoc]
        _ = (a.val * a.val + a.val * b.val) + (b.val * a.val + b.val * b.val) := by
            rw [← add_assoc]
        _ = a.val * (a.val + b.val) + (b.val * a.val + b.val * b.val) := by
            rw [← left_distrib]
        _ = a.val * (a.val + b.val) + b.val * (a.val + b.val) := by
            rw [← left_distrib]
        _ = (a.val + b.val) * (a.val + b.val) := by
            rw [← right_distrib]
```

Now expand `(a+b)^2`. In traditional math you would just write
`(a+b)^2 = a^2 + ab + ba + b^2`. In Lean, we have to justify each step using the
distributive law. The chain works backward: it factors
`a^2 + ab + ba + b^2` back into `(a+b)(a+b)` by collecting terms using `left_distrib`
(which says `a*(b+c) = ab + ac`) and `right_distrib` (which says `(a+b)*c = ac + bc`).

```lean
    rw [sum_sq, a_sq, zero_add, b_sq, add_zero, mul_comm b.val a.val] at expand
```

Now substitute what we know:
- `(a+b)^2 = 0` (from microstability)
- `a^2 = 0` (from Delta membership)
- `b^2 = 0` (from Delta membership)
- `ba = ab` (from commutativity)

After these substitutions, the expanded equation `a^2 + ab + ba + b^2 = (a+b)^2`
becomes `0 + ab + (ab + 0) = 0`, which simplifies to `ab + ab = 0`.

```lean
    have h2 : (1 + 1) * (a.val * b.val) = 0 := by
      rw [right_distrib, one_mul]; exact expand
    exact mul_eq_zero_of_ne_zero two_ne_zero h2
```

Since `ab + ab = (1+1) * ab` (by the distributive law and `1 * ab = ab`), we have
`2 * ab = 0`. Now we use the helper lemma: since `2 ≠ 0` (proved as `two_ne_zero`
in Field.lean -- this is why we needed a field of characteristic not 2!), we can
conclude `ab = 0`.

So microstability would force the product of ANY two infinitesimals to be zero.

```lean
  exact microproduct_not_zero this
```

But we just proved that not all products of infinitesimals are zero
(`microproduct_not_zero`). Contradiction. Therefore Delta is NOT microstable.

### The full chain of reasoning

Let's step back and see the complete argument, because it weaves together nearly
every result in the file:

1. **Assume** Delta is closed under addition (microstable).
2. Then `(a+b)^2 = 0` for any `a, b` in Delta.
3. **Expand**: `a^2 + 2ab + b^2 = 0`. Since `a^2 = 0` and `b^2 = 0`, we get `2ab = 0`.
4. Since `2 ≠ 0` (ordered field), **divide**: `ab = 0` for all `a, b` in Delta.
5. By **microcancellation**, all Delta elements are equal: if `d*n = 0 = e*n` for all
   `n`, then `d = e`.
6. But Delta is **non-degenerate** (because if it were degenerate, the identity function
   would have two different derivatives at the origin, forcing `0 = 1`).
7. **Contradiction**.

This is a remarkable chain. It connects the algebraic structure (characteristic not 2),
the Kock-Lawvere axiom (via microcancellation and non-degeneracy), and the order
structure (via `0 < 1` implying `0 ≠ 1`) into a single argument that the infinitesimals
cannot form a subgroup of R under addition.

## Summary

This file contains the mathematical core of SIA. The key results and their
dependencies:

- **delta_near_zero**: uses the ordered field structure (positive times positive is positive)
- **microaffinity**: a direct corollary of Kock-Lawvere
- **delta_nondegenerate**: uses microaffinity + uniqueness + `0 < 1`
- **delta_indistinguishable_zero**: combines delta_near_zero with apartness
- **not_lem_on_delta**: chains indistinguishability + non-degeneracy
- **microcancellation**: uses Kock-Lawvere uniqueness directly
- **delta_not_microstable**: chains microstability assumption -> all products zero
  (using characteristic not 2) -> all elements equal (using microcancellation) ->
  contradiction (using non-degeneracy)

Every theorem in the hierarchy builds on what came before, and the whole structure
rests on the Kock-Lawvere axiom's uniqueness clause. Existence of the slope gives us
derivatives. Uniqueness of the slope gives us LEM refutation, microcancellation, and
the non-closure of Delta under addition.

In the next articles, we will use microaffinity and microcancellation to build actual
calculus: continuity of all functions, the sum rule, the product rule, and the chain
rule for derivatives.
