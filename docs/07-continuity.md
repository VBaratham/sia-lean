# Article 7: Continuity.lean — Every Function Is Continuous

*Corresponds to Bell, Chapter 1.*

## The punchline, up front

In a standard calculus course, continuity is something you *check*. You are given a
function, and you have to prove it is continuous — usually via an epsilon-delta argument.
Some functions pass (polynomials, trig functions, exponentials). Some functions fail (the
step function, the Dirichlet function). The world divides into continuous and
discontinuous, and you have to do work to tell them apart.

In Smooth Infinitesimal Analysis, continuity is *free*. Every function from R to R is
continuous. No conditions, no checking, no epsilon-delta argument. This article walks
through `SIA/Continuity.lean`, which proves this theorem in about 30 lines.

But before we get to the main theorem, the file builds up an elegant definition of what
"continuous" even means in SIA, and along the way proves a surprising fact: the natural
notion of "closeness" in SIA is reflexive and symmetric, but *not* transitive.

## What continuity means in traditional calculus

Recall the standard epsilon-delta definition:

> A function f is continuous at a point x if for every epsilon > 0, there exists a
> delta > 0 such that whenever |y - x| < delta, we have |f(y) - f(x)| < epsilon.

In words: you can make f(y) as close to f(x) as you like, by making y close enough
to x. The "as close as you like" part is the epsilon. The "close enough" part is the
delta. The definition is notoriously tricky because of all the quantifier alternation —
"for every epsilon, there exists a delta, such that for all y..."

SIA replaces this entire apparatus with something much simpler.

## What continuity means in SIA

In SIA, two points are "neighbors" if their difference is an infinitesimal — a nilsquare
element of Delta. A function is continuous if it preserves the neighbor relation: if x
and y are neighbors, then f(x) and f(y) are neighbors.

No epsilons, no deltas, no quantifier alternation. Just: "infinitely close inputs
produce infinitely close outputs."

## The Neighbors relation

Here is the definition:

```lean
def Neighbors (a b : R) : Prop := (a - b) * (a - b) = 0
```

`Neighbors a b` holds when `(a - b)^2 = 0` — that is, when the difference `a - b` is a
nilsquare infinitesimal. Remember from Article 6 that Delta is the set of all elements
whose square is zero. So `Neighbors a b` is saying exactly that `a - b` is in Delta.

Compare this with the classical notion of closeness. In standard analysis, "a is close
to b" is always relative — close *how close?* You need a tolerance epsilon. In SIA,
"a is a neighbor of b" is absolute. There is exactly one notion of closeness: their
difference squares to zero. No tolerance parameter needed.

This is the `def` keyword, which introduces a new definition. Unlike `theorem` (which
states a fact to be proved), `def` gives a name to a concept. Here, `Neighbors` is
defined as a `Prop` — a proposition that may or may not hold for a given pair `(a, b)`.

## neighbors_refl: every point is a neighbor of itself

```lean
theorem neighbors_refl (a : R) : Neighbors a a := by
  show (a - a) * (a - a) = 0
  rw [sub_self, zero_mul]
```

This says: for any `a`, `Neighbors a a` holds. The proof:

1. **`show (a - a) * (a - a) = 0`** — This unfolds the definition of `Neighbors`. The
   `show` tactic replaces the goal with a definitionally equal statement. Since
   `Neighbors a a` is defined as `(a - a) * (a - a) = 0`, this is just making the
   goal explicit.

2. **`rw [sub_self, zero_mul]`** — Two rewrites in sequence. First, `sub_self` rewrites
   `a - a` to `0` (from Algebra.lean: anything minus itself is zero). Then `zero_mul`
   rewrites `0 * 0` to `0`. The goal becomes `0 = 0`, which Lean closes automatically.

This is unsurprising: the difference between a and itself is 0, and 0 is in Delta
(since 0 * 0 = 0). Every point is infinitely close to itself.

## neighbors_symm: the neighbor relation is symmetric

```lean
theorem neighbors_symm {a b : R} (h : Neighbors a b) : Neighbors b a := by
  show (b - a) * (b - a) = 0
  rw [← neg_sub a b, neg_mul_neg]
  exact h
```

If a is a neighbor of b, then b is a neighbor of a. This says: if `(a - b)^2 = 0`,
then `(b - a)^2 = 0`. The proof:

1. **`show (b - a) * (b - a) = 0`** — Unfold the definition. We need to prove
   `(b - a) * (b - a) = 0`.

2. **`rw [← neg_sub a b, neg_mul_neg]`** — Two rewrites. First, `← neg_sub a b`
   rewrites `b - a` as `-(a - b)` (the backward arrow `←` applies the lemma
   right-to-left). After this rewrite, the goal is `(-(a - b)) * (-(a - b)) = 0`.
   Then `neg_mul_neg` rewrites `(-x) * (-y)` as `x * y`, so the goal becomes
   `(a - b) * (a - b) = 0`.

3. **`exact h`** — But `(a - b) * (a - b) = 0` is exactly our hypothesis `h`. Done.

The mathematical content is simple: `b - a = -(a - b)`, so `(b - a)^2 = (-(a - b))^2 =
(a - b)^2`. Squaring absorbs the sign.

So `Neighbors` is reflexive and symmetric. If this were also transitive, it would be an
equivalence relation — a perfectly well-behaved notion of "sameness up to an
infinitesimal." But it is not transitive. And the reason it fails to be transitive is
one of the deepest facts in this formalization.

## neighbors_not_transitive: the big surprise

```lean
theorem neighbors_not_transitive :
    ¬ (∀ {a b c : R}, Neighbors a b → Neighbors b c → Neighbors a c) := by
```

This theorem says: it is *not* the case that `Neighbors` is transitive. If a is near b,
and b is near c, you cannot conclude that a is near c.

This might seem bizarre. If a and b are infinitely close, and b and c are infinitely
close, how can a and c be far apart? The answer has to do with what "infinitely close"
means in SIA. Two points are neighbors when their difference *squares* to zero. But the
*sum* of two nilsquare elements need not be nilsquare. We proved exactly this in Article
6: Delta is not microstable.

Let's walk through the proof step by step.

### The proof strategy

The proof is by contradiction. We assume transitivity holds, derive from it that Delta
is microstable, and then invoke `delta_not_microstable` from Article 6 to get a
contradiction.

```lean
  intro h_trans
  have : Microstable (fun (r : R) => r * r = 0) := by
```

`intro h_trans` assumes transitivity holds. Then we set out to prove `Microstable` for
the property `r * r = 0` — that is, the property that defines membership in Delta.
Recall from Article 6 that `Microstable A` means: for any `a` satisfying `A` and any
`d` in Delta, `a + d` also satisfies `A`. For the property `r * r = 0`, this would mean
Delta is closed under addition by Delta elements.

### Constructing the microstability proof

```lean
    intro ⟨a, ha⟩ d
```

We need to show that for any `a` with `a * a = 0` (i.e., `a` is in Delta) and any `d`
in Delta, we have `(a + d.val) * (a + d.val) = 0`. The `⟨a, ha⟩` destructures the
subtype element into the value `a` and its proof `ha : a * a = 0`. The `d` is a Delta
element.

Now comes the clever construction. We need to show `(a + d)^2 = 0`, which is the same
as saying `a + d` is in Delta, which is the same as saying `Neighbors (a + d) 0`... but
actually the proof takes a slightly indirect route through the neighbor relation.

```lean
    have n_a0 : Neighbors a 0 := by
      show (a - 0) * (a - 0) = 0
      rw [sub_zero]; exact ha
```

**Step 1: a is a neighbor of 0.** Since `a * a = 0` and `a - 0 = a`, we have
`(a - 0)^2 = a^2 = 0`. So `Neighbors a 0`.

```lean
    have n_0neg : Neighbors 0 (-d.val) := by
      show (0 - -d.val) * (0 - -d.val) = 0
      rw [sub_eq_add_neg, neg_neg, zero_add]
      exact d.property
```

**Step 2: 0 is a neighbor of -d.** We need `(0 - (-d))^2 = 0`. The rewrites simplify
`0 - (-d)` step by step: `sub_eq_add_neg` rewrites subtraction as addition of the negation,
giving `0 + -(-d)`. Then `neg_neg` simplifies `-(-d)` to `d`. Then `zero_add` simplifies
`0 + d` to `d`. The goal becomes `d * d = 0`, which is `d.property` — the defining
property of a Delta element.

```lean
    have n_aneg : Neighbors a (-d.val) := h_trans n_a0 n_0neg
```

**Step 3: By transitivity, a is a neighbor of -d.** This is where we use the assumed
transitivity `h_trans`. We have `Neighbors a 0` and `Neighbors 0 (-d)`, so by
transitivity, `Neighbors a (-d)`. This means `(a - (-d))^2 = 0`.

```lean
    show (a + d.val) * (a + d.val) = 0
    have : (a - -d.val) * (a - -d.val) = 0 := n_aneg
    rw [sub_eq_add_neg, neg_neg] at this
    exact this
```

**Step 4: Convert to the form we need.** We have `(a - (-d))^2 = 0`. But
`a - (-d) = a + d` (subtracting a negative is adding). The `rw [sub_eq_add_neg, neg_neg]`
performs this simplification in the hypothesis `this`, turning it into
`(a + d) * (a + d) = 0`, which is exactly what we needed to prove.

### The contradiction

```lean
  exact delta_not_microstable this
```

We have now proved that Delta is microstable (assuming transitivity of Neighbors). But
in Article 6, we proved `delta_not_microstable`: Delta is NOT microstable. This is a
direct contradiction, so the assumption of transitivity must be false.

### Stepping back: why the construction works

The chain of reasoning is:

1. Assume `Neighbors` is transitive.
2. Take any `a` in Delta and any `d` in Delta.
3. Build a chain: `a` is near `0` (because a is in Delta), and `0` is near `-d`
   (because d is in Delta, so -d is too, and 0 - (-d) = d is in Delta).
4. By transitivity: `a` is near `-d`, meaning `(a - (-d))^2 = (a + d)^2 = 0`.
5. So `a + d` is in Delta. Since a and d were arbitrary Delta elements, Delta is closed
   under addition — microstable.
6. But we proved Delta is not microstable. Contradiction.

The use of `-d` as an intermediary is a nice trick. The chain goes `a -- 0 -- (-d)`,
which gives us `a - (-d) = a + d`. The negation converts neighbor-subtraction into the
addition we need for microstability.

## Why isn't neighbors transitive? The intuition

This result deserves some reflection, because it reveals something fundamental about
infinitesimals.

Each individual infinitesimal step is "infinitely small" — so small that it squares to
zero. But two infinitely small steps added together need not be infinitely small in the
same sense. The sum of two nilsquares is not necessarily nilsquare.

Here is an analogy. Imagine you are standing at position 0 on the number line. You take
one infinitesimal step of size d to reach position d. Then you take another infinitesimal
step of size d to reach position 2d. Each step was infinitesimal: d^2 = 0. But the total
displacement is 2d, and (2d)^2 = 4d^2 = 0, so actually in this case 2d is still
nilsquare. The problem arises not because any specific pair of steps breaks things, but
because you cannot guarantee it for *all* pairs. The proof in Article 6 showed that if
Delta were closed under addition, then all products of Delta elements would be zero,
which would force all Delta elements to be equal, contradicting Delta's non-degeneracy.

This connects to something deep about calculus. Integration is the process of adding up
infinitely many infinitesimal pieces to get a finite result. If infinitesimals could
never accumulate — if the neighbor relation were transitive — then you could never
integrate to get anything nonzero. The non-transitivity of `Neighbors` is what makes
integration possible. Infinitesimal steps *can* add up.

## all_continuous: the main theorem

```lean
theorem all_continuous (f : R → R) :
    ∀ (x y : R), Neighbors x y → Neighbors (f x) (f y) := by
```

The statement: for any function `f : R → R`, and any two points x and y, if x and y
are neighbors, then f(x) and f(y) are neighbors. In other words, every function
preserves the neighbor relation. In other other words, every function is continuous.

No hypotheses on f. No smoothness assumption. No boundedness condition. Just: any
function whatsoever.

### Setting up: extracting the infinitesimal

```lean
  intro x y hxy
  let d_val := x - y
  have d_sq : d_val * d_val = 0 := hxy
  let d : Delta R := ⟨d_val, d_sq⟩
```

We introduce the points `x`, `y` and the hypothesis `hxy : Neighbors x y`, which means
`(x - y) * (x - y) = 0`. Then we name the difference `d_val := x - y` and note that
`d_val * d_val = 0` — this is just `hxy` itself. Now we can package `d_val` together
with the proof `d_sq` into a Delta element `d : Delta R`. The angle brackets `⟨d_val,
d_sq⟩` construct a subtype element: a value together with a proof that it satisfies the
subtype predicate.

### Rewriting x in terms of y and d

```lean
  have hx_eq : x = y + d.val := by
    show x = y + (x - y)
    have : y + (x - y) = y + (x + -y) := by rw [sub_eq_add_neg]
    rw [this, add_comm x, ← add_assoc, add_neg, zero_add]
```

This establishes that `x = y + d` — that is, x is obtained from y by adding the
infinitesimal d. The proof just does algebra: `y + (x - y) = y + x - y = x`. The
individual steps are:

- `sub_eq_add_neg` rewrites `x - y` as `x + (-y)`
- `add_comm x` swaps to get `y + (-y + x)`... actually, let's trace more carefully.
  After `rw [this]`, the goal is `x = y + (x + -y)`. Then `add_comm x` makes it
  `x = y + (-y + x)`. Then `← add_assoc` regroups to `x = (y + -y) + x`. Then
  `add_neg` simplifies `y + -y` to `0`. Then `zero_add` simplifies `0 + x` to `x`.
  The goal becomes `x = x`, which Lean closes.

This is a lot of work to prove something "obvious." Remember, we built our algebra from
scratch with no automation library. Every algebraic step must be justified by name. This
is the price of building on a minimal foundation — and the payoff is knowing exactly
which axioms are in play.

### Applying microaffinity

```lean
  obtain ⟨a, ha, _⟩ := microaffinity f y
```

This is the key move. We invoke `microaffinity` from Article 6. Recall what it says:
for any function `f : R → R` and any point `y`, there exists a unique slope `a` such
that for all `d` in Delta:

    f(y + d) = f(y) + a * d

The `obtain ⟨a, ha, _⟩` destructures this existential: `a` is the slope, `ha` is the
proof that `f(y + d) = f(y) + a * d` for all d in Delta, and `_` is the uniqueness
proof (which we don't need here, so we discard it with an underscore).

This is where the Kock-Lawvere axiom does its work. It guarantees that f is "locally
linear" at every point — its behavior on infinitesimal neighborhoods is exactly that of
a straight line.

### Computing f(x) - f(y)

```lean
  have hfd : f x = f y + a * d.val := by rw [hx_eq]; exact ha d
```

Since `x = y + d.val` (from `hx_eq`), we can rewrite `f x` as `f (y + d.val)`, and
then microaffinity tells us this equals `f y + a * d.val`. The `rw [hx_eq]` does the
substitution, and `exact ha d` applies the microaffinity equation to our specific `d`.

```lean
  show (f x - f y) * (f x - f y) = 0
  have diff_eq : f x - f y = a * d.val := by
    calc f x - f y = (f y + a * d.val) - f y := by rw [hfd]
      _ = (f y + a * d.val) + -(f y) := by rw [sub_eq_add_neg]
      _ = (a * d.val + f y) + -(f y) := by rw [add_comm (f y)]
      _ = a * d.val + (f y + -(f y)) := by rw [add_assoc]
      _ = a * d.val + 0 := by rw [add_neg]
      _ = a * d.val := by rw [add_zero]
```

The `show` makes the goal explicit: we need `(f x - f y)^2 = 0`. Then `diff_eq`
establishes that `f x - f y = a * d.val`. The `calc` block is a chain of equalities,
each justified by a single rewrite. It is just simplifying
`(f y + a * d) - f y` down to `a * d` by canceling the `f y` terms. Step by step:
substitute `hfd`, expand subtraction as addition of negation, swap the addition order,
re-associate, cancel `f y + -(f y)` to 0, and drop the `+ 0`.

The mathematical content is trivial: `(f(y) + a*d) - f(y) = a*d`. But again, every
algebraic step must be named explicitly.

### The final computation: (a*d)^2 = 0

```lean
  rw [diff_eq]
  calc (a * d.val) * (a * d.val)
      = a * (d.val * (a * d.val)) := by rw [mul_assoc]
    _ = a * ((d.val * a) * d.val) := by rw [mul_assoc d.val]
    _ = a * ((a * d.val) * d.val) := by rw [mul_comm d.val a]
    _ = a * (a * (d.val * d.val)) := by rw [mul_assoc a]
    _ = a * (a * 0) := by rw [d_sq]
    _ = 0 := by rw [mul_zero, mul_zero]
```

After rewriting with `diff_eq`, the goal is `(a * d.val) * (a * d.val) = 0`. We need
to show that the square of `a * d` is zero.

The idea is simple: rearrange `(a*d)*(a*d)` to isolate `d*d`, which we know is zero.
But the rearrangement requires several steps because our algebra only gives us
associativity and commutativity one step at a time. Let's trace through:

1. `(a * d) * (a * d) = a * (d * (a * d))` — associativity, pulling out the first `a`
2. `= a * ((d * a) * d)` — associativity inside, regrouping `d * (a * d)` as `(d * a) * d`
3. `= a * ((a * d) * d)` — commutativity, swapping `d * a` to `a * d`
4. `= a * (a * (d * d))` — associativity, regrouping `(a * d) * d` as `a * (d * d)`
5. `= a * (a * 0)` — substituting `d * d = 0` (this is `d_sq`, the fact that d is in Delta)
6. `= 0` — `a * 0 = 0`, then `a * 0 = 0` again

The rearrangement is essentially: `(ad)^2 = a^2 * d^2 = a^2 * 0 = 0`. We are using the
fact that R is a commutative ring, so we can freely rearrange products. The `calc` block
just spells out the rearrangement one associativity/commutativity step at a time.

And that's it. We have shown `(f x - f y)^2 = 0`, which means `Neighbors (f x) (f y)`.
Every function preserves the neighbor relation. Every function is continuous.

## The proof at a glance

Here is the entire argument in plain English, without the algebraic bookkeeping:

1. Assume x and y are neighbors, so `x - y` is in Delta.
2. Write `x = y + d` where d is in Delta.
3. By microaffinity (the Kock-Lawvere axiom), `f(y + d) = f(y) + a*d` for some slope a.
4. Therefore `f(x) - f(y) = a*d`.
5. Squaring: `(f(x) - f(y))^2 = (a*d)^2 = a^2 * d^2 = a^2 * 0 = 0`.
6. So `f(x) - f(y)` is in Delta, meaning f(x) and f(y) are neighbors.

The crucial ingredient is step 3: microaffinity, which comes from the Kock-Lawvere
axiom. It tells us that f is locally linear, so the difference `f(x) - f(y)` is a
*scalar multiple* of the infinitesimal `d`. And a scalar multiple of an infinitesimal is
still infinitesimal (a fact we proved as `mul_delta_sq` in Article 6, and which the
`calc` block re-derives directly here).

## Comparing with epsilon-delta continuity

It is worth pausing to appreciate how different this is from the traditional approach.

**Traditional proof that f(x) = x^2 is continuous at a point c:**

> Let epsilon > 0. We need delta > 0 such that |x - c| < delta implies |x^2 - c^2| <
> epsilon. Note that |x^2 - c^2| = |x + c| * |x - c|. If |x - c| < 1, then
> |x| < |c| + 1, so |x + c| < 2|c| + 1. Choose delta = min(1, epsilon / (2|c| + 1)).
> Then |x^2 - c^2| = |x + c| * |x - c| < (2|c| + 1) * delta <= epsilon.

This is a correct proof, but it is doing a lot of estimation and case analysis. You
have to choose delta cleverly, bound intermediate terms, and track inequalities through
multiple steps. And this is for the *simplest* nontrivial example.

**SIA proof that ANY f is continuous:**

> If x and y are neighbors, then x - y = d with d^2 = 0. By microaffinity,
> f(x) - f(y) = a*d. Then (a*d)^2 = a^2 * d^2 = 0. So f(x) and f(y) are neighbors.

One argument. For all functions. No estimation.

The tradeoff is that SIA works in a different logical framework (constructive, no LEM),
and the "functions" in SIA are inherently smooth — there are no discontinuous functions
to worry about, because the axioms forbid them from existing.

## The philosophical picture

In traditional mathematics, the world of functions is vast: continuous ones,
discontinuous ones, differentiable ones, non-differentiable ones, measurable ones, and
so on. You start with the biggest class and impose conditions to narrow down to the
well-behaved functions you actually want to work with.

SIA takes the opposite approach. The axioms (specifically the Kock-Lawvere axiom) are
strong enough that *only* well-behaved functions can exist. Every function is smooth
(infinitely differentiable), and therefore every function is continuous. You don't need
to check — it is built into the fabric of the universe.

This might seem restrictive. Where are the step functions? The absolute value function?
The characteristic function of the rationals? They simply don't exist in SIA. But
this is not a loss for the purposes of calculus. Calculus is fundamentally about smooth
functions — derivatives, integrals, differential equations. The "pathological" functions
of classical analysis (nowhere-differentiable continuous functions, everywhere-
discontinuous measurable functions) are curiosities that have no role in the core
development of calculus. SIA just cuts them out from the start.

The gain is enormous simplicity. Instead of checking hypotheses at every step ("is f
continuous here? is f differentiable here? is the derivative continuous?"), you just
compute. Every function you can write down is automatically smooth, automatically
continuous, and automatically has derivatives of all orders.

## What we've built

This file establishes four results:

- **`Neighbors`** — A definition: two points are neighbors if their difference is in
  Delta (squares to zero).
- **`neighbors_refl`** — Every point is a neighbor of itself.
- **`neighbors_symm`** — The neighbor relation is symmetric.
- **`neighbors_not_transitive`** — The neighbor relation is NOT transitive. Transitivity
  would force Delta to be microstable, which we proved impossible in Article 6.
- **`all_continuous`** — Every function R -> R preserves the neighbor relation. This is
  the SIA version of "every function is continuous."

The next file, `Derivative.lean`, takes the next step: not only is every function
continuous, but every function has a derivative. And the derivative satisfies all the
rules you know from calculus — sum rule, product rule, chain rule — all proved without
limits.
