# Article 4: Field.lean — Connecting Order with Arithmetic

## Where we are

In Article 2, we built `CommRing` (addition, multiplication, negation, and all the
familiar rules) and `CField` (division and inverses). In Article 3, we built
`StrictOrder` (a less-than relation with irreflexivity, transitivity, cotransitivity,
and apartness). But so far these two structures live in separate worlds. We have
numbers that we can add and multiply, and we have an ordering we can compare with, but
nothing connects the two.

Think about the real numbers. You know that if `a < b`, then `a + 5 < b + 5`. You know
that if `c > 0` and `a < b`, then `c * a < c * b`. These aren't consequences of the
ring axioms or the order axioms alone -- they're *compatibility conditions* between
arithmetic and ordering.

That's what `Field.lean` provides: a single class that bundles together the algebra, the
ordering, and three axioms that say they play nicely together. Then it derives a
collection of useful lemmas from those three axioms.

## The imports and setup

```lean
import SIA.Algebra
import SIA.Order

universe u
```

The `import` lines are Lean's module system. `import SIA.Algebra` makes everything from
`Algebra.lean` available -- the `CommRing` class, the `CField` class, and all the
theorems proved there (like `add_left_cancel`, `neg_neg`, `mul_sub`, etc.). Similarly,
`import SIA.Order` brings in `StrictOrder` and its theorems (`lt_trans`, `le_of_lt`,
`lt_cotrans`, etc.).

Imports in Lean are transitive: since `Algebra.lean` doesn't import anything beyond
Lean's core, and `Order.lean` doesn't either, our import tree is simple. But if
`Order.lean` had imported `Algebra.lean`, then `import SIA.Order` alone would have
sufficed here, since we'd get `Algebra` transitively.

The `universe u` line is the same universe variable we've seen in every file. It lets
our definitions work for any type, not just one fixed type.

## The main class

```lean
class ConstructiveOrderedField (R : Type u) extends CField R, StrictOrder R where
  lt_zero_one     : (0 : R) < 1
  lt_add_left     : ∀ {a b : R}, a < b → ∀ (c : R), c + a < c + b
  lt_mul_pos_left : ∀ {a b c : R}, 0 < c → a < b → c * a < c * b
```

This is the heart of the file. Let's break it down.

**`class ConstructiveOrderedField (R : Type u)`** declares a new typeclass. Just as
`CommRing R` meant "R is a commutative ring" and `StrictOrder R` meant "R has an
ordering," `ConstructiveOrderedField R` means "R is a constructive ordered field."

**`extends CField R, StrictOrder R`** is Lean's inheritance mechanism. It says: a
constructive ordered field is automatically a `CField` (so it has `+`, `*`, `-`, `/`,
`⁻¹` and all the ring/field axioms) *and* a `StrictOrder` (so it has `<` with
irreflexivity, transitivity, cotransitivity, and apartness). The `extends` keyword
means we don't have to repeat any of those axioms -- they come along for free.

Then come three new axioms, the glue between arithmetic and ordering:

### Axiom 1: `lt_zero_one`

```lean
lt_zero_one : (0 : R) < 1
```

Zero is strictly less than one. This may seem trivially obvious, but it's doing real
work. It rules out degenerate cases. In a ring where `0 = 1`, everything collapses:
every element equals zero (since `a = a * 1 = a * 0 = 0`). By demanding `0 < 1`, and
since `<` is irreflexive (nothing is less than itself), we're guaranteeing `0 ≠ 1`,
which keeps the field non-trivial.

The `(0 : R)` annotation tells Lean that these are the zero and one of `R`, not of
natural numbers or some other type.

### Axiom 2: `lt_add_left`

```lean
lt_add_left : ∀ {a b : R}, a < b → ∀ (c : R), c + a < c + b
```

If `a < b`, then for any `c`, `c + a < c + b`. In other words, adding the same thing
to both sides preserves strict inequality. The `c` goes on the left -- we'll derive the
right-handed version (`a + c < b + c`) as the first theorem.

Why is this the right axiom? Because ordering should be *translation-invariant*.
Sliding the entire number line left or right shouldn't change which of two numbers is
bigger. If I owe you 3 dollars and you owe me 5, and we both receive 100 dollars, you're
still ahead.

### Axiom 3: `lt_mul_pos_left`

```lean
lt_mul_pos_left : ∀ {a b c : R}, 0 < c → a < b → c * a < c * b
```

If `c` is positive (`0 < c`) and `a < b`, then `c * a < c * b`. Multiplying both sides
by a positive number preserves strict inequality.

Note the restriction: `c` must be positive. If `c` were negative, the inequality would
flip. If `c` were zero, both sides would be zero and you couldn't have a strict
inequality. We only axiomatize the positive case and derive the rest as needed.

Together, these three axioms are the standard compatibility conditions for an ordered
field. They're essentially the same axioms you'd find in any algebra textbook defining
an ordered field, just stated in a form natural for Lean.

## The namespace and variable setup

```lean
namespace ConstructiveOrderedField

variable {R : Type u} [ConstructiveOrderedField R]
open CommRing CField StrictOrder
```

**`namespace ConstructiveOrderedField`** opens a namespace. All theorems defined inside
will have the full name `ConstructiveOrderedField.lt_add_right`,
`ConstructiveOrderedField.le_neg_flip`, etc. But within the namespace, we can refer to
them by their short names.

**`variable {R : Type u} [ConstructiveOrderedField R]`** sets up an implicit context.
Every theorem below will silently accept a type `R` and an instance of
`ConstructiveOrderedField R`. We don't have to write these parameters on every theorem
-- Lean fills them in automatically.

**`open CommRing CField StrictOrder`** is important and worth understanding. Without
this line, to use the theorem that `a + 0 = a`, you'd have to write
`CommRing.add_zero`. With `open CommRing`, you can just write `add_zero`. The `open`
command brings all the names from those namespaces into scope.

This is also why we can freely refer to `lt_trans`, `neg_add`, `add_comm`, `mul_inv`,
`ne_lt`, etc. in the proofs below -- they come from the opened namespaces.

## Derived lemmas: basic order-arithmetic facts

Now come the payoffs. From just three axioms, we derive a whole toolkit.

### `lt_add_right`: adding on the right

```lean
theorem lt_add_right {a b : R} (h : a < b) (c : R) : a + c < b + c := by
  have h1 : c + a < c + b := lt_add_left h c
  rw [add_comm c a, add_comm c b] at h1
  exact h1
```

Our axiom `lt_add_left` puts `c` on the left: `c + a < c + b`. But sometimes we want
it on the right: `a + c < b + c`. The proof is one line of real content:

1. **`have h1 : c + a < c + b := lt_add_left h c`** -- Apply the axiom to get the
   left-handed version. We pass it the proof `h : a < b` and the value `c`.
2. **`rw [add_comm c a, add_comm c b] at h1`** -- Rewrite `c + a` to `a + c` and
   `c + b` to `b + c` inside `h1`, using commutativity of addition. The `at h1` means
   "rewrite in hypothesis h1, not in the goal."
3. **`exact h1`** -- Now `h1` says `a + c < b + c`, which is exactly what we need.

This pattern -- derive the right-handed version from the left-handed one via
commutativity -- appears repeatedly.

### `le_add_left_of`: adding preserves `<=`

```lean
theorem le_add_left_of {a b : R} (h : a ≤ b) (c : R) : c + a ≤ c + b := by
  intro hba
  have : -c + (c + b) < -c + (c + a) := lt_add_left hba (-c)
  rw [← add_assoc, neg_add, zero_add, ← add_assoc, neg_add, zero_add] at this
  exact h this
```

Recall from Article 3 that `a ≤ b` is defined as `¬(b < a)` -- "it's not the case that
`b < a`." To prove `c + a ≤ c + b`, which means `¬(c + b < c + a)`, we assume the
opposite and derive a contradiction. Let's walk through:

1. **`intro hba`** -- We're proving a negation, so we assume the thing being negated.
   Now `hba : c + b < c + a`.
2. **`have : -c + (c + b) < -c + (c + a) := lt_add_left hba (-c)`** -- Add `-c` to
   both sides. Now we have `-c + (c + b) < -c + (c + a)`.
3. **`rw [← add_assoc, neg_add, zero_add, ← add_assoc, neg_add, zero_add] at this`**
   -- A chain of rewrites that simplifies both sides:
   - `← add_assoc` turns `-c + (c + b)` into `(-c + c) + b`
   - `neg_add` turns `(-c + c)` into `0`
   - `zero_add` turns `0 + b` into `b`
   - The same three steps apply to the right side

   After all rewrites, `this` says `b < a`.
4. **`exact h this`** -- But `h` says `a ≤ b`, which means `¬(b < a)`. Applying `h` to
   a proof of `b < a` produces a contradiction (`False`), which proves anything.

### `le_add_right_of`: the right-handed version

```lean
theorem le_add_right_of {a b : R} (h : a ≤ b) (c : R) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]
  exact le_add_left_of h c
```

Same pattern as `lt_add_right`: flip to the left-handed version using commutativity.
This time the `rw` is in the goal (no `at` clause), so it rewrites `a + c` to `c + a`
and `b + c` to `c + b` in what we're trying to prove, and then the left-handed lemma
finishes it.

### `lt_neg_flip`: negation reverses order

```lean
theorem lt_neg_flip {a b : R} (h : a < b) : -b < -a := by
  have h1 : -b + a < -b + b := lt_add_left h (-b)
  rw [neg_add] at h1
  have h2 : (-b + a) + -a < 0 + -a := lt_add_right h1 (-a)
  rw [zero_add, add_assoc, add_neg, add_zero] at h2
  exact h2
```

If `a < b`, then `-b < -a`. Negation flips the inequality. The proof is a nice piece of
algebraic manipulation -- the kind of thing that feels like "obvious" on paper but
requires explicit steps in a proof assistant.

1. **`have h1 : -b + a < -b + b := lt_add_left h (-b)`** -- Start with `a < b`, add
   `-b` to both sides. Get `-b + a < -b + b`.
2. **`rw [neg_add] at h1`** -- The right side `-b + b` simplifies to `0`. Now
   `h1 : -b + a < 0`.
3. **`have h2 : (-b + a) + -a < 0 + -a := lt_add_right h1 (-a)`** -- Add `-a` to both
   sides (on the right this time). Get `(-b + a) + -a < 0 + -a`.
4. **`rw [zero_add, add_assoc, add_neg, add_zero] at h2`** -- Simplify both sides:
   - `zero_add` turns `0 + -a` into `-a`
   - `add_assoc` turns `(-b + a) + -a` into `-b + (a + -a)`
   - `add_neg` turns `a + -a` into `0`
   - `add_zero` turns `-b + 0` into `-b`

   Now `h2 : -b < -a`.
5. **`exact h2`** -- Done.

The proof strategy is: start with `a < b`, add things to isolate `-b` on one side and
`-a` on the other. It's the formalized version of the informal argument "subtract `a`
and `b` from both sides."

### `le_neg_flip`: negation reverses `<=` too

```lean
theorem le_neg_flip {a b : R} (h : a ≤ b) : -b ≤ -a :=
  fun hna => h (by rw [← neg_neg a, ← neg_neg b]; exact lt_neg_flip hna)
```

This is written in "term mode" rather than tactic mode -- there's no `by` at the top
level. Since `-b ≤ -a` means `¬(-a < -b)`, we need a function that takes a proof of
`-a < -b` and produces `False`.

Given `hna : -a < -b`, we need to contradict `h : a ≤ b` (i.e., `¬(b < a)`). The
inner `by` block does this:
- `rw [← neg_neg a, ← neg_neg b]` rewrites the goal from `b < a` to `-(-b) < -(-a)`
  (using the fact that `--x = x`, applied in reverse).
- `exact lt_neg_flip hna` applies the strict version to `-a < -b`, getting
  `-(-b) < -(-a)`.

So we've turned `-a < -b` into `b < a`, which contradicts `h`.

### `neg_lt_zero` and `neg_pos`: signs of negations

```lean
theorem neg_lt_zero {a : R} (h : 0 < a) : -a < 0 := by
  have := lt_neg_flip h; rw [neg_zero] at this; exact this

theorem neg_pos {a : R} (h : a < 0) : 0 < -a := by
  have := lt_neg_flip h; rw [neg_zero] at this; exact this
```

Two quick corollaries of `lt_neg_flip`:
- If `a` is positive, then `-a` is negative. From `0 < a`, `lt_neg_flip` gives
  `-a < -0`, and `neg_zero` simplifies `-0` to `0`.
- If `a` is negative, then `-a` is positive. From `a < 0`, `lt_neg_flip` gives
  `-0 < -a`, and again `neg_zero` cleans up.

### `zero_lt_two`: building up from `0 < 1`

```lean
theorem zero_lt_two : (0 : R) < 1 + 1 := by
  have h1 : (0 : R) < 1 := lt_zero_one
  have h2 : 1 + (0 : R) < 1 + 1 := lt_add_left h1 1
  rw [add_zero] at h2
  exact lt_trans h1 h2
```

We want `0 < 1 + 1`. We don't have a literal `2` -- in this formalization, two is
represented as `1 + 1`. The proof chains two facts:

1. **`h1 : 0 < 1`** -- This is our axiom `lt_zero_one`.
2. **`h2 : 1 + 0 < 1 + 1`** -- Apply `lt_add_left` to `0 < 1` with `c = 1`. This
   gives `1 + 0 < 1 + 1`.
3. **`rw [add_zero] at h2`** -- Simplify `1 + 0` to `1`. Now `h2 : 1 < 1 + 1`.
4. **`exact lt_trans h1 h2`** -- Chain `0 < 1` and `1 < 1 + 1` by transitivity to get
   `0 < 1 + 1`.

This is a small result, but it demonstrates how you build up knowledge in a proof
assistant: even "two is positive" needs a proof from the axioms.

### `two_ne_zero`: two is not zero

```lean
theorem two_ne_zero : (1 + 1 : R) ≠ 0 :=
  Ne.symm (lt_ne zero_lt_two)
```

From `0 < 1 + 1` (proved just above), `lt_ne` (from `StrictOrder`) gives us
`0 ≠ 1 + 1`. Then `Ne.symm` flips it to `1 + 1 ≠ 0`.

This will be crucial later in the development. When we study Delta (the set of
nilsquare infinitesimals), we'll need to divide by 2 to show that Delta is
"non-microstable" -- that it isn't closed under addition. That division requires
knowing `2 ≠ 0`.

## The harder proofs

The last two theorems are substantially more complex than anything above. They involve
reasoning about inverses, case analysis via apartness, and proof by contradiction.

### `one_div_pos_of_pos`: the reciprocal of a positive number is positive

```lean
theorem one_div_pos_of_pos {c : R} (hc : 0 < c) : 0 < 1 / c := by
  have c_ne : c ≠ 0 := Ne.symm (lt_ne hc)
  have inv_ne : c⁻¹ ≠ 0 := CField.inv_ne_zero c_ne
  have one_div_eq : 1 / c = c⁻¹ := by rw [CField.div_eq_mul_inv, one_mul]
  rw [one_div_eq]
  exact (ne_lt inv_ne).elim
    (fun h => by
      have : c * c⁻¹ < c * 0 := lt_mul_pos_left hc h
      rw [CField.mul_inv c_ne, mul_zero] at this
      exact absurd (lt_trans lt_zero_one this) (lt_irrefl 0))
    id
```

This is a key lemma: if `c > 0`, then `1/c > 0`. In classical math, you'd say
"obviously, dividing 1 by a positive gives a positive." But constructively, we can't
just wave our hands. Let's trace through.

**Setup (lines 1-4):**

1. **`c_ne : c ≠ 0`** -- From `0 < c`, we know `0 ≠ c` (by `lt_ne`), and `Ne.symm`
   flips it to `c ≠ 0`. We need this because division and inverses are only
   well-behaved for nonzero elements.
2. **`inv_ne : c⁻¹ ≠ 0`** -- The inverse of a nonzero element is nonzero (proved in
   `Algebra.lean`).
3. **`one_div_eq : 1 / c = c⁻¹`** -- Since `a / b` is defined as `a * b⁻¹`, we get
   `1 / c = 1 * c⁻¹ = c⁻¹`. This lets us work with `c⁻¹` instead of `1 / c`.
4. **`rw [one_div_eq]`** -- Rewrite the goal from `0 < 1 / c` to `0 < c⁻¹`.

**The core argument (lines 5-9):**

Now we need to show `0 < c⁻¹`. We know `c⁻¹ ≠ 0`. This is where apartness (from
Article 3) pays off. The axiom `ne_lt` says: if `a ≠ b`, then `a < b ∨ b < a`. Applied
to `c⁻¹ ≠ 0`, we get `c⁻¹ < 0 ∨ 0 < c⁻¹`.

**`(ne_lt inv_ne).elim`** performs case analysis on this disjunction. The `.elim`
method takes two functions -- one for each case.

**Case 1: `c⁻¹ < 0`** (the `fun h =>` branch). This is the "impossible" case. We
derive a contradiction:
- **`c * c⁻¹ < c * 0`** -- Since `c > 0` and `c⁻¹ < 0`, multiplying `c⁻¹ < 0` by the
  positive number `c` gives `c * c⁻¹ < c * 0`.
- **`rw [CField.mul_inv c_ne, mul_zero] at this`** -- Simplify: `c * c⁻¹ = 1` (that's
  the defining property of an inverse) and `c * 0 = 0`. Now `this : 1 < 0`.
- **`absurd (lt_trans lt_zero_one this) (lt_irrefl 0)`** -- We have `0 < 1`
  (from `lt_zero_one`) and `1 < 0` (from `this`). By transitivity, `0 < 0`. But
  `lt_irrefl` says nothing is less than itself. The `absurd` combinator takes a
  proposition and its negation and produces anything -- in this case, it produces a
  proof of `0 < c⁻¹` (since `False` implies anything).

**Case 2: `0 < c⁻¹`** (the `id` branch). This is exactly what we want to prove. `id`
is the identity function -- it just returns its argument unchanged. If we already have a
proof of `0 < c⁻¹`, we're done.

The elegance here is worth noting. We didn't use the Law of the Excluded Middle. We
used *apartness*: since `c⁻¹ ≠ 0`, we know `c⁻¹ < 0 ∨ 0 < c⁻¹`. This is a
constructive disjunction -- we can actually decide which case holds (or rather, one of
them must provide a proof). We then eliminated the impossible case by contradiction.
This is not the same as classical case splitting; it works because `ne_lt` is an axiom
of our constructive order.

### `le_mul_pos_left`: multiplying by a non-negative number preserves `<=`

```lean
theorem le_mul_pos_left {a b c : R} (hab : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  intro hba
  have c_ne : c ≠ 0 := by
    intro h; rw [h, zero_mul, zero_mul] at hba
    exact lt_irrefl _ hba
  exact (ne_lt c_ne).elim
    (fun c_neg => hc c_neg)
    (fun c_pos => by
      have inv_pos : 0 < c⁻¹ := by
        have : 1 / c = c⁻¹ := by rw [CField.div_eq_mul_inv, one_mul]
        rw [← this]; exact one_div_pos_of_pos c_pos
      have : c⁻¹ * (c * b) < c⁻¹ * (c * a) := lt_mul_pos_left inv_pos hba
      rw [← mul_assoc, CField.inv_mul c_ne, one_mul,
          ← mul_assoc, CField.inv_mul c_ne, one_mul] at this
      exact hab this)
```

This is the most complex proof in the file. We want to show: if `a ≤ b` and `c ≥ 0`,
then `c * a ≤ c * b`. The strict version (`lt_mul_pos_left`) is an axiom, but the
non-strict version requires real work.

Recall that `a ≤ b` means `¬(b < a)` and `0 ≤ c` means `¬(c < 0)`. We need to prove
`c * a ≤ c * b`, i.e., `¬(c * b < c * a)`.

**Step 1: Assume the opposite.**

```lean
intro hba
```

We assume `hba : c * b < c * a` and aim for a contradiction.

**Step 2: Show `c ≠ 0`.**

```lean
have c_ne : c ≠ 0 := by
  intro h; rw [h, zero_mul, zero_mul] at hba
  exact lt_irrefl _ hba
```

If `c` were zero, then `c * b = 0` and `c * a = 0`, so `hba` would say `0 < 0`, which
contradicts irreflexivity. Therefore `c ≠ 0`. (The underscore `_` in `lt_irrefl _`
tells Lean to infer the argument -- it figures out that the argument is `0`.)

**Step 3: Case split on whether `c` is negative or positive.**

```lean
exact (ne_lt c_ne).elim
  (fun c_neg => hc c_neg)
  (fun c_pos => ...)
```

Since `c ≠ 0`, apartness (`ne_lt`) gives us `c < 0 ∨ 0 < c`.

**Case 3a: `c < 0`.** If `c` is negative, then `c_neg : c < 0`. But we assumed
`hc : 0 ≤ c`, which means `¬(c < 0)`. Applying `hc` to `c_neg` gives a contradiction
immediately. That's what `hc c_neg` does -- it applies the negation to the proof,
producing `False`.

**Case 3b: `c > 0`.** This is the substantial case. We know `c > 0` and
`c * b < c * a`, and we need a contradiction with `a ≤ b` (i.e., `¬(b < a)`).

The strategy is: multiply both sides of `c * b < c * a` by `c⁻¹` to "cancel" the `c`
and recover `b < a`.

```lean
have inv_pos : 0 < c⁻¹ := by
  have : 1 / c = c⁻¹ := by rw [CField.div_eq_mul_inv, one_mul]
  rw [← this]; exact one_div_pos_of_pos c_pos
```

First, establish that `c⁻¹` is positive. We use the `one_div_pos_of_pos` theorem we
just proved: since `c > 0`, we get `1/c > 0`, which equals `c⁻¹ > 0`.

```lean
have : c⁻¹ * (c * b) < c⁻¹ * (c * a) := lt_mul_pos_left inv_pos hba
```

Now multiply both sides of `c * b < c * a` by the positive number `c⁻¹`. This is
legitimate because `lt_mul_pos_left` (our axiom) says multiplying by a positive
preserves strict inequality.

```lean
rw [← mul_assoc, CField.inv_mul c_ne, one_mul,
    ← mul_assoc, CField.inv_mul c_ne, one_mul] at this
```

Simplify both sides. The rewrite chain does:
- `← mul_assoc`: turns `c⁻¹ * (c * b)` into `(c⁻¹ * c) * b`
- `CField.inv_mul c_ne`: turns `c⁻¹ * c` into `1` (this requires `c ≠ 0`)
- `one_mul`: turns `1 * b` into `b`
- The same three steps for the other side

After the rewrite, `this : b < a`.

```lean
exact hab this
```

But `hab : a ≤ b` means `¬(b < a)`. Applying `hab` to our proof of `b < a` gives the
contradiction.

**Why this proof is interesting.** The structure reveals something about constructive
reasoning. We couldn't just say "either `c > 0` or `c = 0` or `c < 0`" because that
three-way split (trichotomy) requires the Law of the Excluded Middle. Instead, we:
1. First proved `c ≠ 0` by a separate contradiction argument.
2. Then used apartness (`ne_lt`) to split into `c < 0 ∨ 0 < c` -- a constructively
   valid two-way split.
3. Eliminated each case.

This two-stage approach -- first rule out equality, then use apartness to split -- is a
common pattern in constructive algebra.

## Summary

`Field.lean` defines `ConstructiveOrderedField`, the algebraic foundation for SIA. It
takes the algebra from Article 2 and the ordering from Article 3 and welds them together
with three axioms:

| Axiom | Says | Why it matters |
|-------|------|----------------|
| `lt_zero_one` | `0 < 1` | Field is non-trivial |
| `lt_add_left` | Adding preserves `<` | Order is translation-invariant |
| `lt_mul_pos_left` | Positive multiplication preserves `<` | Order is scaling-invariant |

From these, we derived:

- **Symmetric versions**: `lt_add_right`, `le_add_right_of` (adding on the right).
- **Non-strict versions**: `le_add_left_of`, `le_add_right_of`, `le_mul_pos_left`
  (the `≤` analogs).
- **Negation and sign**: `lt_neg_flip`, `le_neg_flip`, `neg_lt_zero`, `neg_pos`.
- **Concrete facts**: `zero_lt_two`, `two_ne_zero`.
- **Inverse positivity**: `one_div_pos_of_pos`.

These lemmas form the toolkit we'll use in later files. In Article 5, we'll add the
final ingredient: the Kock-Lawvere axiom, which turns our ordered field into the setting
for Smooth Infinitesimal Analysis.
