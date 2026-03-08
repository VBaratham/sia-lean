# Appendix: Cotransitivity

*This appendix covers material that is mathematically interesting but not used
by any SIA proof in this project. The corresponding Lean code lives in
`extras/Cotransitivity.lean`, outside the main `SIA/` directory.*

---

## What cotransitivity is

Cotransitivity (also called **locatedness**) is a standard axiom in constructive
order theory:

```
∀ {a b : R}, a < b → ∀ (c : R), a < c ∨ c < b
```

It says: if `a < b`, then for any third point `c`, either `a < c` or `c < b`
(or both — constructive "or" allows both to hold).

Picture a number line:

```
    a-----------b
```

If you know `a < b`, and someone hands you any point `c`, cotransitivity says:
`c` must land somewhere that lets you make at least one comparison. Either `c` is
to the right of `a` (giving `a < c`), or `c` is to the left of `b` (giving
`c < b`), or both:

```
    a-----c-----b        both a < c and c < b
    a-----------b---c    a < c (and also c is past b)
    c---a-------b        c < b (and also c is before a)
```

In every case, at least one of `a < c` or `c < b` holds.

The name "cotransitivity" comes from a duality with transitivity. Transitivity
says: if you know `a < b` and `b < c`, you can conclude `a < c` — you combine
two facts to produce one. Cotransitivity goes the other direction: from one fact
(`a < b`) and one test point (`c`), you produce a disjunction of two facts
(`a < c ∨ c < b`).

## Why it's not in our axiom system

Bell does not list cotransitivity among his order axioms (Chapter 8, axiom R₂).
More importantly, none of the SIA proofs in this project use it. We verified
this by checking which theorems depend on `lt_cotrans` — only the three theorems
in `extras/Cotransitivity.lean` itself (`le_lt_trans`, `lt_le_trans`, `le_trans`),
and nothing downstream uses those.

Since our goal is to formalize what Bell's SIA actually needs, we keep
cotransitivity as an optional extension rather than a core axiom.

## The CotransOrder class

The Lean code defines a class that extends `StrictOrder` with the cotransitivity
axiom:

```lean
class CotransOrder (R : Type u) extends StrictOrder R where
  lt_cotrans : ∀ {a b : R}, a < b → ∀ (c : R), a < c ∨ c < b
```

Any type with a `CotransOrder` instance automatically has all the `StrictOrder`
axioms plus cotransitivity.

## The cotransitivity proofs

The following three theorems show how cotransitivity replaces trichotomy in
proofs about transitivity of `≤`. They demonstrate a proof pattern that comes
up again and again in constructive order theory.

### le_lt_trans: if a ≤ b and b < c, then a < c

```lean
theorem le_lt_trans {a b c : R} (hab : a ≤ b) (hbc : b < c) : a < c :=
  (lt_cotrans hbc a).elim (fun h => (hab h).elim) id
```

We know `a ≤ b` (i.e., `¬ (b < a)`) and `b < c`. We want to prove `a < c`.

The strategy: use cotransitivity on `b < c` with test point `a`. This gives us:

    lt_cotrans hbc a : b < a ∨ a < c

This is a value of type `Or`, and we need to extract a proof of `a < c` from it.
We use `.elim`, which is how you do case analysis on `Or` in Lean.

**Case 1: `b < a`.** We get `h : b < a`. But we also know `hab : a ≤ b`, which
means `¬ (b < a)`. So `hab h` applies the negation to the proof, producing
`False`. Then `False.elim` (written as `.elim`) converts `False` into anything —
including `a < c`. This is the principle of *ex falso quodlibet*: from a
contradiction, you can prove anything.

**Case 2: `a < c`.** We get a proof of `a < c`, which is exactly what we wanted.
The function `id` (the identity function) just returns it unchanged.

The expression tree:

```
(lt_cotrans hbc a).elim (fun h => (hab h).elim) id
│                       │                        │
│                       │                        └─ Case 2: a < c → a < c (identity)
│                       │
│                       └─ Case 1: b < a → a < c
│                          hab h : False  (because hab says ¬(b < a))
│                          .elim : False → a < c
│
└─ b < a ∨ a < c  (from cotransitivity)
```

### lt_le_trans: if a < b and b ≤ c, then a < c

```lean
theorem lt_le_trans {a b c : R} (hab : a < b) (hbc : b ≤ c) : a < c :=
  (lt_cotrans hab c).elim id (fun h => (hbc h).elim)
```

This is the mirror image. We use cotransitivity on `a < b` with test point `c`:

    lt_cotrans hab c : a < c ∨ c < b

**Case 1: `a < c`.** This is what we want, so `id` returns it.

**Case 2: `c < b`.** We have `h : c < b`. But `hbc : b ≤ c` means `¬ (c < b)`.
So `hbc h : False`, and `.elim` converts the contradiction to `a < c`.

Notice the symmetry with `le_lt_trans` — the `id` and the
contradiction-elimination swap sides because the `Or` comes out in a different
order.

### le_trans: ≤ is transitive

```lean
theorem le_trans {a b c : R} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  fun hca => (lt_cotrans hca b).elim hbc hab
```

We want `a ≤ c`, which means `¬ (c < a)`. So assume `hca : c < a` and derive a
contradiction.

Use cotransitivity on `c < a` with test point `b`:

    lt_cotrans hca b : c < b ∨ b < a

**Case 1: `c < b`.** This is `h : c < b`. But `hbc : b ≤ c` means `¬ (c < b)`.
So `hbc h : False`. Contradiction.

**Case 2: `b < a`.** This is `h : b < a`. But `hab : a ≤ b` means `¬ (b < a)`.
So `hab h : False`. Contradiction.

Both cases are contradictions, so we're done. Notice that this proof doesn't
need `False.elim` explicitly — the `.elim` on `Or` just needs both branches to
produce the same type, and since both branches produce `False`, and the goal is
`False` (because we're inside a proof of a negation `¬ (c < a)`, which is
`c < a → False`), it works out.

Also notice the elegance here: `hbc` and `hab` are both of type
`¬ (something)`, which is `something → False`, so they can be passed directly
as the branch handlers to `.elim`. No `fun` wrappers needed. This is a place
where Lean's treatment of negation as a function type pays off.
