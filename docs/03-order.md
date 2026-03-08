# Article 3: Order.lean — What Does "Less Than" Mean Without LEM?

*Corresponds to Bell, Chapter 1 (constructive variant of the ordering Bell assumes).*

In Articles 1 and 2, we built a commutative ring and a field from scratch. We have
addition, multiplication, negation, inverses — all the arithmetic you need for a number
system. But we don't yet have any notion of *order*. We can't say "a < b" or "a is
positive" or "a is between b and c."

In classical mathematics, ordering the real numbers is straightforward: for any two
numbers a and b, exactly one of `a < b`, `a = b`, or `a > b` holds. This is called
**trichotomy**, and you probably never thought twice about it.

But trichotomy is secretly classical. We can't have it in SIA. This article explains
why, and shows how the file `SIA/Order.lean` builds a constructive replacement.

## Why trichotomy implies the Law of the Excluded Middle

Here is the key insight. Suppose you have trichotomy for your number system: for any
a and b, either `a < b`, `a = b`, or `b < a`. Now let P be *any* proposition
whatsoever. Define:

    a = 0
    b = if P then 0 else 1

By trichotomy applied to a and b, one of three cases must hold:

- `a < b`: then `0 < b`, so `b ≠ 0`, so P must be false
- `a = b`: then `b = 0`, so P must be true
- `b < a`: impossible, since b is 0 or 1 and a is 0

So for any proposition P, we've decided whether P is true or false. That is exactly
the Law of the Excluded Middle (LEM). And as we discussed in Article 1, LEM is
incompatible with SIA — it would collapse Delta down to {0} and kill the
Kock-Lawvere axiom.

So we need a weaker notion of order, one that is still strong enough to do useful
mathematics but does not secretly smuggle in LEM.

## The StrictOrder class

Here is the class definition:

```lean
class StrictOrder (R : Type u) extends LT R where
  lt_irrefl : ∀ (a : R), ¬ (a < a)
  lt_trans  : ∀ {a b c : R}, a < b → b < c → a < c
  ne_lt     : ∀ {a b : R}, a ≠ b → a < b ∨ b < a
```

Let's go through each piece.

### `extends LT R`

`LT R` is a Lean built-in typeclass that gives the type `R` a `<` operator. By
writing `extends LT R`, we're saying: a `StrictOrder` on `R` provides a `<`
relation, plus the three axioms that follow. This is the same pattern we saw in
Article 2 where `CommRing R` extended `Add R`, `Mul R`, etc.

### `lt_irrefl : ∀ (a : R), ¬ (a < a)`

**Irreflexivity.** Nothing is less than itself. The `¬` means "not" — more
precisely, `¬ (a < a)` means "assuming `a < a` leads to a contradiction." In Lean,
`¬ P` is defined as `P → False`, where `False` is the type with no inhabitants
(a proposition with no proof). So `lt_irrefl` says: "give me any `a`, and I'll give
you a function that takes a proof of `a < a` and produces `False`."

### `lt_trans : ∀ {a b c : R}, a < b → b < c → a < c`

**Transitivity.** If a < b and b < c, then a < c. Nothing unusual here — this is the
same as in classical math. The curly braces `{a b c : R}` make these arguments
*implicit*: Lean will figure them out from context, so you don't have to write them
explicitly.

### `ne_lt : ∀ {a b : R}, a ≠ b → a < b ∨ b < a`

**Apartness.** If a and b are *not equal*, then one of them is strictly less than the
other. The `∨` means "or" — but remember, in constructive logic, a proof of `P ∨ Q`
must *actually specify* which one holds and provide a proof of it. You can't just say
"one of them is true" without saying which.

This might look like trichotomy, but it's strictly weaker. Trichotomy says: for any
a and b, either `a < b`, `a = b`, or `b < a`. Apartness says: *if you already know*
a ≠ b, then you get `a < b ∨ b < a`. The difference is the hypothesis. You need
a proof of `a ≠ b` up front.

And in constructive logic, `a ≠ b` means "assuming a = b leads to a contradiction."
You might not have such a proof! For example, for a nilsquare infinitesimal d, you
can't prove `d = 0` and you can't prove `d ≠ 0`. So `ne_lt` gives you nothing in
that case, which is exactly what we want — we don't want to be able to compare
infinitesimals to zero.

## Opening the namespace

```lean
namespace StrictOrder

variable {R : Type u} [StrictOrder R]
```

`namespace StrictOrder` means all the theorems that follow live under the name
`StrictOrder.*` and have access to the axioms of the `StrictOrder` class.

`variable {R : Type u} [StrictOrder R]` says: "throughout this section, R is a type
with a `StrictOrder` instance." The curly braces make `R` implicit, and the square
brackets `[StrictOrder R]` tell Lean's typeclass system to find the instance
automatically.

## Defining ≤

```lean
instance : LE R where
  le a b := ¬ (b < a)
```

This defines "less than or equal to" for our type R. The definition is:

> `a ≤ b` means `¬ (b < a)` — "it is not the case that b < a."

This is different from what you might expect. In classical math, you'd probably define
`a ≤ b` as `a < b ∨ a = b` ("a is strictly less than b, or they are equal"). That
definition is perfectly consistent constructively — it doesn't lead to contradictions.
But it's less useful, because to prove `a ≤ b` you'd need to produce a proof of
`a < b` or a proof of `a = b`, and sometimes you can't do either (for example, you
can't prove `d < 0`, `d = 0`, or `0 < d` for an arbitrary infinitesimal `d`). So you'd end up with fewer theorems
about `≤`.

The negation-based definition `¬ (b < a)` is weaker (easier to satisfy): you just
need to show that `b < a` is impossible, without having to decide which of the two
positive cases holds. This makes `≤` provable in more situations.

Note the `instance` keyword: this is creating a typeclass instance, telling Lean "here
is how to interpret the `≤` symbol for any type R that has a `StrictOrder`." After this
definition, we can write `a ≤ b` anywhere that R has a `StrictOrder`.

## The first theorems

### lt_ne: strict inequality implies not-equal

```lean
theorem lt_ne {a b : R} (h : a < b) : a ≠ b :=
  fun hab => lt_irrefl a (hab ▸ h)
```

If `a < b`, then `a ≠ b`. Recall that `a ≠ b` means `(a = b) → False`, so we need to
provide a function that takes a proof of `a = b` and produces `False`.

The keyword `fun` creates an anonymous function (also called a lambda). The syntax
`fun x => body` means "given `x`, return `body`." Here, `fun hab => ...` takes a
proof `hab : a = b` and derives a contradiction.

The key move is `hab ▸ h`. The `▸` operator is called "substitution" or "rewrite in
the goal." Here, `hab` is a proof that `a = b`, and `h` is a proof that `a < b`.
Writing `hab ▸ h` substitutes b with a in h (rewriting backward along the equality),
producing a proof of `a < a`. Then `lt_irrefl a` takes that proof of `a < a` and
produces `False` — a contradiction.

So the whole thing says: "If a = b, then a < b becomes a < a, which contradicts
irreflexivity."

### le_refl: ≤ is reflexive

```lean
theorem le_refl (a : R) : a ≤ a := lt_irrefl a
```

`a ≤ a` unfolds to `¬ (a < a)`, which is exactly `lt_irrefl a`. This is a
one-word proof: the axiom of irreflexivity *is* the proof that ≤ is reflexive.

### le_of_lt: strict inequality implies weak inequality

```lean
theorem le_of_lt {a b : R} (h : a < b) : a ≤ b :=
  fun hba => lt_irrefl a (lt_trans h hba)
```

If `a < b`, then `a ≤ b`. Remember, `a ≤ b` means `¬ (b < a)`, so we need to show
that `b < a` is impossible. Assume `hba : b < a`. Then by transitivity, `a < b` and
`b < a` give `a < a`, which contradicts irreflexivity.

### le_of_eq: equality implies weak inequality

```lean
theorem le_of_eq {a b : R} (h : a = b) : a ≤ b :=
  h ▸ le_refl a
```

If `a = b`, then `a ≤ b`. We start with `le_refl a : a ≤ a`, and use `h ▸` to
substitute, yielding `a ≤ b`.

## The theorem that doesn't exist: le_antisymm

In classical math, if `a ≤ b` and `b ≤ a`, then `a = b`. This is called
**antisymmetry**, and it's a basic property of every ordered set you've ever met.

In our system, we can *not* prove this. Here's why:

We have `a ≤ b` (meaning `¬ (b < a)`) and `b ≤ a` (meaning `¬ (a < b)`). We want
to conclude `a = b`. How?

In classical math, you'd use trichotomy: either `a < b`, `a = b`, or `b < a`. The
first and third cases are ruled out by our hypotheses, so `a = b`.

But we don't have trichotomy. We have `ne_lt`: if `a ≠ b`, then `a < b ∨ b < a`. But
that goes the wrong direction — it starts from `a ≠ b`, not toward `a = b`.

What we *can* do is prove the double negation: `¬¬ (a = b)`. That is, "it's not the
case that a ≠ b." This is weaker than `a = b`, and the gap between `¬¬ P` and `P` is
exactly what separates constructive from classical logic.

### Double negation, explained

In classical logic, `¬¬ P` and `P` are the same thing. "It's not the case that P is
false" means "P is true." This is called **double-negation elimination** (DNE), and
it is equivalent to LEM.

In constructive logic, `¬¬ P` is strictly weaker than `P`. You can always go from `P`
to `¬¬ P` (if P is true, then the assumption that P is false leads to contradiction),
but you can't go back. Knowing that "the assumption P is false leads to contradiction"
doesn't hand you an actual *proof* of P — it just tells you that no disproof exists.

This is a real difference, not just a philosophical quibble. In our system,
`¬¬ (a = b)` means "you'll never be able to prove a ≠ b," but it does NOT give you a
proof of `a = b` that you could use in computation. It's the difference between "there
is no evidence against" and "here is the evidence for."

### le_le_eq_nn: the best we can do

```lean
theorem le_le_eq_nn {a b : R} (hab : a ≤ b) (hba : b ≤ a) : ¬¬ (a = b) :=
  fun hne => (ne_lt hne).elim (fun h => hba h) (fun h => hab h)
```

We want `¬¬ (a = b)`, which is `¬ (a = b) → False`, which is `(a ≠ b) → False`.
So assume `hne : a ≠ b` and derive a contradiction.

By `ne_lt`, `a ≠ b` gives us `a < b ∨ b < a`:

    ne_lt hne : a < b ∨ b < a

Now eliminate the `Or`:

**Case 1: `a < b`.** We have `h : a < b`. But `hba : b ≤ a` means `¬ (a < b)`. So
`hba h : False`. Contradiction.

**Case 2: `b < a`.** We have `h : b < a`. But `hab : a ≤ b` means `¬ (b < a)`. So
`hab h : False`. Contradiction.

Both cases are contradictions, so `¬¬ (a = b)` holds. But notice: at no point did we
produce an actual proof of `a = b`. We only showed that assuming `a ≠ b` is
inconsistent. In classical logic, this would be the same as proving `a = b`. In
constructive logic, it is not.

This is a core difference between the SIA world and classical real analysis. When you
work with the reals classically, `≤` is a *partial order* (reflexive, antisymmetric,
transitive). In SIA, `≤` is reflexive, but antisymmetry only holds behind a double
negation. (Transitivity of `≤` can be proved if you add cotransitivity — see the
[appendix](appendix-cotransitivity.md).) This is not a defect — it's a feature. It
reflects the genuine underdetermination of order among infinitesimals.

## Summary of `.elim` patterns

Since `.elim` appears many times in this file, here is a summary of the two forms
used:

**`Or.elim` — case analysis on a disjunction.** If you have `h : P ∨ Q` and you want
to prove `R`, you write:

```lean
h.elim (fun hp => ...) (fun hq => ...)
```

The first function handles the case where P holds; the second handles Q. Both must
return something of type R.

**`False.elim` — anything from a contradiction.** If you have `h : False`, then
`h.elim` produces a value of any type. This is ex falso quodlibet: from a
contradiction, anything follows. You see this in `(hab h).elim` where `hab : ¬ X`
and `h : X`, so `hab h : False`, and `.elim` converts it to whatever type is needed.

## What we've built

This file establishes a strict order on our type R with three axioms
(irreflexivity, transitivity, apartness) and derives from them:

- A definition of `≤` as negated strict inequality
- That `<` implies `≠` (`lt_ne`)
- That `≤` is reflexive (`le_refl`)
- That `<` implies `≤` (`le_of_lt`) and `=` implies `≤` (`le_of_eq`)
- That mutual `≤` implies double-negated equality (`le_le_eq_nn`)

A fourth axiom, **cotransitivity** (`a < b → ∀ c, a < c ∨ c < b`), is a standard
constructive order axiom but is not used by any SIA proof in this project. It lives
in `extras/Cotransitivity.lean` and is documented in the
[cotransitivity appendix](appendix-cotransitivity.md).

The next file, `Field.lean`, will connect this order structure with the field
arithmetic from Article 2, giving us a **constructive ordered field** — the base
structure on which SIA is built.
