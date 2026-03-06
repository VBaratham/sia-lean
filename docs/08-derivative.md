# Article 8: Derivative.lean --- Derivatives Without Limits

This is the file the entire project has been building toward. In Article 1,
we promised that SIA gives you derivatives without limits, without
epsilon-delta arguments, without careful estimation. This file delivers on
that promise.

We will prove the sum rule, the product rule, the chain rule, and the
derivative of constant and identity functions --- all from pure algebra,
with no analysis machinery whatsoever. The proofs are short, and the key
steps are exactly the steps you would do on a whiteboard. The difference is
that here, every step is verified by a computer.

But before we get to the theorems, we need to address a subtle design
decision that shapes the entire file.

---

## The design choice: why there is no `deriv` function

In most calculus formalizations, you would define a function `deriv f x` that
returns the derivative of `f` at `x`. In our setting, the derivative is the
unique slope from microaffinity (Article 6): for any function `f` and point
`x`, there exists a unique `a` such that for all `d` in Delta,

    f(x + d) = f(x) + a * d

The natural thing to do would be to extract that unique `a` and call it
`deriv f x`. In Lean, the tool for extracting a witness from an existence
proof is `Exists.choose`. But `Exists.choose` relies on `Classical.choice`
--- which is exactly the axiom that gives you the Law of the Excluded Middle.

And as we proved in Article 6, LEM is incompatible with SIA. Our entire
project is about avoiding classical logic. If we used `Exists.choose` to
define `deriv`, every theorem about derivatives would depend on
`Classical.choice`, and our constructive guarantee would be ruined.

So we take a different approach. Instead of defining the derivative as a
function, we prove derivative *rules* directly. The technique is:

1. Assume `f` has slope `a` (meaning `f(x+d) = f(x) + a*d` for all `d` in
   Delta).
2. Assume `g` has slope `b` (similarly).
3. Show that some candidate (like `a + b`) satisfies the slope equation for
   the combined function.
4. Use uniqueness (from `ExistsUnique`) to conclude that the slope of the
   combined function equals the candidate.

This is the strategy behind every theorem in this file. The header comment
explains it:

```lean
import SIA.Delta

universe u

namespace SIA

variable {R : Type u} [SIA R]
open CommRing StrictOrder
```

We import `SIA.Delta`, which gives us everything: the full algebraic
hierarchy, the Kock-Lawvere axiom, Delta, microaffinity, and
microcancellation. The `variable` line says all theorems below work for any
type `R` that satisfies the SIA axioms. The `open` command brings names from
`CommRing` and `StrictOrder` into scope so we can write `zero_mul` instead
of `CommRing.zero_mul`.

---

## Constant function: slope is 0

```lean
theorem deriv_const_slope (c : R) (x : R) :
    ∀ (d : Delta R), (fun _ => c) (x + d.val) = (fun _ => c) x + 0 * d.val := by
  intro d; rw [zero_mul, add_zero]
```

The constant function `fun _ => c` ignores its input and always returns `c`.
The slope should be 0, because a constant function has no change.

The theorem says: for all `d` in Delta, `c = c + 0 * d`. The proof is
immediate. `zero_mul` rewrites `0 * d.val` to `0`, and `add_zero` rewrites
`c + 0` to `c`, leaving `c = c`, which Lean accepts as true by reflexivity.

If you know the derivative of a constant is zero, this is exactly what you
would expect. The only difference from a traditional proof is that there are
no limits involved --- just substitution and simplification.

---

## Identity function: slope is 1

```lean
theorem deriv_id_slope (x : R) :
    ∀ (d : Delta R), id (x + d.val) = id x + 1 * d.val := by
  intro d; simp [id, one_mul]
```

The identity function `id` returns its input unchanged: `id(t) = t`. Its
slope should be 1, because the identity grows at rate 1.

The theorem says: `x + d = x + 1 * d`. The `simp` tactic unfolds `id` to
see that both sides are just `x + d` (since `1 * d = d` by `one_mul`), and
closes the goal.

---

## Sum rule: slope of f + g is slope of f plus slope of g

```lean
theorem deriv_add_slope (f g : R → R) (x a b : R)
    (ha : ∀ (d : Delta R), f (x + d.val) = f x + a * d.val)
    (hb : ∀ (d : Delta R), g (x + d.val) = g x + b * d.val) :
    ∀ (d : Delta R), (f (x + d.val) + g (x + d.val)) = (f x + g x) + (a + b) * d.val := by
  intro d
  rw [ha d, hb d, right_distrib]
  rw [add_assoc, ← add_assoc (a * d.val), add_comm (a * d.val) (g x),
      add_assoc, add_assoc]
```

This is the sum rule: `(f + g)' = f' + g'`. Let us read the statement
carefully.

The hypotheses `ha` and `hb` say that `f` has slope `a` and `g` has slope
`b` at the point `x`. The conclusion says that the function `f + g` (that
is, the function sending `t` to `f(t) + g(t)`) has slope `a + b`.

Here is the mathematical content. Starting from the left side:

    f(x + d) + g(x + d)
    = (f(x) + a*d) + (g(x) + b*d)       [by ha and hb]
    = (f(x) + g(x)) + (a + b)*d         [rearranging terms]

The last step uses `right_distrib`, which is the ring axiom saying
`(a + b) * d = a * d + b * d`. Reading it right-to-left, `a*d + b*d`
becomes `(a + b) * d`, which is what we need.

The proof rewrites with `ha d` and `hb d` to expand both function
applications, then with `right_distrib` to factor the slopes. The remaining
four rewrites are just rearranging the sum --- moving `g(x)` past `a * d`
and regrouping parentheses. This is the kind of routine algebra that you
would do in your head on paper, but Lean requires each step to be justified.

---

## Negation rule: slope of -f is -a

```lean
theorem deriv_neg_slope (f : R → R) (x a : R)
    (ha : ∀ (d : Delta R), f (x + d.val) = f x + a * d.val) :
    ∀ (d : Delta R), (-(f (x + d.val))) = (-(f x)) + (-a) * d.val := by
  intro d
  rw [ha d, neg_add_distrib, neg_mul_left]
```

If `f` has slope `a`, then `-f` has slope `-a`. The proof expands
`f(x + d)` using `ha`, then distributes negation over the sum with
`neg_add_distrib` (which says `-(p + q) = -p + -q`), and finally pulls
the negation sign onto the left factor of the product using `neg_mul_left`
(which says `-(a * d) = (-a) * d`).

---

## Scalar multiplication: slope of c * f is c * a

```lean
theorem deriv_const_mul_slope (c : R) (f : R → R) (x a : R)
    (ha : ∀ (d : Delta R), f (x + d.val) = f x + a * d.val) :
    ∀ (d : Delta R), (c * f (x + d.val)) = (c * f x) + (c * a) * d.val := by
  intro d
  rw [ha d, left_distrib, mul_assoc]
```

If `f` has slope `a`, then `c * f` has slope `c * a`. The proof is two
rewrites: expand `f(x + d)` with `ha`, distribute `c` over the sum with
`left_distrib` (which says `c * (p + q) = c * p + c * q`), and reassociate
`c * (a * d)` into `(c * a) * d` with `mul_assoc`.

This matches the familiar scalar multiple rule from calculus: `(c * f)' =
c * f'`.

---

## Product rule: the highlight of the file

```lean
theorem deriv_mul_slope (f g : R → R) (x a b : R)
    (ha : ∀ (d : Delta R), f (x + d.val) = f x + a * d.val)
    (hb : ∀ (d : Delta R), g (x + d.val) = g x + b * d.val) :
    ∀ (d : Delta R), (f (x + d.val) * g (x + d.val)) =
      (f x * g x) + (a * g x + f x * b) * d.val := by
  intro d
  rw [ha d, hb d]
  rw [left_distrib, right_distrib, right_distrib]
  -- last term: (a*d)*(b*d) = a*b*d² = 0
  have last_zero : (a * d.val) * (b * d.val) = 0 := by
    calc (a * d.val) * (b * d.val)
        = a * (d.val * (b * d.val)) := by rw [mul_assoc]
      _ = a * ((d.val * b) * d.val) := by rw [mul_assoc d.val]
      _ = a * ((b * d.val) * d.val) := by rw [mul_comm d.val b]
      _ = a * (b * (d.val * d.val)) := by rw [mul_assoc b]
      _ = a * (b * 0) := by rw [d.property]
      _ = 0 := by rw [mul_zero, mul_zero]
  rw [last_zero, add_zero]
  rw [right_distrib]
  rw [add_assoc]; congr 1
  calc a * d.val * g x + f x * (b * d.val)
      = a * (d.val * g x) + f x * (b * d.val) := by rw [mul_assoc a]
    _ = a * (g x * d.val) + f x * (b * d.val) := by rw [mul_comm d.val (g x)]
    _ = (a * g x) * d.val + f x * (b * d.val) := by rw [← mul_assoc a]
    _ = (a * g x) * d.val + (f x * b) * d.val := by rw [← mul_assoc (f x)]
```

This is the product rule: if `f` has slope `a` and `g` has slope `b`, then
`f * g` has slope `a * g(x) + f(x) * b`. In the notation of traditional
calculus, this is `(fg)' = f'g + fg'`.

This theorem is the jewel of the file, and it perfectly illustrates why SIA
makes calculus algebraically clean. Let us trace through the mathematics
before looking at the proof.

### The mathematical argument

We want to compute `f(x+d) * g(x+d)`. Expand using the slope equations:

    f(x+d) * g(x+d)
    = (f(x) + a*d) * (g(x) + b*d)

Now multiply out, exactly as you would expand `(p + q)(r + s)`:

    = f(x)*g(x) + f(x)*(b*d) + (a*d)*g(x) + (a*d)*(b*d)

There are four terms. The first is `f(x)*g(x)`, which is the value of `fg`
at `x`. The middle two are the "first-order" terms, proportional to `d`.
The last term is the "second-order" term.

Here is the key move. The last term is `(a*d)*(b*d)`. Rearranging the
factors, this contains `d * d` --- which is `d^2`. But `d` is in Delta, so
`d^2 = 0`. Therefore the last term vanishes:

    (a*d)*(b*d) = a*b*d^2 = a*b*0 = 0

What remains is:

    f(x)*g(x) + f(x)*(b*d) + (a*d)*g(x)
    = f(x)*g(x) + (a*g(x) + f(x)*b) * d

And that is the product rule. The slope of `fg` is `a*g(x) + f(x)*b`,
which is `f'(x)*g(x) + f(x)*g'(x)`.

### Why this is remarkable

In traditional calculus, proving the product rule requires a limit argument.
The standard proof adds and subtracts a cleverly chosen term:

    [f(x+h)g(x+h) - f(x)g(x)] / h
    = f(x+h) * [g(x+h) - g(x)]/h + g(x) * [f(x+h) - f(x)]/h

You then take the limit as `h -> 0`, argue that `f(x+h) -> f(x)` (which
requires continuity, which requires its own proof), and conclude. It works,
but it involves an estimation argument and a continuity argument on top of
the algebra.

Here, there is no limit, no continuity argument, no clever trick. You
expand the product, and the second-order term is exactly zero because
infinitesimals are nilsquare. The proof is pure algebra.

This is the core reason SIA exists as a theory. The nilsquare property
`d^2 = 0` is not just a curiosity --- it is the engine that makes all of
calculus algebraic.

### The proof in detail

The proof proceeds in three phases.

**Phase 1: Expand.** The first three rewrites substitute the slope equations
(`ha d` and `hb d`) and then distribute multiplication over addition using
`left_distrib` and `right_distrib`. After this, the goal contains the four
terms from the FOIL expansion.

**Phase 2: Kill the second-order term.** The `have last_zero` block proves
that `(a * d) * (b * d) = 0`. The `calc` chain rearranges the four factors
using associativity and commutativity until `d * d` (which is `d.property`,
the proof that `d^2 = 0`) appears. Then `mul_zero` collapses `b * 0` to `0`
and `a * 0` to `0`. After `rw [last_zero, add_zero]`, the second-order
term is gone.

**Phase 3: Rearrange into the target form.** What remains is
`f(x)*g(x) + a*d*g(x) + f(x)*b*d`, and we need to show this equals
`f(x)*g(x) + (a*g(x) + f(x)*b)*d`. The `right_distrib` rewrite expands
`(a*g(x) + f(x)*b)*d` on the right side. Then `congr 1` says "the first
summands are the same (`f(x)*g(x)`), so it suffices to show the second
summands are equal." The final `calc` block shuffles factors using
associativity and commutativity to match the two sides: moving `d` to the
right in `a*d*g(x)` (to get `(a*g(x))*d`) and regrouping `f(x)*(b*d)` as
`(f(x)*b)*d`.

The `congr 1` tactic deserves a brief explanation. It stands for
"congruence, one level deep." If your goal is `p + q = p + r`, then
`congr 1` reduces it to `q = r` --- it peels off the shared outer structure
(here, `p + _`) and asks you to prove the remaining pieces are equal.

---

## Chain rule: composition of slopes

```lean
theorem deriv_comp_slope (f g : R → R) (x a b : R)
    (ha : ∀ (d : Delta R), f (g x + d.val) = f (g x) + a * d.val)
    (hb : ∀ (d : Delta R), g (x + d.val) = g x + b * d.val) :
    ∀ (d : Delta R), f (g (x + d.val)) = f (g x) + (a * b) * d.val := by
  intro d
  -- g(x+d) = g(x) + b*d, and b*d ∈ Delta
  have gd_sq : (b * d.val) * (b * d.val) = 0 := by
    calc (b * d.val) * (b * d.val)
        = b * (d.val * (b * d.val)) := by rw [mul_assoc]
      _ = b * ((d.val * b) * d.val) := by rw [mul_assoc d.val]
      _ = b * ((b * d.val) * d.val) := by rw [mul_comm d.val b]
      _ = b * (b * (d.val * d.val)) := by rw [mul_assoc b]
      _ = b * (b * 0) := by rw [d.property]
      _ = 0 := by rw [mul_zero, mul_zero]
  let gd : Delta R := ⟨b * d.val, gd_sq⟩
  rw [hb d, ha gd, mul_assoc]
```

This is the chain rule: if `g` has slope `b` at `x` and `f` has slope `a`
at `g(x)`, then `f composed with g` has slope `a * b` at `x`. In classical
notation: `(f(g(x)))' = f'(g(x)) * g'(x)`.

### The mathematical argument

Start with `f(g(x + d))`. By the slope equation for `g`:

    g(x + d) = g(x) + b*d

So `f(g(x + d)) = f(g(x) + b*d)`. Now we want to apply the slope equation
for `f` at the point `g(x)`. That equation says: for any element `e` in
Delta, `f(g(x) + e) = f(g(x)) + a*e`. The question is: can we use
`e = b*d`?

We can, provided `b*d` is itself in Delta --- that is, provided
`(b*d)^2 = 0`. And it is:

    (b*d)^2 = (b*d)*(b*d) = b*b*d*d = b^2 * d^2 = b^2 * 0 = 0

So `b*d` is a valid element of Delta, and we can apply the slope equation
for `f`:

    f(g(x) + b*d) = f(g(x)) + a*(b*d) = f(g(x)) + (a*b)*d

The slope is `a*b`, which is the chain rule.

### The proof in detail

The `have gd_sq` block proves `(b * d) * (b * d) = 0` by the same kind of
associativity-commutativity shuffling we saw in the product rule. The `calc`
chain rearranges the factors until `d.val * d.val` appears, substitutes
`d.property` (which is the proof that `d^2 = 0`), and collapses to zero.

The line `let gd : Delta R := ...` constructs `b * d` as a formal element
of `Delta R`. Remember from Article 5 that an element of `Delta R` is a
pair: a value and a proof that its square is zero. Here the value is
`b * d.val` and the proof is `gd_sq`.

Finally, `rw [hb d, ha gd, mul_assoc]` does three things:

1. `hb d` replaces `g(x + d)` with `g(x) + b*d`.
2. `ha gd` replaces `f(g(x) + b*d)` with `f(g(x)) + a*(b*d)`.
3. `mul_assoc` rewrites `a * (b * d)` as `(a * b) * d`.

And the goal is closed. Three rewrites for the chain rule.

### Comparison with traditional calculus

The classical chain rule proof is notoriously subtle. The naive approach ---
write `[f(g(x+h)) - f(g(x))]/h` as `[f(g(x+h)) - f(g(x))]/[g(x+h) - g(x)]
* [g(x+h) - g(x)]/h` and take the limit --- breaks down when
`g(x+h) - g(x) = 0`. You need either a careful reparameterization argument
or a different proof strategy entirely.

In SIA, this problem does not arise. We never divide by anything. We never
need `g(x+d) - g(x)` to be nonzero. We just need `b*d` to be in Delta,
which is always true. The proof is algebraic substitution, nothing more.

---

## The user-facing theorems

The five slope theorems above (constant, identity, sum, negation, scalar
multiplication, product, chain) prove that a *candidate* slope satisfies
the microaffinity equation. But they do not directly say "the derivative of
f+g is the derivative of f plus the derivative of g." To get that statement,
we need uniqueness.

This is what the final three theorems do. They package the slope theorems
into statements using `ExistsUnique.unique`.

### Sum rule with uniqueness

```lean
theorem deriv_add_eq (f g : R → R) (x : R) :
    ∀ (af ag afg : R),
    (∀ (d : Delta R), f (x + d.val) = f x + af * d.val) →
    (∀ (d : Delta R), g (x + d.val) = g x + ag * d.val) →
    (∀ (d : Delta R), (f (x + d.val) + g (x + d.val)) = (f x + g x) + afg * d.val) →
    afg = af + ag := by
  intro af ag afg hf hg hfg
  have hab := deriv_add_slope f g x af ag hf hg
  exact (microaffinity (fun t => f t + g t) x).unique hfg hab
```

This says: suppose `af` is the slope of `f`, `ag` is the slope of `g`, and
`afg` is the slope of `f + g`. Then `afg = af + ag`.

The proof is two lines. First, `deriv_add_slope` shows that `af + ag`
satisfies the slope equation for `f + g` (this is the earlier theorem).
Second, `(microaffinity ...).unique` says: since the slope of `f + g` is
unique (by the Kock-Lawvere axiom, via the `microaffinity` theorem from
Article 6), and both `afg` and `af + ag` satisfy the slope equation, they
must be equal.

This is where `ExistsUnique.unique` (from Article 5) does its work. Recall
that `ExistsUnique.unique` says: if there exists a unique thing satisfying a
property, and two candidates both satisfy it, then the two candidates are
equal. Here the property is "being a slope for `f + g` at `x`," and the two
candidates are `afg` (given by hypothesis) and `af + ag` (constructed by
`deriv_add_slope`).

### Product rule with uniqueness

```lean
theorem deriv_mul_eq (f g : R → R) (x : R) :
    ∀ (af ag afg : R),
    (∀ (d : Delta R), f (x + d.val) = f x + af * d.val) →
    (∀ (d : Delta R), g (x + d.val) = g x + ag * d.val) →
    (∀ (d : Delta R), (f (x + d.val) * g (x + d.val)) = (f x * g x) + afg * d.val) →
    afg = af * g x + f x * ag := by
  intro af ag afg hf hg hfg
  have hab := deriv_mul_slope f g x af ag hf hg
  exact (microaffinity (fun t => f t * g t) x).unique hfg hab
```

Same structure. The slope theorem `deriv_mul_slope` provides the candidate
`af * g x + f x * ag`. Uniqueness from microaffinity forces `afg` to equal
it. The result is the product rule: `(fg)' = f'g + fg'`.

### Chain rule with uniqueness

```lean
theorem deriv_comp_eq (f g : R → R) (x : R) :
    ∀ (af ag afg : R),
    (∀ (d : Delta R), f (g x + d.val) = f (g x) + af * d.val) →
    (∀ (d : Delta R), g (x + d.val) = g x + ag * d.val) →
    (∀ (d : Delta R), f (g (x + d.val)) = f (g x) + afg * d.val) →
    afg = af * ag := by
  intro af ag afg hf hg hfg
  have hab := deriv_comp_slope f g x af ag hf hg
  exact (microaffinity (fun t => f (g t)) x).unique hfg hab
```

The chain rule: the slope of `f composed with g` is the product of the
slopes. Note the careful typing in `hf`: the slope of `f` is taken at the
point `g x`, not at `x`. This matches the traditional chain rule, where
`f'` is evaluated at `g(x)`.

---

## The two-layer architecture

It is worth stepping back to see the structure of the file as a whole. There
are two layers of theorems:

**Layer 1: Slope construction.** Theorems like `deriv_add_slope`,
`deriv_mul_slope`, `deriv_comp_slope`. These say: "given slopes for the
parts, here is a slope for the whole." They are pure algebra --- expand,
simplify, rearrange. They never invoke microaffinity or uniqueness.

**Layer 2: Derivative rules.** Theorems like `deriv_add_eq`,
`deriv_mul_eq`, `deriv_comp_eq`. These say: "the slope of the whole equals
the expected combination of the parts' slopes." They invoke uniqueness
exactly once, delegating the algebraic work to Layer 1.

This separation is clean and modular. If you wanted to add a new derivative
rule (say, for the quotient `f/g`), you would:

1. Prove a slope construction theorem showing that a certain candidate
   satisfies the slope equation.
2. Write a one-line wrapper using `microaffinity ... .unique`.

---

## What we have proved

Let us compare the SIA derivatives with their classical counterparts:

| Rule | Classical statement | SIA slope |
|------|-------------------|-----------|
| Constant | `(c)' = 0` | `0` |
| Identity | `(x)' = 1` | `1` |
| Sum | `(f+g)' = f' + g'` | `a + b` |
| Negation | `(-f)' = -f'` | `-a` |
| Scalar | `(cf)' = c*f'` | `c*a` |
| Product | `(fg)' = f'g + fg'` | `a*g(x) + f(x)*b` |
| Chain | `(f(g(x)))' = f'(g(x))*g'(x)` | `a*b` |

The formulas are identical. The difference is entirely in how they are
proved. In classical calculus, each of these requires a limit argument. In
SIA, each is pure algebra, with the nilsquare property `d^2 = 0` doing the
heavy lifting.

The product rule proof is about 20 lines. The chain rule proof is about 15
lines. The sum rule is 5 lines. In a classical formalization using
epsilon-delta limits, the product rule alone can run to hundreds of lines
once you account for the limit definitions, the continuity lemma, and the
estimation arguments. The simplicity here is not an accident --- it is a
direct consequence of the Kock-Lawvere axiom.

---

## The constructive guarantee

Every theorem in this file avoids `Classical.choice`. The proofs use only:

- Ring axioms (associativity, commutativity, distributivity).
- The nilsquare property `d^2 = 0` (from the `Delta` subtype).
- Microaffinity and uniqueness (from the Kock-Lawvere axiom).

No excluded middle, no proof by contradiction on real-number properties, no
`Exists.choose`. The derivative rules are fully constructive. In Article 9,
we will verify this by asking Lean to inspect the axiom dependencies of
every theorem.

---

## Looking back

This file is short --- about 100 lines of actual proof. Yet it contains the
sum rule, product rule, chain rule, and several simpler derivative rules,
all verified by computer. The reason it can be so short is that SIA
collapses the distance between "informal whiteboard argument" and "rigorous
formal proof." In traditional analysis, the gap between the two is enormous:
the informal product rule argument (expand, note that `h^2` is negligible,
drop it) looks nothing like the formal epsilon-delta proof. In SIA, the
informal argument *is* the formal proof. You expand, note that `d^2 = 0`,
drop it. That is both the intuition and the computer-checked proof.

This is the payoff of the entire project. Five files of algebraic
infrastructure (Articles 2 through 4), one file of axioms (Article 5), one
file of core theorems (Article 6), and one file of continuity (Article 7)
--- all leading to a file where the fundamental theorems of differential
calculus are proved in a few lines of pure algebra.
