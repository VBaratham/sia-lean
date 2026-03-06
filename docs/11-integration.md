# Article 11: Integration.lean --- Integration and the Fundamental Theorem of Calculus

In traditional calculus, integration is the culmination of a long journey.
You define Riemann sums, take limits of increasingly fine partitions, prove
that the limit exists for well-behaved functions, and then --- after all that
work --- you prove the Fundamental Theorem of Calculus, which connects
integration back to differentiation. The FTC is rightly considered one of the
great theorems of mathematics. It takes two seemingly different concepts (area
under a curve and rate of change) and reveals them to be inverses.

In Smooth Infinitesimal Analysis, the story is completely different.
Integration is not defined by a limiting process. It is introduced by an
axiom: every function has a unique antiderivative. The Fundamental Theorem
of Calculus is not a deep theorem that requires the Mean Value Theorem and
careful limit arguments. It is, in one direction, literally the definition,
and in the other direction, a short consequence of uniqueness.

This might feel like cheating. But it is no different from how traditional
analysis handles the real numbers themselves. The completeness of the reals
--- every bounded increasing sequence has a limit --- is an axiom, not a
theorem. That axiom is what makes Riemann integration possible. SIA simply
replaces one foundational axiom with another: instead of completeness, we
have the integration axiom. The depth of the mathematics has not disappeared;
it has moved into the axiom.

This article walks through `SIA/Integration.lean`, which formalizes
integration, proves both parts of the Fundamental Theorem, and establishes
linearity and additivity of the integral. It is the longest file in the
project so far, and it brings together every idea from the previous ten
articles.

---

## Setup

```lean
import SIA.Delta

universe u

namespace SIA

variable {R : Type u}
open CommRing StrictOrder
```

The file imports `SIA.Delta`, which brings in the full algebraic hierarchy,
the Kock-Lawvere axiom, Delta, microaffinity, and microcancellation. The
variable declaration says all theorems work for any type `R`, and the `open`
commands bring names into scope. This is the same preamble we have seen in
every file since Article 6.

---

## What it means to be an antiderivative

```lean
def IsAntideriv [SIA R] (F f : R → R) : Prop :=
  F 0 = 0 ∧ ∀ (x : R) (d : Delta R), F (x + d.val) = F x + f x * d.val
```

This is the definition that everything in the file rests on. It says: `F` is
an antiderivative of `f` when two conditions hold.

**Condition 1: Normalization.** `F(0) = 0`. This pins down the constant of
integration. In traditional calculus, antiderivatives are only determined up
to an additive constant --- if `F` is an antiderivative of `f`, then so is
`F + C` for any constant `C`. Here we remove that ambiguity by requiring the
antiderivative to vanish at zero. This is the SIA analogue of writing the
definite integral `integral from 0 to x of f(t) dt`, which always evaluates
to 0 at `x = 0`.

**Condition 2: The slope condition.** For every point `x` and every
infinitesimal `d` in Delta, `F(x + d) = F(x) + f(x) * d`. This is the SIA
way of saying "the derivative of F is f." Recall from Article 6 that
microaffinity gives every function a unique slope at every point. The slope
condition says that the slope of `F` at `x` is exactly `f(x)`.

Compare this with the traditional definition, where `F` is an antiderivative
of `f` when `F'(x) = f(x)` for all `x`. In the traditional setting, `F'(x)`
is a limit:

    F'(x) = lim_{h->0} [F(x+h) - F(x)] / h

In SIA, there is no limit and no division. The microaffinity equation
`F(x + d) = F(x) + f(x) * d` directly says that `f(x)` is the slope of `F`
at `x`. The equation is exact, not approximate, because infinitesimals are
nilsquare --- there are no higher-order terms to worry about.

The `∧` symbol means "and," joining the two conditions. This is a conjunction,
so a proof of `IsAntideriv F f` is a pair: a proof that `F 0 = 0` and a proof
of the slope condition.

---

## The integration axiom

```lean
end SIA

class SIAIntegral (R : Type u) extends SIA R where
  integration : ∀ (f : R → R),
    SIA.ExistsUnique fun (F : R → R) => SIA.IsAntideriv F f
```

This defines a new class `SIAIntegral` that extends `SIA` with one additional
axiom: for every function `f : R -> R`, there exists a unique function
`F : R -> R` such that `IsAntideriv F f`.

There are several things to unpack here.

**Why a new class?** The integration axiom is genuinely new. It cannot be
derived from the Kock-Lawvere axiom. Kock-Lawvere tells us about the behavior
of functions on infinitesimal neighborhoods --- it is a *local* statement.
The integration axiom is a *global* statement: it asserts the existence of a
function defined on all of `R`, not just on Delta. Going from local to global
requires additional structure, and the integration axiom provides it.

This is analogous to the situation in traditional calculus. The existence of
derivatives (which is local) does not by itself guarantee the existence of
antiderivatives (which is global). In the traditional setting, the existence
of antiderivatives for continuous functions is proved using the completeness
of the reals --- you define `F(x) = integral from 0 to x of f(t) dt` using
Riemann sums and show the limit exists. In SIA, we do not have Riemann sums
or completeness. Instead, we axiomatically assert what the traditional proof
establishes.

**Why ExistsUnique?** The axiom does not just say an antiderivative exists. It
says there is exactly one. This is crucial. If antiderivatives were not unique,
you could not use them to define a well-behaved integral. Uniqueness is what
makes the integral of a function a *definite* quantity, not an ambiguous one.

The uniqueness comes from two sources working together: the normalization
condition `F(0) = 0` pins down the additive constant, and the slope condition
pins down the behavior everywhere else. Together, they leave no room for a
second antiderivative.

**The `extends SIA R` clause** means that any type `R` satisfying `SIAIntegral`
automatically satisfies `SIA` as well. You get all the ring axioms, the field
axioms, the order, and the Kock-Lawvere axiom, plus the integration axiom on
top.

Notice the `end SIA` before the class definition. As we discussed in Article 5,
this is a Lean technicality: you cannot define a class inside a namespace that
shares part of its name. The namespace is reopened immediately after the
definition.

```lean
namespace SIA

variable {R : Type u} [SIAIntegral R]
open CommRing StrictOrder ConstructiveOrderedField
```

From here on, `R` is assumed to satisfy `SIAIntegral`, which gives us
everything: the full algebraic hierarchy plus both the Kock-Lawvere axiom and
the integration axiom.

---

## Uniqueness of antiderivatives

```lean
theorem antideriv_unique {F G f : R → R}
    (hF : IsAntideriv F f) (hG : IsAntideriv G f) : F = G :=
  (SIAIntegral.integration f).unique hF hG
```

If `F` and `G` are both antiderivatives of the same function `f`, then
`F = G`. They are not just equal at some points, or equal up to a constant ---
they are the same function, everywhere.

The proof is one line. `SIAIntegral.integration f` gives us the proof that
there is a unique antiderivative of `f`. The `.unique` method (from
`ExistsUnique.unique`, which we defined in Article 5) says: if two things
both satisfy a uniquely-satisfied property, they must be equal. We hand it
`hF` (the proof that `F` is an antiderivative of `f`) and `hG` (the proof
that `G` is an antiderivative of `f`), and it returns `F = G`.

This is the same uniqueness technique we used throughout Derivative.lean
(Article 8). There, we used `microaffinity ... .unique` to prove derivative
rules. Here, we use `integration ... .unique` to prove integration rules. The
pattern is identical, and it is one of the most powerful tools in the project.

In traditional calculus, if `F` and `G` are both antiderivatives of `f`, you
can only conclude that `F - G` is a constant. Here, the normalization condition
`F(0) = 0` eliminates the constant, giving us true equality.

---

## FTC Part 2: the derivative of the integral is the original function

```lean
theorem ftc_part2 {F f : R → R} (hF : IsAntideriv F f) (x : R) :
    ∀ (d : Delta R), F (x + d.val) = F x + f x * d.val :=
  hF.2 x
```

In traditional calculus, the Fundamental Theorem of Calculus Part 2 (sometimes
called Part 1, depending on the textbook) says:

    d/dx [integral from 0 to x of f(t) dt] = f(x)

That is, if you integrate `f` and then differentiate, you get `f` back. The
traditional proof requires the Mean Value Theorem for integrals and a careful
limit argument.

In SIA, this is literally the definition of `IsAntideriv`. The second
component of `IsAntideriv F f` says that `F` has slope `f(x)` at every point
`x` --- which is exactly the statement that the derivative of `F` is `f`.
The proof is `hF.2 x`: take the second component (`.2`) of the
antiderivative hypothesis and apply it to `x`.

One line of code. Compare that with the traditional proof, which fills a page
or more of analysis textbook. The simplicity is not because the mathematics is
shallow --- it is because the depth has been absorbed into the axioms. The
integration axiom *defines* the antiderivative to be a function whose slope is
`f`. Asking for the derivative of the antiderivative is asking: "what is the
slope of the function whose slope is defined to be `f`?" The answer is
obviously `f`.

---

## Shifting an antiderivative: the normalization trick

```lean
theorem shift_is_antideriv {F f : R → R}
    (hslope : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + f x * d.val) :
    IsAntideriv (fun x => F x - F 0) f := by
  constructor
  · exact sub_self (F 0)
  · intro x d
    show F (x + d.val) - F 0 = (F x - F 0) + f x * d.val
    rw [hslope x d]
    rw [sub_eq (F x + f x * d.val), sub_eq (F x)]
    rw [add_assoc, add_comm (f x * d.val) (-(F 0)), ← add_assoc]
```

This theorem handles a situation that arises naturally in calculus. Suppose
you have a function `F` that has slope `f(x)` at every point (so `F` is an
antiderivative of `f` in the sense of having the right derivative), but
`F(0)` might not be zero. Then `G(x) = F(x) - F(0)` is a proper
antiderivative in our sense: it has the same slope as `F` everywhere, and
`G(0) = F(0) - F(0) = 0`.

This is the normalization trick. In traditional calculus, you would say
"antiderivatives are unique up to a constant, so we can always subtract the
constant to get `F(0) = 0`." Here we make that explicit.

The proof has two parts, matching the two conditions of `IsAntideriv`:

**Part 1 (normalization):** We need `G(0) = 0`, that is, `F(0) - F(0) = 0`.
This is `sub_self (F 0)` --- anything minus itself is zero.

**Part 2 (slope):** We need to show that `G` has slope `f(x)` at every
point. The goal is:

    F(x + d) - F(0) = (F(x) - F(0)) + f(x) * d

We rewrite `F(x + d)` using the slope hypothesis `hslope x d` to get
`F(x) + f(x) * d`. Then it is pure algebra: we need to show that
`(F(x) + f(x) * d) - F(0) = (F(x) - F(0)) + f(x) * d`. The three rewrites
expand subtractions as additions of negations and rearrange the terms. This
is the kind of tedious-but-straightforward algebraic shuffling that the `ring`
tactic would handle automatically in a library-rich formalization, but which
we do step by step in our minimal foundation.

---

## A helper lemma: algebraic cancellation

```lean
private theorem sub_sub_cancel_right (a b c : R) : (a - c) - (b - c) = a - b := by
  calc (a - c) - (b - c)
      = (a - c) + (-(b - c)) := by rw [sub_eq]
    _ = (a - c) + (c - b) := by rw [neg_sub]
    _ = (a - c) + (c + -(b)) := by rw [sub_eq c b]
    _ = ((a - c) + c) + -(b) := by rw [← add_assoc]
    _ = a + -(b) := by rw [sub_add_cancel]
    _ = a - b := by rw [← sub_eq]
```

This is a pure algebra lemma: `(a - c) - (b - c) = a - b`. The `c` terms
cancel. This is used in the proof of FTC Part 1 below.

The `private` keyword means this lemma is not visible outside the file. It is
a helper, not part of the public API.

The `calc` block traces through six steps. Let us read the chain:

1. Expand the outer subtraction: `(a - c) - (b - c) = (a - c) + (-(b - c))`.
2. Simplify `-(b - c)` to `c - b` using `neg_sub`.
3. Expand the inner subtraction: `c - b = c + (-b)`.
4. Re-associate: `(a - c) + (c + (-b)) = ((a - c) + c) + (-b)`.
5. Cancel `(a - c) + c` to `a` using `sub_add_cancel`.
6. Fold back: `a + (-b) = a - b`.

This is a one-line fact in pen-and-paper mathematics. In our minimal
foundation, where every algebraic step must be justified by name, it takes
six steps. The `private` keyword acknowledges that this lemma has no
mathematical interest of its own --- it is bookkeeping.

---

## FTC Part 1: the integral of the derivative recovers the function

```lean
theorem ftc_part1 {F G f : R → R}
    (hG : IsAntideriv G f)
    (hslope : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + f x * d.val) :
    ∀ (a b : R), G b - G a = F b - F a := by
  have hH : IsAntideriv (fun x => F x - F 0) f := shift_is_antideriv hslope
  have heq : G = fun x => F x - F 0 := antideriv_unique hG hH
  intro a b
  have hGb : G b = F b - F 0 := congrFun heq b
  have hGa : G a = F a - F 0 := congrFun heq a
  rw [hGb, hGa]
  exact sub_sub_cancel_right (F b) (F a) (F 0)
```

In traditional calculus, FTC Part 1 (again, numbering varies by textbook) says:

    integral from a to b of f(x) dx = F(b) - F(a)

where `F` is any antiderivative of `f`. This connects the definite integral
(defined via Riemann sums) with antiderivatives.

In our setting, the theorem says: if `G` is the canonical antiderivative of
`f` (with `G(0) = 0`), and `F` is any function with slope `f(x)` at every
point (but possibly `F(0) != 0`), then `G(b) - G(a) = F(b) - F(a)` for all
`a` and `b`.

Since `G(b) - G(a)` is the natural definition of "the integral of `f` from
`a` to `b`" (it is `G(b) - G(a)` where `G` is the antiderivative), this
theorem says that you can compute the integral using ANY function with the
right slope, not just the one satisfying `F(0) = 0`.

### The proof step by step

**Step 1: Shift `F`.** The hypothesis `hslope` says `F` has slope `f(x)`
everywhere, but we do not know that `F(0) = 0`. The theorem
`shift_is_antideriv` builds `H(x) = F(x) - F(0)`, which IS a proper
antiderivative.

**Step 2: Use uniqueness.** Both `G` and `H` are antiderivatives of `f` (both
satisfy `IsAntideriv`). By `antideriv_unique`, `G = H`. This gives us
`G = fun x => F x - F 0`.

**Step 3: Substitute.** For any `b`, `G(b) = F(b) - F(0)`. Similarly,
`G(a) = F(a) - F(0)`. The `congrFun` tactic applies a function equality to a
specific argument: if `G = H`, then `G(b) = H(b)`.

**Step 4: Cancel.** After substitution, the goal becomes
`(F(b) - F(0)) - (F(a) - F(0)) = F(b) - F(a)`. This is exactly the
`sub_sub_cancel_right` lemma from above.

The structure of this proof is worth noting. The hard mathematical work is
done by `antideriv_unique` --- the uniqueness of antiderivatives. Everything
else is just setting up the right functions and doing algebra. This is the
same pattern we saw in Derivative.lean: uniqueness does the heavy lifting, and
algebra fills in the details.

---

## Functions with zero slope are constant

The next group of theorems establishes that a function with zero derivative
everywhere is constant. This is a crucial result, and the way it is proved
reveals something important about the relationship between microaffinity and
integration.

### The zero function is an antiderivative of zero

```lean
theorem zero_is_antideriv_zero : IsAntideriv (fun (_ : R) => (0 : R)) (fun (_ : R) => (0 : R)) := by
  constructor
  · rfl
  · intro x d; rw [zero_mul, add_zero]
```

The zero function `F(x) = 0` is an antiderivative of the zero function
`f(x) = 0`. The normalization condition `F(0) = 0` is `0 = 0`, which is
`rfl`. The slope condition says `0 = 0 + 0 * d`, and after `zero_mul`
(rewriting `0 * d` to `0`) and `add_zero` (rewriting `0 + 0` to `0`),
the goal closes.

### If F has slope 0 everywhere and F(0) = 0, then F is identically zero

```lean
theorem zero_slope_is_zero {F : R → R}
    (hF0 : F 0 = 0)
    (hslope : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + (0 : R) * d.val) :
    F = fun _ => 0 := by
  have hF : IsAntideriv F (fun _ => 0) := ⟨hF0, fun x d => hslope x d⟩
  exact antideriv_unique hF zero_is_antideriv_zero
```

If `F` has slope 0 everywhere and `F(0) = 0`, then `F` is the zero function.
The proof: package the hypotheses into a proof that `F` is an antiderivative
of the zero function, and then use uniqueness. The zero function is also an
antiderivative of the zero function (by the previous lemma). By uniqueness,
`F` equals the zero function.

### The corollary: zero slope implies constant

```lean
theorem zero_slope_is_const {F : R → R}
    (hslope : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + (0 : R) * d.val) :
    ∀ (x : R), F x = F 0 := by
  have hH : IsAntideriv (fun x => F x - F 0) (fun _ => 0) := by
    constructor
    · exact sub_self (F 0)
    · intro x d
      show F (x + d.val) - F 0 = (F x - F 0) + (0 : R) * d.val
      rw [hslope x d, sub_eq (F x + (0 : R) * d.val), sub_eq (F x)]
      rw [add_assoc, add_comm ((0 : R) * d.val) (-(F 0)), ← add_assoc]
  have heq := antideriv_unique hH zero_is_antideriv_zero
  intro x
  have : F x - F 0 = 0 := congrFun heq x
  calc F x = (F x - F 0) + F 0 := by rw [sub_add_cancel]
    _ = 0 + F 0 := by rw [this]
    _ = F 0 := by rw [zero_add]
```

This removes the condition `F(0) = 0`. If `F` has slope 0 everywhere (but
`F(0)` might be anything), then `F(x) = F(0)` for all `x` --- that is, `F`
is constant.

The proof follows the now-familiar pattern: shift `F` by subtracting `F(0)`
to get a function that vanishes at zero, show it is an antiderivative of the
zero function, use uniqueness to conclude it equals the zero function, and
then unwind.

### Why this result is significant

In Article 7, we proved that the neighbor relation is not transitive. You
cannot chain infinitesimal steps: knowing that `a` is infinitesimally close
to `b`, and `b` is infinitesimally close to `c`, does not let you conclude
that `a` is close to `c`. This is because Delta is not closed under addition
(Article 6).

So microaffinity alone --- the fact that every function is locally linear ---
cannot give you global information. Microaffinity tells you the slope at each
point, but it cannot tell you that a function with zero slope at every point
is globally constant. The local data does not automatically aggregate into a
global conclusion.

The integration axiom changes this. It is a *global* statement: for every
function, there is a unique antiderivative defined on all of `R`. The
uniqueness is global too --- two antiderivatives of the same function must
agree everywhere, not just locally. This global uniqueness is what lets us
prove that a function with zero slope everywhere is constant.

In traditional calculus, the analogous result (a function with zero derivative
is constant) is proved using the Mean Value Theorem, which itself relies on
the completeness of the reals. So in both settings, proving that "zero slope
implies constant" requires a global axiom beyond the local notion of
derivative. In classical analysis, that axiom is completeness. In SIA, it is
the integration axiom.

---

## Linearity of antiderivatives

The next four theorems establish that the antiderivative operation is linear:
it respects addition, scalar multiplication, negation, and subtraction. Each
proof follows the same two-step strategy from Derivative.lean: (1) show that
the candidate function satisfies the antiderivative conditions, (2) use
uniqueness to conclude it is THE antiderivative.

### Addition of antiderivatives

```lean
theorem antideriv_add {F G : R → R} {f g : R → R}
    (hF : IsAntideriv F f) (hG : IsAntideriv G g) :
    IsAntideriv (fun x => F x + G x) (fun x => f x + g x) := by
  constructor
  · show F 0 + G 0 = 0
    rw [hF.1, hG.1, add_zero]
  · intro x d
    show F (x + d.val) + G (x + d.val) = (F x + G x) + (f x + g x) * d.val
    rw [hF.2 x d, hG.2 x d, right_distrib]
    rw [add_assoc, ← add_assoc (f x * d.val), add_comm (f x * d.val) (G x),
        add_assoc, add_assoc]
```

If `F` is an antiderivative of `f` and `G` is an antiderivative of `g`, then
`F + G` is an antiderivative of `f + g`. Let us walk through both parts.

**Normalization:** We need `(F + G)(0) = F(0) + G(0) = 0`. Since `F(0) = 0`
(from `hF.1`) and `G(0) = 0` (from `hG.1`), this is `0 + 0 = 0`, which
follows from `add_zero`.

**Slope:** We need:

    F(x + d) + G(x + d) = (F(x) + G(x)) + (f(x) + g(x)) * d

Starting from the left, we expand using the slope conditions:

    F(x + d) + G(x + d) = (F(x) + f(x)*d) + (G(x) + g(x)*d)

Then `right_distrib` rewrites `(f(x) + g(x)) * d` as `f(x)*d + g(x)*d` on
the right side. What remains is rearranging:

    (F(x) + f(x)*d) + (G(x) + g(x)*d)  =  (F(x) + G(x)) + (f(x)*d + g(x)*d)

This is just moving `G(x)` past `f(x)*d` and regrouping parentheses. The four
rewrites in the second line handle the associativity and commutativity steps
one at a time.

Compare this with the sum rule for derivatives in Article 8. The mathematical
content is identical --- expand, regroup, apply the distributive law. The
difference is that here we are working with antiderivatives (functions on all
of `R`) rather than slopes (numbers).

### Uniqueness consequence for addition

```lean
theorem antideriv_add_eq {F G H : R → R} {f g : R → R}
    (hF : IsAntideriv F f) (hG : IsAntideriv G g)
    (hH : IsAntideriv H (fun x => f x + g x)) :
    H = fun x => F x + G x :=
  antideriv_unique hH (antideriv_add hF hG)
```

This is the uniqueness wrapper. If `H` is the antiderivative of `f + g`, and
`F` and `G` are antiderivatives of `f` and `g` respectively, then `H` must
equal `F + G`. The proof: `antideriv_add` shows that `F + G` is an
antiderivative of `f + g`, and `antideriv_unique` says there can be only one.

This is exactly the two-layer architecture from Article 8. Layer 1
(`antideriv_add`) constructs the candidate and verifies it works. Layer 2
(`antideriv_add_eq`) invokes uniqueness. The pattern is clean and modular.

### Scalar multiplication

```lean
theorem antideriv_const_mul {F : R → R} {f : R → R} (c : R)
    (hF : IsAntideriv F f) :
    IsAntideriv (fun x => c * F x) (fun x => c * f x) := by
  constructor
  · show c * F 0 = 0
    rw [hF.1, mul_zero]
  · intro x d
    show c * F (x + d.val) = c * F x + c * f x * d.val
    rw [hF.2 x d, left_distrib, mul_assoc]
```

If `F` is an antiderivative of `f`, then `c * F` is an antiderivative of
`c * f`. The normalization step uses `c * 0 = 0`. The slope step distributes
`c` over the sum and reassociates: `c * (F(x) + f(x)*d) = c*F(x) + c*f(x)*d`
becomes `c*F(x) + (c*f(x))*d` after `mul_assoc`.

This mirrors `deriv_const_mul_slope` from Article 8 almost exactly. The same
algebra, the same two rewrites.

### Negation

```lean
theorem antideriv_neg {F : R → R} {f : R → R}
    (hF : IsAntideriv F f) :
    IsAntideriv (fun x => -(F x)) (fun x => -(f x)) := by
  constructor
  · show -(F 0) = 0
    rw [hF.1, neg_zero]
  · intro x d
    show -(F (x + d.val)) = -(F x) + -(f x) * d.val
    rw [hF.2 x d, neg_add_distrib, neg_mul_left]
```

If `F` is an antiderivative of `f`, then `-F` is an antiderivative of `-f`.
The proof uses `neg_zero` (negation of zero is zero), `neg_add_distrib`
(negation distributes over sums), and `neg_mul_left` (pulling a negation onto
the left factor of a product). These are the same algebraic lemmas used in
`deriv_neg_slope` in Article 8.

### Subtraction

```lean
theorem antideriv_sub {F G : R → R} {f g : R → R}
    (hF : IsAntideriv F f) (hG : IsAntideriv G g) :
    IsAntideriv (fun x => F x - G x) (fun x => f x - g x) := by
  constructor
  · show F 0 - G 0 = 0
    rw [hF.1, hG.1, sub_self]
  · intro x d
    show F (x + d.val) - G (x + d.val) = (F x - G x) + (f x - g x) * d.val
    rw [hF.2 x d, hG.2 x d, sub_mul]
    rw [sub_eq (F x + f x * d.val), sub_eq (F x), sub_eq (f x * d.val)]
    rw [neg_add_distrib]
    rw [add_assoc, ← add_assoc (f x * d.val),
        add_comm (f x * d.val) (-(G x)),
        add_assoc, add_assoc]
```

If `F` is an antiderivative of `f` and `G` is an antiderivative of `g`,
then `F - G` is an antiderivative of `f - g`. This is the longest of the
linearity proofs because subtraction generates more terms that need
rearranging. The `sub_mul` lemma rewrites `(f(x) - g(x)) * d` as
`f(x)*d - g(x)*d`, and then the remaining lines expand subtractions as
additions of negations and shuffle terms into the right order.

The mathematical content is routine: expand both sides, cancel, and regroup.
The Lean proof just makes every algebraic step explicit.

---

## Integral additivity

```lean
theorem integral_additive (F : R → R) (a b c : R) :
    (F b - F a) + (F c - F b) = F c - F a := by
  rw [add_comm, sub_eq (F b) (F a), ← add_assoc, sub_add_cancel, ← sub_eq]
```

This is the theorem that, in integral notation, reads:

    integral from a to b of f + integral from b to c of f = integral from a to c of f

If we define the definite integral as `F(b) - F(a)` where `F` is the
antiderivative, then this becomes:

    (F(b) - F(a)) + (F(c) - F(b)) = F(c) - F(a)

This is pure algebra --- a telescoping sum. The `F(b)` terms cancel. Notice
that the theorem does not even mention `f` or `IsAntideriv`. It is true for
ANY function `F` and ANY points `a`, `b`, `c`. The antiderivative hypothesis
is not needed because this is just arithmetic.

The proof swaps the order of addition (so that `F(c) - F(b)` comes first),
expands the subtraction, reassociates, cancels `F(b)`, and folds back into a
subtraction.

---

## Integration of constant functions

```lean
theorem const_antideriv_slope {F : R → R} (c : R)
    (hF : IsAntideriv F (fun _ => c)) :
    ∀ (x : R) (d : Delta R), F (x + d.val) = F x + c * d.val :=
  hF.2
```

If `F` is the antiderivative of the constant function `c`, then `F` has slope
`c` at every point. This is just extracting the slope condition from
`IsAntideriv`.

You might wonder: should the antiderivative of the constant `c` be
`F(x) = c * x`? It should, and the slope condition confirms that `F` behaves
like `c * x` at the infinitesimal level. But we cannot directly state
`F(x) = c * x` without extracting the multiplication-by-`x` function from the
Kock-Lawvere axiom, which would require `Exists.choose` and classical logic.
So instead we characterize `F` by its slope: it grows at rate `c` everywhere.
This is the conditional approach we have used throughout the project.

---

## Connecting integration back to microaffinity

The final two theorems close the circle between integration and
differentiation by connecting antiderivatives to the microaffinity framework
from Article 6.

```lean
theorem antideriv_microaffine {F f : R → R} (hF : IsAntideriv F f) (x : R) :
    ∀ (d : Delta R), F (x + d.val) = F x + f x * d.val :=
  hF.2 x
```

The antiderivative `F` satisfies the microaffinity equation at every point,
with slope `f(x)`. This is identical to `ftc_part2` above --- the same fact,
restated for emphasis. The antiderivative is microaffine, and its slope at `x`
is `f(x)`.

```lean
theorem antideriv_slope_eq {F f : R → R} (hF : IsAntideriv F f) (x : R) :
    ∀ (a : R), (∀ (d : Delta R), F (x + d.val) = F x + a * d.val) → a = f x := by
  intro a ha
  exact (microaffinity F x).unique ha (hF.2 x)
```

This theorem says: if `F` is an antiderivative of `f`, and some number `a`
also serves as a slope for `F` at the point `x`, then `a` must equal `f(x)`.
The slope of the antiderivative is uniquely determined to be `f(x)`.

The proof uses `microaffinity F x` from Article 6, which tells us that the
slope of `F` at `x` is unique. Both `a` (by hypothesis `ha`) and `f(x)` (by
the antiderivative condition `hF.2 x`) satisfy the slope equation. By
`.unique`, they must be equal.

This closes the circle. We started with microaffinity (Article 6), which
says every function has a unique slope at every point --- giving us
derivatives. Then we added the integration axiom, which says every function
has a unique antiderivative --- giving us integrals. Now `antideriv_slope_eq`
confirms that these two concepts are consistent: the slope of the
antiderivative of `f` is exactly `f`. Differentiation and integration are
inverses, just as in traditional calculus.

---

## The Exists.choose problem, revisited

As with Derivative.lean (Article 8), every theorem in this file is stated
conditionally: "IF `F` is an antiderivative of `f`, THEN ..." We never
extract the antiderivative as a concrete function.

The reason is the same. The integration axiom says `ExistsUnique`: there
exists a unique `F` satisfying the antiderivative conditions. To extract that
`F` as a Lean function, we would need `Exists.choose`, which relies on
`Classical.choice`. And as we proved in Article 6, classical logic is
incompatible with SIA.

So we work around the limitation. Instead of defining a function
`integrate f` that returns the antiderivative, we prove theorems about
any function that happens to be an antiderivative. The integration axiom
guarantees such a function exists (and is unique), so our theorems are not
vacuously true. But we never name or hold the antiderivative as a value.

This is the same design decision as in Article 8, and it works for the same
reason: uniqueness does all the mathematical work. If you want to prove
something about the integral of `f`, you prove it about ANY antiderivative
of `f`, and uniqueness guarantees the result applies to THE antiderivative.

---

## The big picture: FTC in SIA vs. traditional calculus

Let us step back and compare what the Fundamental Theorem of Calculus looks
like in the two settings.

**Traditional calculus.** FTC has two parts, each requiring substantial
machinery:

- *Part 1 (derivative of the integral is the original function):* Define the
  integral via Riemann sums. Prove the limit exists for continuous functions.
  Define `G(x) = integral from 0 to x of f(t) dt`. Prove that
  `G'(x) = f(x)` using the Mean Value Theorem for integrals and a careful
  limit argument.

- *Part 2 (integral of the derivative recovers the function):* Prove that if
  `F' = f`, then `F(b) - F(a) = integral from a to b of f(t) dt`. This
  requires showing that `F - G` has zero derivative everywhere (where `G` is
  the integral function from Part 1), invoking the Mean Value Theorem to
  conclude `F - G` is constant, and evaluating the constant.

Both parts lean heavily on the completeness of the reals (for the existence of
Riemann integrals) and the Mean Value Theorem (for connecting local derivative
information to global function behavior).

**SIA.** The picture is dramatically simpler:

- *FTC Part 2 (derivative of the antiderivative is the original function):*
  This is the definition of `IsAntideriv`. One line: `hF.2 x`.

- *FTC Part 1 (any function with slope f gives the same differences):*
  Shift the candidate by subtracting its value at zero. Use uniqueness of
  antiderivatives. Do algebra. Five lines.

The Mean Value Theorem is not needed. Riemann sums are not needed. The
completeness axiom is not needed. The integration axiom does all the work that
completeness does in the classical setting.

Is this "easier" in some absolute sense? Not exactly. The difficulty has been
relocated, not eliminated. In traditional calculus, the hard work is in
*proving* that antiderivatives exist (via Riemann integration). In SIA, the
existence is *axiomatized*, and the hard work is in justifying the axiom ---
which happens at the level of model theory, not within the formal system
itself.

But for the working mathematician who wants to *use* integration, the SIA
approach is cleaner. You do not need to re-derive existence every time you
integrate a new function. You just invoke the axiom and move on to the
interesting questions.

---

## What this file proves

Let us catalogue the results:

| Theorem | Statement |
|---------|-----------|
| `IsAntideriv` | Definition: F is antiderivative of f means F(0) = 0 and F has slope f(x) at every x |
| `antideriv_unique` | Two antiderivatives of f must be equal |
| `ftc_part2` | The slope of the antiderivative is the original function |
| `shift_is_antideriv` | Shifting F by F(0) gives a proper antiderivative |
| `ftc_part1` | G(b) - G(a) = F(b) - F(a) for any two functions with slope f |
| `zero_is_antideriv_zero` | The zero function is an antiderivative of zero |
| `zero_slope_is_zero` | Zero slope everywhere + F(0) = 0 implies F = 0 |
| `zero_slope_is_const` | Zero slope everywhere implies F is constant |
| `antideriv_add` | Antiderivative of f + g is antiderivative of f + antiderivative of g |
| `antideriv_const_mul` | Antiderivative of c*f is c times antiderivative of f |
| `antideriv_neg` | Antiderivative of -f is negation of antiderivative of f |
| `antideriv_sub` | Antiderivative of f - g is difference of antiderivatives |
| `integral_additive` | (F(b) - F(a)) + (F(c) - F(b)) = F(c) - F(a) |
| `antideriv_slope_eq` | The slope of the antiderivative at x is uniquely f(x) |

Every proof follows one of two patterns:

1. **Direct verification.** Show a candidate satisfies the `IsAntideriv`
   conditions (normalization + slope). This is pure algebra.

2. **Uniqueness.** Two things satisfy the same uniquely-satisfied property,
   therefore they are equal.

These are the same two patterns from Derivative.lean. The file is, in a sense,
a replay of Article 8 at a higher level: where Article 8 proved properties of
slopes (numbers), this file proves properties of antiderivatives (functions).
But the strategy --- construct a candidate, invoke uniqueness --- is identical.

---

## Looking forward

This file is the culmination of the integration story. Starting from the
algebraic axioms (Articles 2--4), through the Kock-Lawvere axiom (Article 5),
the core theorems about infinitesimals (Article 6), continuity (Article 7),
derivatives (Article 8), axiom checking (Article 9), and higher-order
infinitesimals (Article 10), we now have a complete formalization of the two
pillars of calculus: differentiation and integration.

In traditional calculus, the Fundamental Theorem of Calculus is the moment
when two long threads --- the theory of derivatives and the theory of
integrals, developed independently over many chapters --- are finally woven
together. It is a deep and surprising result.

In SIA, the surprise is gone, replaced by clarity. Integration is defined via
antiderivatives. The antiderivative has slope equal to the original function
--- that is the definition. The integral of the derivative recovers the
function --- that follows from uniqueness. The two threads were never
separate; they were always the same thread, viewed from two sides.

The depth of the Fundamental Theorem has not vanished. It has been absorbed
into the integration axiom, which carries the full weight of the classical
theorem. But the formal consequences --- the theorems you actually need to
do calculus --- are simpler, shorter, and more transparent than their
classical counterparts. This is the promise of Smooth Infinitesimal Analysis:
not that calculus becomes trivial, but that the distance between intuition and
rigor becomes small enough to cross in a few lines of algebra.

[Article 12](12-ftc.md) continues the story with `FTC.lean`, which gives
clean, self-contained statements of both parts of the FTC and derives
corollaries: the integral is well-defined, two functions with the same
derivative differ by a constant, and integration by parts.
