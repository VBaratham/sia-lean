# Article 12: FTC.lean --- The Fundamental Theorem of Calculus

*Corresponds to Bell, Chapter 6.*

Article 11 built the integration machinery: the definition of antiderivative,
the integration axiom, both parts of the Fundamental Theorem, linearity, and
the connection back to microaffinity. All of that lives in `Integration.lean`.

This article covers `FTC.lean`, a separate file that gives clean, self-contained
statements of the two parts of the Fundamental Theorem and then derives several
corollaries: the integral is well-defined (independent of antiderivative
choice), two functions with the same derivative differ by a constant, a
function is determined by its derivative and initial value, and integration
by parts.

The separation is deliberate. `Integration.lean` is where the proofs happen.
`FTC.lean` is where the results are packaged for use. If you just want to
*apply* the Fundamental Theorem, this is the file you read.

---

## Setup

```lean
import SIA.Derivative
import SIA.Integration

universe u

namespace SIA

variable {R : Type u} [SIAIntegral R]
open CommRing StrictOrder ConstructiveOrderedField
```

This file imports both `Derivative` and `Integration`. It is the first file
in the project to bring both threads together --- the theory of derivatives
(slopes, the product rule, the chain rule) and the theory of integration
(antiderivatives, uniqueness, linearity).

The variable `[SIAIntegral R]` assumes the full axiom system: commutative
ring, constructive ordered field, the Kock-Lawvere axiom, and the integration
axiom. Everything we have built is available.

---

## Part 1: Differentiation undoes integration

```lean
theorem ftc1 {F f : R → R} (hF : IsAntideriv F f) (x : R) :
    (∀ (d : Delta R), F (x + d.val) = F x + f x * d.val) ∧
    (∀ (a : R), (∀ (d : Delta R), F (x + d.val) = F x + a * d.val) → a = f x) :=
  ⟨hF.2 x, fun _ ha => (microaffinity F x).unique ha (hF.2 x)⟩
```

In traditional notation, this says: if F is the antiderivative of f, then
F'(x) = f(x), and moreover f(x) is the *unique* slope of F at x.

The theorem returns a conjunction (an "and"): two facts packaged together.

**First component:** `F(x + d) = F(x) + f(x) * d` for all infinitesimals d.
This is the slope condition from `IsAntideriv`, extracted via `hF.2 x`. It
says f(x) is *a* slope of F at x.

**Second component:** If some number `a` also satisfies the slope equation
for F at x, then `a = f(x)`. This is uniqueness, proved by invoking
`microaffinity F x` from Article 6. The microaffinity theorem says every
function has a *unique* slope at every point. Both `a` (by hypothesis `ha`)
and `f(x)` (by the antiderivative condition `hF.2 x`) satisfy the slope
equation. By `.unique`, they must be equal.

The proof is a single term: an anonymous constructor `⟨..., ...⟩` building
the pair. No tactics needed.

This is essentially a repackaging of results from `Integration.lean`
(`antideriv_microaffine` and `antideriv_slope_eq`), but the statement is cleaner: one
theorem that says both "f(x) is the slope" and "f(x) is the only slope."

---

## Part 2: Integration undoes differentiation

```lean
theorem ftc2 {g f : R → R}
    (hg : ∀ (x : R) (d : Delta R), g (x + d.val) = g x + f x * d.val)
    {F : R → R} (hF : IsAntideriv F f) :
    ∀ (a b : R), F b - F a = g b - g a :=
  antideriv_eq_any_with_slope hF hg
```

In traditional notation: if g'(x) = f(x) for all x, then the integral of f
from a to b equals g(b) - g(a). That is:

    integral from a to b of g'(x) dx = g(b) - g(a)

The hypothesis `hg` says that g has slope f(x) at every point --- in other
words, g is an antiderivative of f in the derivative sense (though not
necessarily normalized so that g(0) = 0). The hypothesis `hF` says F is the
canonical antiderivative of f (with F(0) = 0).

The conclusion says `F(b) - F(a) = g(b) - g(a)`. Since `F(b) - F(a)` is the
natural definition of the definite integral (the antiderivative evaluated at
the endpoints), this says the integral equals `g(b) - g(a)`.

The proof is a direct call to `antideriv_eq_any_with_slope` from `Integration.lean`. The
mathematical content --- shifting g by g(0), using uniqueness to equate it
with F, doing the algebra --- was all handled there. This theorem just
provides a clean interface.

---

## The integral is well-defined

```lean
theorem integral_well_defined {F G f : R → R}
    (hF : IsAntideriv F f) (hG : IsAntideriv G f) :
    ∀ (a b : R), F b - F a = G b - G a := by
  intro a b; rw [antideriv_unique hF hG]
```

If F and G are both antiderivatives of the same function f, then they give
the same integral values: `F(b) - F(a) = G(b) - G(a)`.

This might seem trivially obvious --- if F = G, then of course
`F(b) - F(a) = G(b) - G(a)`. And that is exactly the proof: `antideriv_unique`
gives us `F = G`, and `rw` rewrites F to G.

But the theorem is worth stating explicitly because it captures an important
mathematical point. In traditional calculus, the definite integral is defined
via Riemann sums, and you must prove it is well-defined (the limit exists and
does not depend on the choice of partition). Here, the integral is defined via
antiderivatives, and well-definedness means it does not depend on which
antiderivative you use. The integration axiom guarantees there is only one
(normalized) antiderivative, so this is automatic.

---

## Two functions with the same derivative differ by a constant

```lean
theorem same_deriv_differ_by_const {f g : R → R} {h : R → R}
    (hf : ∀ (x : R) (d : Delta R), f (x + d.val) = f x + h x * d.val)
    (hg : ∀ (x : R) (d : Delta R), g (x + d.val) = g x + h x * d.val) :
    ∀ (x : R), f x - g x = f 0 - g 0 := by
  have hfg : ∀ (x : R) (d : Delta R),
      (f (x + d.val) - g (x + d.val)) = (f x - g x) + (0 : R) * d.val := by
    intro x d
    rw [hf x d, hg x d, zero_mul, add_zero]
    rw [sub_eq_add_neg (f x + h x * d.val), sub_eq_add_neg (f x)]
    rw [neg_add_distrib, add_assoc,
        ← add_assoc (h x * d.val), add_comm (h x * d.val) (-(g x)),
        add_assoc (-(g x))]
    congr 1; rw [add_neg, add_zero]
  exact zero_slope_is_const hfg
```

If f and g have the same slope h(x) at every point, then f - g is constant.
Specifically, `f(x) - g(x) = f(0) - g(0)` for all x.

This is a classic result in calculus: two functions with the same derivative
differ by a constant. The traditional proof uses the Mean Value Theorem. Our
proof uses the integration axiom, via `zero_slope_is_const` from
`Integration.lean`.

The strategy: show that f - g has slope 0 at every point, then apply
`zero_slope_is_const` to conclude f - g is constant.

**Showing f - g has slope 0.** We need:

    (f(x + d) - g(x + d)) = (f(x) - g(x)) + 0 * d

The left side expands to `(f(x) + h(x)*d) - (g(x) + h(x)*d)` using the
slope hypotheses. The h(x)*d terms cancel --- this is where `congr 1` comes
in. The tactic `congr 1` says: the outer structure of both sides matches (both
are additions with the same first argument), so it suffices to show the second
arguments are equal. The second arguments are `h(x)*d + (-(h(x)*d))` on the
left and `0` on the right, which is `add_neg`.

**Applying `zero_slope_is_const`.** Once we know f - g has slope 0 everywhere,
`zero_slope_is_const` tells us it is constant: `(f(x) - g(x)) = (f(0) - g(0))`
for all x.

---

## A function is determined by its derivative and initial value

```lean
theorem eq_of_same_deriv_and_initial {f g : R → R} {h : R → R}
    (h_init : f 0 = g 0)
    (hf : ∀ (x : R) (d : Delta R), f (x + d.val) = f x + h x * d.val)
    (hg : ∀ (x : R) (d : Delta R), g (x + d.val) = g x + h x * d.val) :
    ∀ (x : R), f x = g x := by
  intro x
  have hconst := same_deriv_differ_by_const hf hg x
  have h0 : f 0 - g 0 = 0 := by rw [h_init, sub_self]
  rw [h0] at hconst
  calc f x = (f x - g x) + g x := by rw [sub_add_cancel]
    _ = 0 + g x := by rw [hconst]
    _ = g x := by rw [zero_add]
```

If f(0) = g(0) and f and g have the same derivative everywhere, then f = g.

This is an immediate corollary of `same_deriv_differ_by_const`. If f - g is
constant and the constant is f(0) - g(0) = 0, then f(x) - g(x) = 0 for all
x, which means f(x) = g(x).

The proof:
1. `same_deriv_differ_by_const` gives us `f(x) - g(x) = f(0) - g(0)`.
2. `h_init` and `sub_self` give us `f(0) - g(0) = 0`.
3. Substituting: `f(x) - g(x) = 0`.
4. The `calc` block recovers `f(x) = g(x)` by adding g(x) to both sides.

This theorem says that in SIA, a function is completely determined by two
pieces of data: its derivative and its value at a single point. In traditional
calculus, this is the existence and uniqueness theorem for first-order ODEs
(the special case where the ODE is y' = h(x)). The traditional proof uses
the Picard-Lindelof theorem, which requires Lipschitz conditions and a
fixed-point argument. Here, it falls out of the integration axiom in a few
lines.

---

## Integration by parts

The final section proves integration by parts. This requires the product rule
from `Derivative.lean`, connecting the two pillars of the project.

### The product rule for slopes

```lean
theorem product_has_slope {F G f g : R → R}
    (hF : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + f x * d.val)
    (hG : ∀ (x : R) (d : Delta R), G (x + d.val) = G x + g x * d.val) :
    ∀ (x : R) (d : Delta R),
      F (x + d.val) * G (x + d.val) =
      F x * G x + (f x * G x + F x * g x) * d.val :=
  fun x d => deriv_mul_slope F G x (f x) (g x) (fun d => hF x d) (fun d => hG x d) d
```

If F has slope f(x) and G has slope g(x) at every point, then the product
F*G has slope f(x)*G(x) + F(x)*g(x) at every point. This is the Leibniz
product rule: (FG)' = F'G + FG'.

The proof delegates to `deriv_mul_slope` from `Derivative.lean` (Article 8).
That theorem proved the product rule for slopes at a single point. Here we
apply it at every point x, wrapping the pointwise result into a universal
statement.

The lambda `fun x d => deriv_mul_slope ...` takes a point x and an
infinitesimal d and returns the product rule identity at that point. The
arguments `(fun d => hF x d)` and `(fun d => hG x d)` specialize the slope
hypotheses to the specific point x, matching the signature that
`deriv_mul_slope` expects.

### The integration by parts formula

```lean
theorem integration_by_parts {F G f g : R → R}
    (hF : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + f x * d.val)
    (hG : ∀ (x : R) (d : Delta R), G (x + d.val) = G x + g x * d.val)
    {H : R → R} (hH : IsAntideriv H (fun x => f x * G x + F x * g x)) :
    ∀ (a b : R), H b - H a = F b * G b - F a * G a :=
  ftc2 (product_has_slope hF hG) hH
```

In traditional notation, integration by parts says:

    integral from a to b of (f'*g + f*g') dx = f(b)*g(b) - f(a)*g(a)

Or rearranging (the form you probably remember from calculus):

    integral of f'*g = f*g - integral of f*g'

Our theorem states the un-rearranged form: the integral of (f'G + Fg') equals
F(b)G(b) - F(a)G(a). The hypotheses say F has slope f, G has slope g, and H
is the antiderivative of f*G + F*g.

The proof is a single call to `ftc2`. The product rule (`product_has_slope`)
tells us that F*G has slope f*G + F*g at every point. So F*G is a function
whose derivative is f*G + F*g. By `ftc2`, the integral of f*G + F*g from a to
b equals (F*G)(b) - (F*G)(a) = F(b)*G(b) - F(a)*G(a).

This is one of the most elegant proofs in the project. Integration by parts,
which in traditional calculus requires careful manipulation of Riemann sums or
a technical application of the product rule followed by the FTC, here reduces
to: "the product rule says FG has the right slope, so by FTC2, the integral
is FG evaluated at the endpoints." One line.

---

## Summary

FTC.lean is a short file --- six theorems and a helper --- but it brings
together every strand of the project:

| Theorem | Statement | Uses |
|---------|-----------|------|
| `ftc1` | (integral of f)' = f(x), uniquely | IsAntideriv + microaffinity |
| `ftc2` | integral of g' = g(b) - g(a) | antideriv_eq_any_with_slope from Integration.lean |
| `integral_well_defined` | Integral independent of antiderivative choice | antideriv_unique |
| `same_deriv_differ_by_const` | Same derivative implies differ by constant | zero_slope_is_const |
| `eq_of_same_deriv_and_initial` | Derivative + initial value determines function | same_deriv_differ_by_const |
| `integration_by_parts` | integral of (f'g + fg') = f(b)g(b) - f(a)g(a) | product rule + ftc2 |

The dependency chain runs through the entire project:

- **Algebra** (Articles 2--4) provides the ring and field operations.
- **Kock-Lawvere** (Article 5) provides microaffinity and microcancellation.
- **Delta** (Article 6) provides the properties of infinitesimals.
- **Derivatives** (Article 8) provides the product rule.
- **Integration** (Article 11) provides antiderivatives and their uniqueness.
- **FTC** (this article) ties everything together.

Every theorem in this file compiles without `Classical.choice`. The entire
development --- from the axioms of a commutative ring through the Fundamental
Theorem of Calculus and integration by parts --- is constructive. Lean's type
checker has verified every step.

This is the capstone of the project. Starting from a handful of axioms about
an ordered field with nilsquare infinitesimals, we have built the core of
calculus: derivatives, derivative rules, continuity, integration, and the
Fundamental Theorem. All without limits, all without classical logic, all
machine-checked.
