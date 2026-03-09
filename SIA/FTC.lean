/-
  SIA.FTC — The Fundamental Theorem of Calculus

  Based on Bell, Chapter 6.

  The two parts of FTC, stated cleanly and connecting derivatives
  (from Derivative.lean) with integration (from Integration.lean):

  Part 1 (Differentiation undoes integration):
    If F is the antiderivative of f, then F has slope f(x) at every x,
    and f(x) is the UNIQUE such slope.  i.e., (∫₀ˣ f)' = f(x).

  Part 2 (Integration undoes differentiation):
    If g has slope f(x) at every x (g' = f), then for any antiderivative F:
    F(b) - F(a) = g(b) - g(a).  i.e., ∫ₐᵇ g' = g(b) - g(a).

  Corollaries:
  - The integral is well-defined (independent of choice of antiderivative)
  - Two functions with the same derivative differ by a constant
  - A function is determined by its derivative and initial value
  - Integration by parts
-/
import SIA.Derivative
import SIA.Integration

universe u

namespace SIA

variable {R : Type u} [SIAIntegral R]
open CommRing StrictOrder ConstructiveOrderedField

-- ═══════════════════════════════════════════════════════
-- Part 1: Differentiation undoes integration
-- (∫₀ˣ f)' = f(x)
-- ═══════════════════════════════════════════════════════

-- If F is the antiderivative of f, then f(x) is the microaffinity slope of F at x.
-- Moreover, this slope is unique: no other value works.
theorem ftc1 {F f : R → R} (hF : IsAntideriv F f) (x : R) :
    (∀ (d : Delta R), F (x + d.val) = F x + f x * d.val) ∧
    (∀ (a : R), (∀ (d : Delta R), F (x + d.val) = F x + a * d.val) → a = f x) :=
  ⟨hF.2 x, fun _ ha => (microaffinity F x).unique ha (hF.2 x)⟩

-- ═══════════════════════════════════════════════════════
-- Part 2: Integration undoes differentiation
-- ∫ₐᵇ g' = g(b) - g(a)
-- ═══════════════════════════════════════════════════════

-- If g has slope f(x) at every x (i.e., g' = f as functions), then the
-- integral of f from a to b equals g(b) - g(a).
theorem ftc2 {g f : R → R}
    (hg : ∀ (x : R) (d : Delta R), g (x + d.val) = g x + f x * d.val)
    {F : R → R} (hF : IsAntideriv F f) :
    ∀ (a b : R), F b - F a = g b - g a :=
  antideriv_eq_any_with_slope hF hg

-- ═══════════════════════════════════════════════════════
-- The integral is well-defined
-- ═══════════════════════════════════════════════════════

-- Any two antiderivatives of the same function give the same integral value.
theorem integral_well_defined {F G f : R → R}
    (hF : IsAntideriv F f) (hG : IsAntideriv G f) :
    ∀ (a b : R), F b - F a = G b - G a := by
  intro a b; rw [antideriv_unique hF hG]

-- ═══════════════════════════════════════════════════════
-- Two functions with the same derivative differ by a constant
-- ═══════════════════════════════════════════════════════

-- If f and g have the same slope at every point, then f - g is constant.
theorem same_deriv_differ_by_const {f g : R → R} {h : R → R}
    (hf : ∀ (x : R) (d : Delta R), f (x + d.val) = f x + h x * d.val)
    (hg : ∀ (x : R) (d : Delta R), g (x + d.val) = g x + h x * d.val) :
    ∀ (x : R), f x - g x = f 0 - g 0 := by
  -- f - g has slope h(x) - h(x) = 0 at every point
  have hfg : ∀ (x : R) (d : Delta R),
      (f (x + d.val) - g (x + d.val)) = (f x - g x) + 0 * d.val := by
    intro x d
    rw [hf x d, hg x d, zero_mul, add_zero]
    rw [sub_eq_add_neg (f x + h x * d.val), sub_eq_add_neg (f x)]
    rw [neg_add_distrib, add_assoc,
        ← add_assoc (h x * d.val), add_comm (h x * d.val) (-(g x)),
        add_assoc (-(g x))]
    congr 1; rw [add_neg, add_zero]
  exact zero_slope_is_const hfg

-- ═══════════════════════════════════════════════════════
-- A function is determined by its derivative and initial value
-- ═══════════════════════════════════════════════════════

-- If f(0) = g(0) and f' = g' everywhere, then f = g.
theorem eq_of_same_deriv_and_initial {f g : R → R} {h : R → R}
    (h_init : f 0 = g 0)
    (hf : ∀ (x : R) (d : Delta R), f (x + d.val) = f x + h x * d.val)
    (hg : ∀ (x : R) (d : Delta R), g (x + d.val) = g x + h x * d.val) :
    ∀ (x : R), f x = g x := by
  intro x
  have hconst := same_deriv_differ_by_const hf hg x
  -- f x - g x = f 0 - g 0 = 0
  have h0 : f 0 - g 0 = 0 := by rw [h_init, sub_self]
  rw [h0] at hconst
  -- f x - g x = 0 implies f x = g x
  calc f x = (f x - g x) + g x := by rw [sub_add_cancel]
    _ = 0 + g x := by rw [hconst]
    _ = g x := by rw [zero_add]

-- ═══════════════════════════════════════════════════════
-- Integration by parts
-- ═══════════════════════════════════════════════════════

-- If F' = f and G' = g, then by the product rule (F*G)' = f*G + F*g.
-- Therefore ∫ₐᵇ (f*G + F*g) = F(b)*G(b) - F(a)*G(a).
-- Rearranging: ∫ₐᵇ f*G = F(b)*G(b) - F(a)*G(a) - ∫ₐᵇ F*g.

-- First: the product F*G has the right slope (product rule)
theorem product_has_slope {F G f g : R → R}
    (hF : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + f x * d.val)
    (hG : ∀ (x : R) (d : Delta R), G (x + d.val) = G x + g x * d.val) :
    ∀ (x : R) (d : Delta R),
      F (x + d.val) * G (x + d.val) =
      F x * G x + (f x * G x + F x * g x) * d.val :=
  fun x d => deriv_mul_slope F G x (f x) (g x) (fun d => hF x d) (fun d => hG x d) d

-- Integration by parts: ∫ₐᵇ (f·G + F·g) = F(b)·G(b) - F(a)·G(a)
theorem integration_by_parts {F G f g : R → R}
    (hF : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + f x * d.val)
    (hG : ∀ (x : R) (d : Delta R), G (x + d.val) = G x + g x * d.val)
    {H : R → R} (hH : IsAntideriv H (fun x => f x * G x + F x * g x)) :
    ∀ (a b : R), H b - H a = F b * G b - F a * G a :=
  ftc2 (product_has_slope hF hG) hH

end SIA
