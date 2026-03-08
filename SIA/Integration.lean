/-
  SIA.Integration — Integration and the Fundamental Theorem of Calculus

  In SIA, integration is characterized by the integration axiom: every function
  f : R → R has a unique antiderivative F with F(0) = 0 and slope f(x) at every x.

  The Fundamental Theorem of Calculus is essentially built into this framework:
  - FTC Part 1 (derivative of the integral is the original function) is the definition
  - FTC Part 2 (integral of the derivative recovers the function) follows from uniqueness

  We also prove linearity and additivity of integration.

  IMPORTANT: As with Derivative.lean, we avoid Exists.choose. We never extract
  the antiderivative as a function. Instead, we state properties conditionally:
  "if F is an antiderivative of f, then..."
-/
import SIA.Delta

universe u

namespace SIA

variable {R : Type u}
open CommRing StrictOrder

-- ═══════════════════════════════════════════════════════
-- Definition of antiderivative
-- ═══════════════════════════════════════════════════════

-- F is an antiderivative of f: F(0) = 0 and F has slope f(x) at every x
def IsAntideriv [SIA R] (F f : R → R) : Prop :=
  F 0 = 0 ∧ ∀ (x : R) (d : Delta R), F (x + d.val) = F x + f x * d.val

end SIA

-- ═══════════════════════════════════════════════════════
-- The integration axiom
-- ═══════════════════════════════════════════════════════

-- Extended SIA with the integration axiom: every function has a unique antiderivative
class SIAIntegral (R : Type u) extends SIA R where
  integration : ∀ (f : R → R),
    SIA.ExistsUnique fun (F : R → R) => SIA.IsAntideriv F f

namespace SIA

variable {R : Type u} [SIAIntegral R]
open CommRing StrictOrder ConstructiveOrderedField

-- ═══════════════════════════════════════════════════════
-- Uniqueness of antiderivatives
-- ═══════════════════════════════════════════════════════

-- If two functions are both antiderivatives of f, they must be equal
theorem antideriv_unique {F G f : R → R}
    (hF : IsAntideriv F f) (hG : IsAntideriv G f) : F = G :=
  (SIAIntegral.integration f).unique hF hG

-- ═══════════════════════════════════════════════════════
-- FTC Part 2: The slope of an antiderivative is the original function
-- ═══════════════════════════════════════════════════════

-- If F is the antiderivative of f, then F has slope f(x) at every x
-- (This is literally the definition of IsAntideriv, stated for clarity)
theorem ftc_part2 {F f : R → R} (hF : IsAntideriv F f) (x : R) :
    ∀ (d : Delta R), F (x + d.val) = F x + f x * d.val :=
  hF.2 x

-- ═══════════════════════════════════════════════════════
-- FTC Part 1: Functions with the same derivative differ by a constant
-- ═══════════════════════════════════════════════════════

-- If F has slope f(x) at every x, then (fun x => F x - F 0) is an antiderivative of f
theorem shift_is_antideriv {F f : R → R}
    (hslope : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + f x * d.val) :
    IsAntideriv (fun x => F x - F 0) f := by
  constructor
  · exact sub_self (F 0)
  · intro x d
    show F (x + d.val) - F 0 = (F x - F 0) + f x * d.val
    rw [hslope x d]
    -- Goal: (F x + f x * d.val) - F 0 = (F x - F 0) + f x * d.val
    rw [sub_eq_add_neg (F x + f x * d.val), sub_eq_add_neg (F x)]
    -- Goal: (F x + f x * d.val) + -(F 0) = (F x + -(F 0)) + f x * d.val
    rw [add_assoc, add_comm (f x * d.val) (-(F 0)), ← add_assoc]

-- Helper: (a - c) - (b - c) = a - b
private theorem sub_sub_cancel_right (a b c : R) : (a - c) - (b - c) = a - b := by
  calc (a - c) - (b - c)
      = (a - c) + (-(b - c)) := by rw [sub_eq_add_neg]
    _ = (a - c) + (c - b) := by rw [neg_sub]
    _ = (a - c) + (c + -(b)) := by rw [sub_eq_add_neg c b]
    _ = ((a - c) + c) + -(b) := by rw [← add_assoc]
    _ = a + -(b) := by rw [sub_add_cancel]
    _ = a - b := by rw [← sub_eq_add_neg]

-- FTC Part 1: If G is the antiderivative of f, and F also has slope f(x)
-- everywhere, then G(b) - G(a) = F(b) - F(a) for all a, b.
-- In other words: ∫_a^b f = F(b) - F(a) for any F with F' = f.
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

-- ═══════════════════════════════════════════════════════
-- A function with zero slope everywhere is constant
-- ═══════════════════════════════════════════════════════

-- The zero function is an antiderivative of the zero function
theorem zero_is_antideriv_zero : IsAntideriv (fun (_ : R) => (0 : R)) (fun (_ : R) => (0 : R)) := by
  constructor
  · rfl
  · intro x d; rw [zero_mul, add_zero]

-- If F has slope 0 everywhere and F(0) = 0, then F is the zero function
theorem zero_slope_is_zero {F : R → R}
    (hF0 : F 0 = 0)
    (hslope : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + (0 : R) * d.val) :
    F = fun _ => 0 := by
  have hF : IsAntideriv F (fun _ => 0) := ⟨hF0, fun x d => hslope x d⟩
  exact antideriv_unique hF zero_is_antideriv_zero

-- Corollary: if F has slope 0 everywhere, then F is constant (F = fun _ => F 0)
theorem zero_slope_is_const {F : R → R}
    (hslope : ∀ (x : R) (d : Delta R), F (x + d.val) = F x + (0 : R) * d.val) :
    ∀ (x : R), F x = F 0 := by
  have hH : IsAntideriv (fun x => F x - F 0) (fun _ => 0) := by
    constructor
    · exact sub_self (F 0)
    · intro x d
      show F (x + d.val) - F 0 = (F x - F 0) + (0 : R) * d.val
      rw [hslope x d, sub_eq_add_neg (F x + (0 : R) * d.val), sub_eq_add_neg (F x)]
      rw [add_assoc, add_comm ((0 : R) * d.val) (-(F 0)), ← add_assoc]
  have heq := antideriv_unique hH zero_is_antideriv_zero
  intro x
  have : F x - F 0 = 0 := congrFun heq x
  calc F x = (F x - F 0) + F 0 := by rw [sub_add_cancel]
    _ = 0 + F 0 := by rw [this]
    _ = F 0 := by rw [zero_add]

-- ═══════════════════════════════════════════════════════
-- Linearity of antiderivatives
-- ═══════════════════════════════════════════════════════

-- The sum of antiderivatives is an antiderivative of the sum
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

-- Uniqueness consequence: if H is the antiderivative of f+g,
-- and F, G are antiderivatives of f, g, then H = F + G
theorem antideriv_add_eq {F G H : R → R} {f g : R → R}
    (hF : IsAntideriv F f) (hG : IsAntideriv G g)
    (hH : IsAntideriv H (fun x => f x + g x)) :
    H = fun x => F x + G x :=
  antideriv_unique hH (antideriv_add hF hG)

-- Scalar multiplication of an antiderivative
theorem antideriv_const_mul {F : R → R} {f : R → R} (c : R)
    (hF : IsAntideriv F f) :
    IsAntideriv (fun x => c * F x) (fun x => c * f x) := by
  constructor
  · show c * F 0 = 0
    rw [hF.1, mul_zero]
  · intro x d
    show c * F (x + d.val) = c * F x + c * f x * d.val
    rw [hF.2 x d, left_distrib, mul_assoc]

-- Negation of an antiderivative
theorem antideriv_neg {F : R → R} {f : R → R}
    (hF : IsAntideriv F f) :
    IsAntideriv (fun x => -(F x)) (fun x => -(f x)) := by
  constructor
  · show -(F 0) = 0
    rw [hF.1, neg_zero]
  · intro x d
    show -(F (x + d.val)) = -(F x) + -(f x) * d.val
    rw [hF.2 x d, neg_add_distrib, neg_mul_left]

-- Subtraction of antiderivatives
theorem antideriv_sub {F G : R → R} {f g : R → R}
    (hF : IsAntideriv F f) (hG : IsAntideriv G g) :
    IsAntideriv (fun x => F x - G x) (fun x => f x - g x) := by
  constructor
  · show F 0 - G 0 = 0
    rw [hF.1, hG.1, sub_self]
  · intro x d
    show F (x + d.val) - G (x + d.val) = (F x - G x) + (f x - g x) * d.val
    rw [hF.2 x d, hG.2 x d, sub_mul]
    rw [sub_eq_add_neg (F x + f x * d.val), sub_eq_add_neg (F x), sub_eq_add_neg (f x * d.val)]
    rw [neg_add_distrib]
    rw [add_assoc, ← add_assoc (f x * d.val),
        add_comm (f x * d.val) (-(G x)),
        add_assoc, add_assoc]

-- ═══════════════════════════════════════════════════════
-- Integral additivity
-- ═══════════════════════════════════════════════════════

-- ∫_a^b f + ∫_b^c f = ∫_a^c f  (where ∫_a^b f := F(b) - F(a))
-- This is pure algebra — true for any function F, not just antiderivatives.
theorem integral_additive (F : R → R) (a b c : R) :
    (F b - F a) + (F c - F b) = F c - F a := by
  rw [add_comm, sub_eq_add_neg (F b) (F a), ← add_assoc, sub_add_cancel, ← sub_eq_add_neg]

-- ═══════════════════════════════════════════════════════
-- Integration of constant functions
-- ═══════════════════════════════════════════════════════

-- The antiderivative of the constant function c is (fun x => c * x)
-- ...but we can't directly define multiplication by x without extracting from KL.
-- Instead, we show that if F is the antiderivative of (fun _ => c), then
-- F has slope c at every point.
theorem const_antideriv_slope {F : R → R} (c : R)
    (hF : IsAntideriv F (fun _ => c)) :
    ∀ (x : R) (d : Delta R), F (x + d.val) = F x + c * d.val :=
  hF.2

-- ═══════════════════════════════════════════════════════
-- Integration preserves the microaffinity slope
-- ═══════════════════════════════════════════════════════

-- The antiderivative has a well-defined slope at every point (which is f)
-- This connects integration back to microaffinity
theorem antideriv_microaffine {F f : R → R} (hF : IsAntideriv F f) (x : R) :
    ∀ (d : Delta R), F (x + d.val) = F x + f x * d.val :=
  hF.2 x

-- The slope of the antiderivative equals f(x) (by uniqueness of slopes)
theorem antideriv_slope_eq {F f : R → R} (hF : IsAntideriv F f) (x : R) :
    ∀ (a : R), (∀ (d : Delta R), F (x + d.val) = F x + a * d.val) → a = f x := by
  intro a ha
  exact (microaffinity F x).unique ha (hF.2 x)

end SIA
