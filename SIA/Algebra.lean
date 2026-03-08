/-
  SIA.Algebra — Basic algebraic structures without Mathlib

  We define CommRing and Field from scratch, since Lean 4 without Mathlib
  only provides the operation typeclasses (Add, Mul, etc.) but no algebraic
  structure classes.

  Not directly from Bell — this is prerequisite infrastructure that Bell assumes.
-/

universe u

class CommRing (R : Type u) extends Add R, Mul R, Neg R, Sub R, Zero R, One R where
  add_assoc     : ∀ (a b c : R), (a + b) + c = a + (b + c)
  add_comm      : ∀ (a b : R), a + b = b + a
  add_zero      : ∀ (a : R), a + 0 = a
  add_neg       : ∀ (a : R), a + (-a) = 0
  sub_eq_add_neg : ∀ (a b : R), a - b = a + (-b)
  mul_assoc     : ∀ (a b c : R), (a * b) * c = a * (b * c)
  mul_comm      : ∀ (a b : R), a * b = b * a
  mul_one       : ∀ (a : R), a * 1 = a
  left_distrib  : ∀ (a b c : R), a * (b + c) = a * b + a * c

namespace CommRing

variable {R : Type u} [CommRing R]

-- Derived via commutativity
theorem zero_add (a : R) : 0 + a = a := by rw [add_comm, add_zero]
theorem neg_add (a : R) : (-a) + a = 0 := by rw [add_comm, add_neg]
theorem one_mul (a : R) : 1 * a = a := by rw [mul_comm, mul_one]
theorem right_distrib (a b c : R) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

-- Cancellation (needed to derive mul_zero)
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add, zero_add]

theorem add_neg_cancel_left (a b : R) : a + (-a + b) = b := by
  rw [← add_assoc, add_neg, zero_add]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have : -a + (a + b) = -a + (a + c) := by rw [h]
  rw [neg_add_cancel_left, neg_add_cancel_left] at this
  exact this

-- Derived: mul_zero (a * 0 + a * 0 = a * (0 + 0) = a * 0 = a * 0 + 0, cancel)
theorem mul_zero (a : R) : a * 0 = 0 :=
  add_left_cancel (by rw [add_zero, ← left_distrib, add_zero] :
    a * 0 + a * 0 = a * 0 + 0)

theorem zero_mul (a : R) : 0 * a = 0 := by rw [mul_comm, mul_zero]

-- Derived: neg_unique, neg_neg, neg_zero
theorem neg_unique {a b : R} (h : a + b = 0) : b = -a := by
  calc b = 0 + b := by rw [zero_add]
    _ = ((-a) + a) + b := by rw [neg_add]
    _ = (-a) + (a + b) := by rw [add_assoc]
    _ = (-a) + 0 := by rw [h]
    _ = -a := by rw [add_zero]

theorem neg_neg (a : R) : -(-a) = a :=
  (neg_unique (neg_add a)).symm

theorem neg_zero : (-0 : R) = 0 :=
  (neg_unique (add_zero 0)).symm

-- Derived: neg_mul_left (a*b + (-a)*b = (a+(-a))*b = 0*b = 0)
theorem neg_mul_left (a b : R) : -(a * b) = (-a) * b :=
  (neg_unique (by rw [← right_distrib, add_neg, zero_mul])).symm

theorem neg_mul_right (a b : R) : -(a * b) = a * (-b) := by
  rw [mul_comm, neg_mul_left, mul_comm]

-- Mark key lemmas for simp
attribute [simp] add_zero zero_add add_neg neg_add mul_one one_mul mul_zero zero_mul
                 neg_neg neg_zero

-- Useful derived lemmas
@[simp] theorem sub_self (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg]

theorem neg_add_distrib (a b : R) : -(a + b) = -a + -b := by
  have h : (a + b) + (-a + -b) = 0 := by
    calc (a + b) + (-a + -b)
      = a + (b + (-a + -b)) := by rw [add_assoc]
    _ = a + ((b + -a) + -b) := by rw [add_assoc]
    _ = a + ((-a + b) + -b) := by rw [add_comm b (-a)]
    _ = a + (-a + (b + -b)) := by rw [add_assoc]
    _ = a + (-a + 0) := by rw [add_neg]
    _ = a + -a := by rw [add_zero]
    _ = 0 := by rw [add_neg]
  exact (neg_unique h).symm

theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  calc (-a) * (-b) = -(a * (-b)) := by rw [← neg_mul_left]
    _ = -(-(a * b)) := by rw [← neg_mul_right]
    _ = a * b := by rw [neg_neg]

theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, sub_eq_add_neg, left_distrib, neg_mul_right]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, sub_eq_add_neg, right_distrib, neg_mul_left]

theorem add_right_cancel {a b c : R} (h : a + c = b + c) : a = b := by
  have : (a + c) + -c = (b + c) + -c := by rw [h]
  rw [add_assoc, add_neg, add_zero, add_assoc, add_neg, add_zero] at this
  exact this

theorem sub_add_cancel (a b : R) : a - b + b = a := by
  rw [sub_eq_add_neg, add_assoc, neg_add, add_zero]

theorem add_sub_cancel (a b : R) : a + b - b = a := by
  rw [sub_eq_add_neg, add_assoc, add_neg, add_zero]

@[simp] theorem sub_zero (a : R) : a - 0 = a := by
  rw [sub_eq_add_neg, neg_zero, add_zero]

@[simp] theorem zero_sub (a : R) : 0 - a = -a := by
  rw [sub_eq_add_neg, zero_add]

theorem neg_sub (a b : R) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add_distrib, neg_neg, add_comm]

end CommRing

-- Note: a standard field also requires 0 ≠ 1 (nontriviality). We omit this
-- because ConstructiveOrderedField provides it via zero_lt_one.
class CField (R : Type u) extends CommRing R, Inv R, Div R where
  div_eq_mul_inv : ∀ (a b : R), a / b = a * b⁻¹
  mul_inv     : ∀ {a : R}, a ≠ 0 → a * a⁻¹ = 1
  inv_zero    : (0 : R)⁻¹ = 0

namespace CField

variable {R : Type u} [CField R]

theorem inv_mul {a : R} (h : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [CommRing.mul_comm, mul_inv h]

theorem inv_ne_zero {a : R} (h : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro hinv
  have h1 : a * a⁻¹ = 1 := mul_inv h
  rw [hinv, CommRing.mul_zero] at h1
  -- h1 : 0 = 1, so a = a * 1 = a * 0 = 0, contradicting h
  exact h (by
    calc a = a * 1 := by rw [CommRing.mul_one]
      _ = a * 0 := by rw [← h1]
      _ = 0 := by rw [CommRing.mul_zero])

theorem mul_div_cancel {a : R} (b : R) (h : a ≠ 0) : b / a * a = b := by
  rw [div_eq_mul_inv, CommRing.mul_assoc, inv_mul h, CommRing.mul_one]

theorem div_mul_cancel {a : R} (b : R) (h : a ≠ 0) : a * (b / a) = b := by
  rw [div_eq_mul_inv, CommRing.mul_comm b, ← CommRing.mul_assoc, mul_inv h, CommRing.one_mul]

theorem mul_inv_cancel_left {a b : R} (h : a ≠ 0) : a⁻¹ * (a * b) = b := by
  rw [← CommRing.mul_assoc, inv_mul h, CommRing.one_mul]

end CField
