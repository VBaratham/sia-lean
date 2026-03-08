/-
  SIA.Field — Constructive ordered field

  An ordered field where the ordering is compatible with arithmetic,
  without trichotomy. This is the base algebraic structure for SIA.
-/
import SIA.Algebra
import SIA.Order

universe u

class ConstructiveOrderedField (R : Type u) extends CField R, StrictOrder R where
  zero_lt_one     : (0 : R) < 1
  lt_add_left     : ∀ {a b : R}, a < b → ∀ (c : R), c + a < c + b
  lt_mul_pos_left : ∀ {a b c : R}, 0 < c → a < b → c * a < c * b

namespace ConstructiveOrderedField

variable {R : Type u} [ConstructiveOrderedField R]
open CommRing CField StrictOrder

-- Basic order-arithmetic lemmas

theorem lt_add_right {a b : R} (h : a < b) (c : R) : a + c < b + c := by
  have h1 : c + a < c + b := lt_add_left h c
  rw [add_comm c a, add_comm c b] at h1
  exact h1

theorem le_add_left_of {a b : R} (h : a ≤ b) (c : R) : c + a ≤ c + b := by
  intro hba
  have : -c + (c + b) < -c + (c + a) := lt_add_left hba (-c)
  rw [← add_assoc, neg_add, zero_add, ← add_assoc, neg_add, zero_add] at this
  exact h this

theorem le_add_right_of {a b : R} (h : a ≤ b) (c : R) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]
  exact le_add_left_of h c

theorem lt_neg_flip {a b : R} (h : a < b) : -b < -a := by
  have h1 : -b + a < -b + b := lt_add_left h (-b)
  rw [neg_add] at h1
  have h2 : (-b + a) + -a < 0 + -a := lt_add_right h1 (-a)
  rw [zero_add, add_assoc, add_neg, add_zero] at h2
  exact h2

theorem le_neg_flip {a b : R} (h : a ≤ b) : -b ≤ -a :=
  fun hna => h (by rw [← neg_neg a, ← neg_neg b]; exact lt_neg_flip hna)

theorem neg_lt_zero {a : R} (h : 0 < a) : -a < 0 := by
  have := lt_neg_flip h; rw [neg_zero] at this; exact this

theorem neg_pos {a : R} (h : a < 0) : 0 < -a := by
  have := lt_neg_flip h; rw [neg_zero] at this; exact this

theorem zero_lt_two : (0 : R) < 1 + 1 := by
  have h1 : (0 : R) < 1 := zero_lt_one
  have h2 : 1 + (0 : R) < 1 + 1 := lt_add_left h1 1
  rw [add_zero] at h2
  exact lt_trans h1 h2

theorem two_ne_zero : (1 + 1 : R) ≠ 0 :=
  Ne.symm (lt_ne zero_lt_two)

theorem one_div_pos_of_pos {c : R} (hc : 0 < c) : 0 < 1 / c := by
  have c_ne : c ≠ 0 := Ne.symm (lt_ne hc)
  have inv_ne : c⁻¹ ≠ 0 := CField.inv_ne_zero c_ne
  have one_div_eq : 1 / c = c⁻¹ := by rw [CField.div_eq_mul_inv, one_mul]
  rw [one_div_eq]
  exact (ne_lt inv_ne).elim
    (fun h => by
      have : c * c⁻¹ < c * 0 := lt_mul_pos_left hc h
      rw [CField.mul_inv c_ne, mul_zero] at this
      exact absurd (lt_trans zero_lt_one this) (lt_irrefl 0))
    id

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

end ConstructiveOrderedField
