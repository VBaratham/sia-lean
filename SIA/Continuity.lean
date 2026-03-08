/-
  SIA.Continuity — All functions are continuous

  In SIA, "neighbors" a b means (a - b)² = 0 (i.e., a - b is in Delta).
  We prove every function R → R preserves the neighbor relation.
  We also show the neighbor relation is symmetric but NOT transitive.
-/
import SIA.Delta

universe u

namespace SIA

variable {R : Type u} [SIA R]
open CommRing StrictOrder ConstructiveOrderedField

-- Two elements are neighbors if their difference is in Delta
def Neighbors (a b : R) : Prop := (a - b) * (a - b) = 0

theorem neighbors_refl (a : R) : Neighbors a a := by
  show (a - a) * (a - a) = 0
  rw [sub_self, zero_mul]

theorem neighbors_symm {a b : R} (h : Neighbors a b) : Neighbors b a := by
  show (b - a) * (b - a) = 0
  rw [← neg_sub a b, neg_mul_neg]
  exact h

-- The neighbor relation is NOT transitive (this would make Delta microstable)
theorem neighbors_not_transitive :
    ¬ (∀ {a b c : R}, Neighbors a b → Neighbors b c → Neighbors a c) := by
  intro h_trans
  have : Microstable (fun (r : R) => r * r = 0) := by
    intro ⟨a, ha⟩ d
    have n_a0 : Neighbors a 0 := by
      show (a - 0) * (a - 0) = 0
      rw [sub_zero]; exact ha
    have n_0neg : Neighbors 0 (-d.val) := by
      show (0 - -d.val) * (0 - -d.val) = 0
      rw [sub_eq_add_neg, neg_neg, zero_add]
      exact d.property
    have n_aneg : Neighbors a (-d.val) := h_trans n_a0 n_0neg
    show (a + d.val) * (a + d.val) = 0
    have : (a - -d.val) * (a - -d.val) = 0 := n_aneg
    rw [sub_eq_add_neg, neg_neg] at this
    exact this
  exact delta_not_microstable this

-- Every function R → R is continuous (preserves neighbors)
theorem all_continuous (f : R → R) :
    ∀ (x y : R), Neighbors x y → Neighbors (f x) (f y) := by
  intro x y hxy
  let d_val := x - y
  have d_sq : d_val * d_val = 0 := hxy
  let d : Delta R := ⟨d_val, d_sq⟩
  have hx_eq : x = y + d.val := by
    show x = y + (x - y)
    have : y + (x - y) = y + (x + -y) := by rw [sub_eq_add_neg]
    rw [this, add_comm x, ← add_assoc, add_neg, zero_add]
  obtain ⟨a, ha, _⟩ := microaffinity f y
  have hfd : f x = f y + a * d.val := by rw [hx_eq]; exact ha d
  show (f x - f y) * (f x - f y) = 0
  have diff_eq : f x - f y = a * d.val := by
    calc f x - f y = (f y + a * d.val) - f y := by rw [hfd]
      _ = (f y + a * d.val) + -(f y) := by rw [sub_eq_add_neg]
      _ = (a * d.val + f y) + -(f y) := by rw [add_comm (f y)]
      _ = a * d.val + (f y + -(f y)) := by rw [add_assoc]
      _ = a * d.val + 0 := by rw [add_neg]
      _ = a * d.val := by rw [add_zero]
  rw [diff_eq]
  calc (a * d.val) * (a * d.val)
      = a * (d.val * (a * d.val)) := by rw [mul_assoc]
    _ = a * ((d.val * a) * d.val) := by rw [mul_assoc d.val]
    _ = a * ((a * d.val) * d.val) := by rw [mul_comm d.val a]
    _ = a * (a * (d.val * d.val)) := by rw [mul_assoc a]
    _ = a * (a * 0) := by rw [d_sq]
    _ = 0 := by rw [mul_zero, mul_zero]

end SIA
