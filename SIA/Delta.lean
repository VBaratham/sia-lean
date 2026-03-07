/-
  SIA.Delta — Properties of nilsquare infinitesimals

  Core results about Delta including:
  - Closure under negation and scaling
  - Infinitesimals are "near zero" (0 ≤ d and d ≤ 0)
  - Delta is non-degenerate (not all zero)
  - LEM is refutable on Delta
  - Microcancellation
  - Microaffinity (every function R → R has a unique derivative)
-/
import SIA.Axioms

universe u

namespace SIA

variable {R : Type u} [SIA R]
open CommRing CField StrictOrder ConstructiveOrderedField

-- Negation preserves Delta membership
theorem neg_delta (d : Delta R) : (-d.val) * (-d.val) = 0 := by
  rw [neg_mul_neg]; exact d.property

instance : Neg (Delta R) where
  neg d := ⟨-d.val, neg_delta d⟩

@[simp]
theorem neg_delta_val (d : Delta R) : (-d).val = -d.val := rfl

-- Scaling preserves Delta membership
theorem mul_delta_sq (d : Delta R) (a : R) : (d.val * a) * (d.val * a) = 0 := by
  have h := d.property
  -- (d*a)*(d*a) = d*(a*(d*a)) = d*((a*d)*a) = d*((d*a)*a) = (d*(d*a))*a = ((d*d)*a)*a
  calc (d.val * a) * (d.val * a)
      = d.val * (a * (d.val * a)) := by rw [mul_assoc]
    _ = d.val * ((a * d.val) * a) := by rw [mul_assoc a]
    _ = d.val * ((d.val * a) * a) := by rw [mul_comm a d.val]
    _ = d.val * (d.val * (a * a)) := by rw [mul_assoc d.val]
    _ = (d.val * d.val) * (a * a) := by rw [mul_assoc]
    _ = 0 * (a * a) := by rw [h]
    _ = 0 := by rw [zero_mul]

-- Delta elements are "between" 0 and 0
theorem delta_near_zero (d : Delta R) : (0 : R) ≤ d.val ∧ d.val ≤ 0 := by
  constructor
  · -- 0 ≤ d.val, i.e., ¬ (d.val < 0)
    intro h_neg
    have h_pos_neg : (0 : R) < -d.val := neg_pos h_neg
    have h1 : (-d.val) * 0 < (-d.val) * (-d.val) :=
      lt_mul_pos_left h_pos_neg h_pos_neg
    rw [mul_zero, neg_mul_neg] at h1
    rw [d.property] at h1
    exact StrictOrder.lt_irrefl 0 h1
  · -- d.val ≤ 0, i.e., ¬ (0 < d.val)
    intro h_pos
    have h1 : d.val * 0 < d.val * d.val :=
      lt_mul_pos_left h_pos h_pos
    rw [mul_zero, d.property] at h1
    exact StrictOrder.lt_irrefl 0 h1

-- Microaffinity: every function R → R is microaffine
theorem microaffinity (f : R → R) (x : R) :
    ExistsUnique fun (a : R) => ∀ (d : Delta R), f (x + d.val) = f x + a * d.val := by
  let g : Delta R → R := fun d => f (x + d.val)
  have hg : g 0 = f x := by simp [g, add_zero]
  obtain ⟨b, hb, huniq⟩ := SIA.kock_lawvere g
  exact ⟨b,
    fun d => by
      have := hb d
      rw [hg] at this
      exact this,
    fun y hy => huniq y (fun d => by
      have := hy d
      rw [hg]
      exact this)⟩

-- Delta is non-degenerate: not all elements are equal
theorem delta_nondegenerate : ¬ (∀ (x y : Delta R), x.val = y.val) := by
  intro deg
  have d_eq_zero : ∀ (d : Delta R), (0 : R) = d.val := fun d => deg 0 d
  let f : R → R := id
  have micro := microaffinity f 0
  have pf_zero : ∀ (d : Delta R), f (0 + d.val) = f 0 + 0 * d.val := by
    intro d; simp [f, zero_add, zero_mul, add_zero]
    exact (d_eq_zero d).symm
  have pf_one : ∀ (d : Delta R), f (0 + d.val) = f 0 + 1 * d.val := by
    intro d; simp [f, zero_add, one_mul]
  have h01 : (0 : R) = 1 := micro.unique pf_zero pf_one
  exact absurd h01 (StrictOrder.lt_ne zero_lt_one)

-- Delta elements are indistinguishable from zero (double negation)
theorem delta_indistinguishable_zero (d : Delta R) : ¬¬ (d.val = 0) := by
  intro h
  have ⟨h_ge, h_le⟩ := delta_near_zero d
  exact (StrictOrder.ne_lt h).elim (fun h_lt => h_ge h_lt) (fun h_gt => h_le h_gt)

-- LEM is refutable on Delta: it is NOT the case that every d is decidably zero
theorem not_lem_on_delta : ¬ (∀ (d : Delta R), d.val = 0 ∨ d.val ≠ 0) := by
  intro lem
  have all_zero : ∀ (d : Delta R), d.val = 0 := by
    intro d
    exact (lem d).elim id (fun h => absurd h (delta_indistinguishable_zero d))
  have all_eq : ∀ (x y : Delta R), x.val = y.val := by
    intro x y; rw [all_zero x, all_zero y]
  exact delta_nondegenerate all_eq

-- Microcancellation: if a*d = b*d for all d in Delta, then a = b
theorem microcancellation {a b : R} (h : ∀ (d : Delta R), a * d.val = b * d.val) : a = b := by
  let f : Delta R → R := fun d => a * d.val
  have kl := SIA.kock_lawvere f
  have pf_a : ∀ (d : Delta R), f d = f 0 + a * d.val := by
    intro d; simp [f, mul_zero, zero_add]
  have pf_b : ∀ (d : Delta R), f d = f 0 + b * d.val := by
    intro d; simp [f, mul_zero, zero_add]; exact h d
  exact kl.unique pf_a pf_b

-- Delta is NOT microstable: Delta + Delta is not contained in Delta
def Microstable (A : R → Prop) : Prop :=
  ∀ (a : { x : R // A x }), ∀ (d : Delta R), A (a.val + d.val)

-- Product of two Delta elements is not necessarily zero
theorem microproduct_not_zero : ¬ (∀ (e n : Delta R), e.val * n.val = 0) := by
  intro h
  have : ∀ (d e : Delta R), d.val = e.val := by
    intro d e
    apply microcancellation
    intro n
    rw [h d n, h e n]
  exact delta_nondegenerate this

-- Helper: if c ≠ 0 and c * x = 0, then x = 0
theorem mul_eq_zero_of_ne_zero {c x : R} (hc : c ≠ 0) (h : c * x = 0) : x = 0 :=
  calc x = 1 * x := by rw [one_mul]
    _ = (c⁻¹ * c) * x := by rw [CField.inv_mul hc]
    _ = c⁻¹ * (c * x) := by rw [mul_assoc]
    _ = c⁻¹ * 0 := by rw [h]
    _ = 0 := by rw [mul_zero]

theorem delta_not_microstable : ¬ Microstable (fun (r : R) => r * r = 0) := by
  intro h_micro
  have : ∀ (a b : Delta R), a.val * b.val = 0 := by
    intro a b
    have a_sq := a.property  -- a² = 0
    have b_sq := b.property  -- b² = 0
    have sum_sq : (a.val + b.val) * (a.val + b.val) = 0 := h_micro a b
    -- Expand (a+b)² directly
    have expand : a.val * a.val + a.val * b.val + (b.val * a.val + b.val * b.val) =
        (a.val + b.val) * (a.val + b.val) := by
      -- (a+b)*(a+b) = a*(a+b) + b*(a+b) = aa + ab + ba + bb
      calc a.val * a.val + a.val * b.val + (b.val * a.val + b.val * b.val)
          = a.val * a.val + (a.val * b.val + (b.val * a.val + b.val * b.val)) := by
            rw [add_assoc]
        _ = (a.val * a.val + a.val * b.val) + (b.val * a.val + b.val * b.val) := by
            rw [← add_assoc]
        _ = a.val * (a.val + b.val) + (b.val * a.val + b.val * b.val) := by
            rw [← left_distrib]
        _ = a.val * (a.val + b.val) + b.val * (a.val + b.val) := by
            rw [← left_distrib]
        _ = (a.val + b.val) * (a.val + b.val) := by
            rw [← right_distrib]
    -- Substitute a²=0, b²=0, (a+b)²=0
    rw [sum_sq, a_sq, zero_add, b_sq, add_zero, mul_comm b.val a.val] at expand
    -- expand : ab + ab = 0
    -- ab + ab = (1+1) * ab
    have h2 : (1 + 1) * (a.val * b.val) = 0 := by
      rw [right_distrib, one_mul]; exact expand
    exact mul_eq_zero_of_ne_zero two_ne_zero h2
  exact microproduct_not_zero this

end SIA
