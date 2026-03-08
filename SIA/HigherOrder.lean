/-
  SIA.HigherOrder — Higher-order infinitesimals

  Based on Bell, Chapter 7.

  Defines natural number exponentiation, natural number embedding into R,
  and Delta_k (k-th order nilpotent infinitesimals: elements d where d^(k+1) = 0).

  Delta_k generalizes Delta: Delta = Delta_k 1 (nilsquare = second power is zero).
  Delta_k 2 contains elements whose cube is zero, etc.

  The generalized Kock-Lawvere axiom (every function on Delta_k is a polynomial
  of degree ≤ k) and Taylor's theorem are planned for a future extension.
-/
import SIA.Delta

universe u

namespace SIA

open CommRing

-- ═══════════════════════════════════════════════════════
-- Natural number exponentiation
-- ═══════════════════════════════════════════════════════

def npow {R : Type u} [CommRing R] (a : R) : Nat → R
  | 0 => 1
  | n + 1 => a * npow a n

variable {R : Type u} [SIA R]
open CField StrictOrder ConstructiveOrderedField

@[simp] theorem npow_zero (a : R) : npow a 0 = 1 := rfl
@[simp] theorem npow_succ (a : R) (n : Nat) : npow a (n + 1) = a * npow a n := rfl

theorem npow_one (a : R) : npow a 1 = a := by
  show a * npow a 0 = a; rw [npow_zero, mul_one]

theorem npow_two (a : R) : npow a 2 = a * a := by
  show a * npow a 1 = a * a; rw [npow_one]

theorem zero_npow_succ (n : Nat) : npow (0 : R) (n + 1) = 0 := by
  show (0 : R) * npow 0 n = 0; rw [zero_mul]

theorem one_npow (n : Nat) : npow (1 : R) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => show (1 : R) * npow 1 n = 1; rw [ih, mul_one]

-- ═══════════════════════════════════════════════════════
-- Embedding natural numbers into R
-- ═══════════════════════════════════════════════════════

def natCast {R : Type u} [CommRing R] : Nat → R
  | 0 => 0
  | n + 1 => natCast n + 1

@[simp] theorem natCast_zero : (natCast 0 : R) = 0 := rfl
@[simp] theorem natCast_succ (n : Nat) : (natCast (n + 1) : R) = natCast n + 1 := rfl

theorem natCast_one : (natCast 1 : R) = 1 := by
  show (natCast 0 : R) + 1 = 1; rw [natCast_zero, zero_add]

theorem natCast_two : (natCast 2 : R) = 1 + 1 := by
  show (natCast 1 : R) + 1 = 1 + 1; rw [natCast_one]

-- ═══════════════════════════════════════════════════════
-- Delta_k: k-th order nilpotent infinitesimals
-- ═══════════════════════════════════════════════════════

-- d ∈ Delta_k k means d^(k+1) = 0
def Delta_k (R : Type u) [CommRing R] (k : Nat) := { d : R // npow d (k + 1) = 0 }

-- Zero is in Delta_k for all k
instance (k : Nat) : Zero (Delta_k R k) where
  zero := ⟨0, zero_npow_succ k⟩

@[simp]
theorem Delta_k.zero_val (k : Nat) : (0 : Delta_k R k).val = 0 := rfl

-- ═══════════════════════════════════════════════════════
-- Relationship between Delta and Delta_k
-- ═══════════════════════════════════════════════════════

-- Delta_k 1 corresponds to Delta (both mean d² = 0)
def toDelta (d : Delta_k R 1) : Delta R :=
  ⟨d.val, by rw [← npow_two]; exact d.property⟩

def fromDelta (d : Delta R) : Delta_k R 1 :=
  ⟨d.val, by rw [npow_two]; exact d.property⟩

@[simp] theorem toDelta_val (d : Delta_k R 1) : (toDelta d).val = d.val := rfl
@[simp] theorem fromDelta_val (d : Delta R) : (fromDelta d).val = d.val := rfl

-- Inclusion: Delta_k k ⊆ Delta_k (k+1)
-- If d^(k+1) = 0, then d^(k+2) = d * d^(k+1) = d * 0 = 0
def Delta_k.incl {k : Nat} (d : Delta_k R k) : Delta_k R (k + 1) :=
  ⟨d.val, by show d.val * npow d.val (k + 1) = 0; rw [d.property, mul_zero]⟩

-- Every Delta element is in Delta_k for all k ≥ 1
-- (stronger: Delta ⊆ Delta_k k for all k ≥ 1, since d² = 0 implies d^n = 0 for n ≥ 2)
theorem delta_in_delta_k (d : Delta R) (k : Nat) : npow d.val (k + 2) = 0 := by
  induction k with
  | zero =>
    show d.val * npow d.val 1 = 0
    rw [npow_one, d.property]
  | succ n ih =>
    show d.val * npow d.val (n + 2) = 0
    rw [ih, mul_zero]

def Delta.toDelta_k (d : Delta R) (k : Nat) : Delta_k R (k + 1) :=
  ⟨d.val, delta_in_delta_k d k⟩

end SIA
