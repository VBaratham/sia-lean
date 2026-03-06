/-
  SIA.Axioms — The Smooth Infinitesimal Analysis axiom system

  Defines Delta (nilsquare infinitesimals) and the SIA class, which adds
  the Kock-Lawvere axiom to a constructive ordered field.
-/
import SIA.Field

universe u

namespace SIA

-- Unique existence (not in Lean 4 core)
def ExistsUnique {α : Sort u} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x

theorem ExistsUnique.exists {α : Sort u} {p : α → Prop} (h : ExistsUnique p) : ∃ x, p x :=
  let ⟨x, hpx, _⟩ := h
  ⟨x, hpx⟩

theorem ExistsUnique.unique {α : Sort u} {p : α → Prop} (h : ExistsUnique p)
    {a b : α} (ha : p a) (hb : p b) : a = b :=
  let ⟨_, _, huniq⟩ := h
  (huniq a ha).trans (huniq b hb).symm

-- Delta: the set of nilsquare infinitesimals
def Delta (R : Type u) [Mul R] [Zero R] := { d : R // d * d = 0 }

-- Zero is always in Delta
def Delta.zero (R : Type u) [CommRing R] : Delta R :=
  ⟨0, CommRing.mul_zero 0⟩

instance {R : Type u} [CommRing R] : Zero (Delta R) where
  zero := Delta.zero R

@[simp]
theorem Delta.zero_val {R : Type u} [CommRing R] : (0 : Delta R).val = 0 := rfl

end SIA

-- The SIA class
class SIA (R : Type u) extends ConstructiveOrderedField R where
  kock_lawvere : ∀ (f : SIA.Delta R → R),
    SIA.ExistsUnique fun (b : R) => ∀ (d : SIA.Delta R), f d = f 0 + b * d.val
