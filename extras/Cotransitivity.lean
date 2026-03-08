/-
  Extras: Cotransitivity and derived theorems

  Cotransitivity (locatedness) is a standard constructive order axiom:
    a < b → ∀ c, a < c ∨ c < b

  It is mathematically interesting but not used by any of our SIA proofs.
  Bell does not list it among his order axioms (Chapter 8, axiom R₂).

  We keep it here as a separate extension of StrictOrder.
-/
import SIA.Order

universe u

class CotransOrder (R : Type u) extends StrictOrder R where
  lt_cotrans : ∀ {a b : R}, a < b → ∀ (c : R), a < c ∨ c < b

namespace CotransOrder

variable {R : Type u} [CotransOrder R]
open StrictOrder

-- Use cotransitivity: from b < c and point a, get b < a ∨ a < c
theorem le_lt_trans {a b c : R} (hab : a ≤ b) (hbc : b < c) : a < c :=
  (lt_cotrans hbc a).elim (fun h => (hab h).elim) id

-- Use cotransitivity: from a < b and point c, get a < c ∨ c < b
theorem lt_le_trans {a b c : R} (hab : a < b) (hbc : b ≤ c) : a < c :=
  (lt_cotrans hab c).elim id (fun h => (hbc h).elim)

theorem le_trans {a b c : R} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  fun hca => (lt_cotrans hca b).elim hbc hab

end CotransOrder
