/-
  SIA.Order — Strict constructive order

  Defines a strict order relation compatible with intuitionistic logic.
  No trichotomy (which would imply LEM), but we have:
  - Irreflexivity, transitivity
  - Cotransitivity (locatedness): a < b → ∀ c, a < c ∨ c < b
  - Apartness from inequality: a ≠ b → a < b ∨ b < a
  - ≤ defined as ¬ (b < a)

  Note: le_antisymm (a ≤ b → b ≤ a → a = b) is NOT provable constructively
  with ≤ defined as ¬(b < a), since it requires double-negation elimination.
  We can only prove ¬¬(a = b) from a ≤ b ∧ b ≤ a.
-/

universe u

class StrictOrder (R : Type u) extends LT R where
  lt_irrefl : ∀ (a : R), ¬ (a < a)
  lt_trans  : ∀ {a b c : R}, a < b → b < c → a < c
  ne_lt     : ∀ {a b : R}, a ≠ b → a < b ∨ b < a
  lt_cotrans : ∀ {a b : R}, a < b → ∀ (c : R), a < c ∨ c < b

namespace StrictOrder

variable {R : Type u} [StrictOrder R]

-- ≤ is the negation of the strict order in the other direction
instance : LE R where
  le a b := ¬ (b < a)

theorem lt_ne {a b : R} (h : a < b) : a ≠ b :=
  fun hab => lt_irrefl a (hab ▸ h)

theorem le_refl (a : R) : a ≤ a := lt_irrefl a

theorem le_of_lt {a b : R} (h : a < b) : a ≤ b :=
  fun hba => lt_irrefl a (lt_trans h hba)

theorem le_of_eq {a b : R} (h : a = b) : a ≤ b :=
  h ▸ le_refl a

-- Use cotransitivity: from b < c and point a, get b < a ∨ a < c
theorem le_lt_trans {a b c : R} (hab : a ≤ b) (hbc : b < c) : a < c :=
  (lt_cotrans hbc a).elim (fun h => (hab h).elim) id

-- Use cotransitivity: from a < b and point c, get a < c ∨ c < b
theorem lt_le_trans {a b c : R} (hab : a < b) (hbc : b ≤ c) : a < c :=
  (lt_cotrans hab c).elim id (fun h => (hbc h).elim)

theorem le_trans {a b c : R} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  fun hca => (lt_cotrans hca b).elim hbc hab

-- We can prove double-negated equality from ≤ in both directions
theorem le_le_eq_nn {a b : R} (hab : a ≤ b) (hba : b ≤ a) : ¬¬ (a = b) :=
  fun hne => (ne_lt hne).elim (fun h => hba h) (fun h => hab h)

end StrictOrder
