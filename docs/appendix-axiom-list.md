# Appendix: Complete Axiom List

This is every axiom in the project — the full set of assumptions from which
all theorems are derived. There are 20 axioms in the main codebase (plus 1
Lean built-in and 1 optional extra), organized across 6 classes.

---

## Lean built-in

**`propext`** — propositional extensionality: if two propositions are logically
equivalent (`P ↔ Q`), then they are equal (`P = Q`). This is built into Lean 4
and is the only Lean-level axiom our proofs use. Notably, we never use
`Classical.choice` (which would give us LEM). The file `CheckAxioms.lean`
verifies this for every theorem in the project.

---

## CommRing — commutative ring (Algebra.lean)

Seven axioms, plus two definitions:

| # | Name | Statement |
|---|------|-----------|
| 1 | `add_assoc` | `(a + b) + c = a + (b + c)` |
| 2 | `add_comm` | `a + b = b + a` |
| 3 | `add_zero` | `a + 0 = a` |
| 4 | `add_neg` | `a + (-a) = 0` |
| 5 | `mul_assoc` | `(a * b) * c = a * (b * c)` |
| 6 | `mul_comm` | `a * b = b * a` |
| 7 | `mul_one` | `a * 1 = a` |
| 8 | `left_distrib` | `a * (b + c) = a * b + a * c` |
| | `sub_eq_add_neg` | `a - b = a + (-b)` *(definition of subtraction)* |

These are the standard axioms for a commutative ring. The other-sided versions
(`zero_add`, `neg_add`, `one_mul`, `right_distrib`) and properties like
`mul_zero` are derived as theorems.

## CField — field (Algebra.lean)

One axiom, plus two definitions/conventions:

| # | Name | Statement |
|---|------|-----------|
| 9 | `mul_inv` | `a ≠ 0 → a * a⁻¹ = 1` |
| | `div_eq_mul_inv` | `a / b = a * b⁻¹` *(definition of division)* |
| | `inv_zero` | `(0 : R)⁻¹ = 0` *(convention — see note)* |

**Note on `inv_zero`:** Bell's inverse axiom only applies when `x ≠ 0` and says
nothing about `0⁻¹`. Since Lean requires `⁻¹` to be a total function (it must
return *something* for every input), we set `0⁻¹ = 0` by convention. No theorem
uses this value at a point where the inverse is mathematically meaningful.

**Note on nontriviality:** A standard field definition also requires `0 ≠ 1`.
We omit this from `CField` because `ConstructiveOrderedField` provides
`zero_lt_one`, from which `0 ≠ 1` follows. This means `CField` alone
technically allows the degenerate case `0 = 1`.

## StrictOrder — constructive ordering (Order.lean)

Three axioms:

| # | Name | Statement |
|---|------|-----------|
| 10 | `lt_irrefl` | `¬(a < a)` |
| 11 | `lt_trans` | `a < b → b < c → a < c` |
| 12 | `ne_lt` | `a ≠ b → a < b ∨ b < a` |

The definition `a ≤ b := ¬(b < a)` is an instance declaration, not a class
axiom.

## ConstructiveOrderedField — ordered field (Field.lean)

Three axioms connecting order with arithmetic:

| # | Name | Statement |
|---|------|-----------|
| 13 | `zero_lt_one` | `0 < 1` |
| 14 | `lt_add_left` | `a < b → c + a < c + b` |
| 15 | `lt_mul_pos_left` | `0 < c → a < b → c * a < c * b` |

## SIA — Kock-Lawvere axiom (Axioms.lean)

One axiom:

| # | Name | Statement |
|---|------|-----------|
| 16 | `kock_lawvere` | Every function `f : Δ → R` satisfies `f(d) = f(0) + b·d` for a unique `b` |

This is Bell's SIA₁ (the principle of microaffineness). Delta is defined as
`{d : R // d * d = 0}` — the nilsquare infinitesimals.

## SIAIntegral — integration axiom (Integration.lean)

One axiom:

| # | Name | Statement |
|---|------|-----------|
| 17 | `integration` | Every function `f : R → R` has a unique antiderivative `F` with `F(0) = 0` |

This replaces Bell's SIA₂ (the constancy principle). The two are
interderivable — see the [comparison with Bell](appendix-comparison-with-bell.md).

---

## Summary

| Category | Count | Notes |
|----------|-------|-------|
| Genuine mathematical axioms | 17 | Everything above numbered 1–17 |
| Definitions | 2 | `sub_eq_add_neg`, `div_eq_mul_inv` |
| Conventions | 1 | `inv_zero` |
| Lean built-in | 1 | `propext` |
| **Total** | **21** | |

---

## Optional extra (not used by any proof)

The file `extras/Cotransitivity.lean` defines `CotransOrder` extending
`StrictOrder` with one additional axiom:

| Name | Statement |
|------|-----------|
| `lt_cotrans` | `a < b → ∀ c, a < c ∨ c < b` |

This is not used by any SIA proof and Bell does not list it among his axioms.
See the [cotransitivity appendix](appendix-cotransitivity.md).
