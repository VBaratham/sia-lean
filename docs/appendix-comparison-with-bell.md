# Appendix: Comparison with Bell's Axiom System

This appendix catalogs the differences between our Lean formalization and the
axiom system in Bell's *A Primer of Infinitesimal Analysis* (2nd edition,
Chapter 8). Some are deliberate design choices, some are consequences of
working in Lean's type theory, and some are omissions of material we haven't
formalized.

---

## Field axioms (Bell's R₁)

Bell's R₁ says R is a nontrivial field: the usual commutative ring axioms, plus
`¬(0 = 1)` and `¬(x = 0) → ∃y(x·y = 1)`.

**Our formalization** splits this across `CommRing` (Algebra.lean) and `CField`
(Algebra.lean).

### Differences

**Inverse as a total function.** Bell writes `¬(x = 0) → ∃y(x·y = 1)` — an
existential statement that an inverse *exists*. We instead provide a total
function `inv : R → R` with the axiom `a ≠ 0 → a * a⁻¹ = 1`, plus the
convention `inv_zero : (0 : R)⁻¹ = 0`.

This is actually *more* constructive than Bell's formulation, not less. In
Lean's type theory, `∃ y, x * y = 1` lives in `Prop`, which is
proof-irrelevant — you cannot extract the witness `y` without `Classical.choice`.
A total inverse function avoids this problem entirely: the inverse is
computable data, not a propositional assertion.

The choice of `0⁻¹ = 0` is arbitrary but harmless — no theorem ever uses it
at a value where the inverse is mathematically meaningful. Bell simply doesn't
address what happens at 0, since his axiom only fires when `x ≠ 0`.

**Nontriviality.** Bell includes `¬(0 = 1)` as an explicit field axiom. We omit
it from `CField` because our `ConstructiveOrderedField` provides `zero_lt_one`,
from which `0 ≠ 1` follows by irreflexivity of `<`. A comment in the code notes
this.

**Subtraction and division.** Bell doesn't mention subtraction or division —
they are just notation for `x + (-y)` and `x · y⁻¹`. We include
`sub_eq_add_neg` and `div_eq_mul_inv` as definitional axioms in our classes,
which is standard practice in Lean formalizations (it tells the system how to
unfold the `Sub` and `Div` typeclasses).

### Non-differences

Our ring axioms are essentially identical to Bell's. We axiomatize one-sided
versions (`add_zero`, `mul_one`) and derive the other sides via commutativity,
which is equivalent to Bell listing the one-sided versions `0 + x = x` and
`1·x = x`. We also derive `mul_zero` (which Bell doesn't list) as a theorem
from the ring axioms, not an axiom.

---

## Order axioms (Bell's R₂)

Bell's R₂ gives R a strict order `<` with the following axioms:

1. Irreflexivity and transitivity
2. `x < y ∧ y < z → x < z` (transitivity, same as ours)
3. `¬(x = y) → x < y ∨ y < x` (apartness)
4. `0 < x → ∃y(x = y²)` (positive elements have square roots)
5. `∀x(0 < x ∨ x < 1)` (every element is either positive or less than 1)

**Our formalization** has only the first three (irreflexivity, transitivity,
apartness) in `StrictOrder` (Order.lean), plus three ordered-field compatibility
axioms in `ConstructiveOrderedField` (Field.lean).

### What we omit

**Square roots of positives** (`0 < x → ∃y(x = y²)`). We don't have this. None
of our proofs use it. Bell uses it in some later chapters (e.g., to show that
positive elements are invertible), but the results we formalize don't depend
on it.

**Locatedness** (`∀x(0 < x ∨ x < 1)`). We don't have this either. This axiom
says every element of R can be compared to at least one of two benchmarks. It
is a weakened form of decidability — not as strong as trichotomy, but still
gives you *some* comparison for every element. None of our proofs need it.

**Cotransitivity** (`a < b → ∀c, a < c ∨ c < b`). Bell does not list this as an
axiom, and we don't include it in `StrictOrder`. It lives in
`extras/Cotransitivity.lean` as an optional extension. See the
[cotransitivity appendix](appendix-cotransitivity.md).

### What we add

**Ordered field axioms.** Our `ConstructiveOrderedField` includes three axioms
connecting order with arithmetic:

- `zero_lt_one : 0 < 1`
- `lt_add_left : a < b → ∀ c, c + a < c + b`
- `lt_mul_pos_left : 0 < c → a < b → c * a < c * b`

Bell's R₂ does not list these explicitly, but they are standard properties of
ordered fields that Bell uses implicitly throughout. We make them explicit
axioms.

---

## SIA axioms (Bell's SIA₁ and SIA₂)

Bell states two axioms:

- **SIA₁** (Microaffineness): Every function `f : Δ → R` satisfies
  `f(ε) = f(0) + b·ε` for a unique `b`.

- **SIA₂** (Constancy principle): If `f : R → R` satisfies
  `f(x + ε) = f(x)` for all x and all ε in Δ, then f is constant.

### What we have

**Kock-Lawvere (= SIA₁).** Our `SIA` class (Axioms.lean) includes exactly
Bell's microaffineness axiom:

```lean
kock_lawvere : ∀ (f : Delta R → R),
  ExistsUnique fun (b : R) => ∀ (d : Delta R), f d = f 0 + b * d.val
```

This matches Bell's SIA₁. We use our custom `ExistsUnique` (which is
`∃ x, p x ∧ ∀ y, p y → y = x`) rather than Lean's built-in `∃!`, to ensure
we can extract uniqueness proofs without `Classical.choice`.

**Integration axiom.** Our `SIAIntegral` class (Integration.lean) adds: every
function `f : R → R` has a unique antiderivative F with F(0) = 0. This
corresponds to the integration axiom Bell introduces in Chapter 6, and is a
separate axiom class because it is only needed for integration and the FTC.

### What we omit

**Constancy principle (SIA₂).** We do not axiomatize Bell's SIA₂. The
constancy principle says: if `f(x + ε) = f(x)` for all x and all infinitesimals
ε, then f is constant (`f(x) = f(y)` for all x, y).

This is a powerful axiom — it bridges the local (infinitesimal neighborhoods)
and the global (all of R). Bell uses it primarily for integration theory. Our
formalization replaces it with the integration axiom, which directly provides
antiderivatives. The two approaches yield the same theorems (FTC, integration
by parts, etc.), but the integration axiom is more directly usable in Lean
because it provides a function rather than asserting a universal property.

The constancy principle can be derived from the integration axiom (a function
with zero slope everywhere is constant — this is our `zero_slope_is_const`
theorem), so we lose no generality.

---

## Summary table

| Bell axiom | Our formalization | Status |
|-----------|-------------------|--------|
| R₁: field axioms | `CommRing` + `CField` | Equivalent (inverse is a function, not existential) |
| R₁: `¬(0 = 1)` | Derived from `zero_lt_one` | Derived, not axiomatized |
| R₂: irreflexivity, transitivity | `StrictOrder` | Same |
| R₂: apartness | `StrictOrder.ne_lt` | Same |
| R₂: square roots of positives | — | Omitted (unused) |
| R₂: `∀x(0 < x ∨ x < 1)` | — | Omitted (unused) |
| R₂: cotransitivity | `extras/Cotransitivity.lean` | Optional extra (Bell omits it too) |
| (not in Bell) | `zero_lt_one`, `lt_add_left`, `lt_mul_pos_left` | Added (implicit in Bell) |
| SIA₁: microaffineness | `SIA.kock_lawvere` | Same |
| SIA₂: constancy principle | Derived as `zero_slope_is_const` | Derived from integration axiom |
| Ch. 6: integration | `SIAIntegral.integration` | Axiomatized (Bell derives from SIA₂) |
