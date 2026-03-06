# Smooth Infinitesimal Analysis in Lean 4 — Implementation Plan

## Overview

Formalize Smooth Infinitesimal Analysis (SIA) in Lean 4, proving the major theorems of
calculus using infinitesimals instead of limits — all without the Law of the Excluded
Middle (LEM). SIA is inherently intuitionistic: its core axiom (Kock-Lawvere) is
*inconsistent* with LEM, so constructive reasoning is not just a preference but a
mathematical necessity.

Primary reference: J.L. Bell, *A Primer of Infinitesimal Analysis* (2nd ed., Cambridge, 2008).

## Ensuring LEM is Excluded

This is a hard requirement, not a guideline. Our approach:

1. **No Mathlib dependency.** Mathlib uses `Classical` pervasively. We build all
   algebraic and order-theoretic infrastructure from scratch.

2. **No `Classical.choice`.** Lean 4's core has three extra-logical axioms:
   - `propext` (propositional extensionality) — constructively acceptable
   - `Quot.sound` (quotient soundness) — constructively acceptable
   - `Classical.choice` — this is what gives LEM; we never use it

3. **No classical tactics.** We avoid `by_contra` (uses `Classical.byContradiction`),
   `Decidable.em`, `open Classical`, etc.

4. **Automated verification.** `SIA/CheckAxioms.lean` contains a meta-program that
   inspects every declaration in our namespace at compile time and fails the build if
   any theorem depends on `Classical.choice`. This gives a machine-checked guarantee.

5. **Manual spot-checks.** Use `#print axioms <name>` during development to verify
   individual theorems.

## Architecture

```
SIA/
├── lakefile.lean           -- Lean 4 project config (no Mathlib)
├── lean-toolchain          -- pins Lean version
├── SIA.lean                -- root import file
├── SIA/
│   ├── Axioms.lean         -- The SIA class: ordered field + Kock-Lawvere
│   ├── Order.lean          -- Strict constructive order, <= from negation
│   ├── Field.lean          -- Constructive ordered field
│   ├── Delta.lean          -- Delta properties, LEM refutation, microcancellation
│   ├── Derivative.lean     -- f' definition via microaffinity, derivative rules
│   ├── Continuity.lean     -- All functions are continuous
│   ├── HigherOrder.lean    -- Delta_k, Taylor's theorem
│   ├── Integration.lean    -- Integration via antiderivatives
│   ├── FTC.lean            -- Fundamental Theorem of Calculus
│   └── CheckAxioms.lean    -- Compile-time LEM-freedom verifier
```

## Import DAG

```
CheckAxioms  (standalone meta-program)

FTC
 └── Integration
      └── Derivative
           ├── Delta
           │    └── Axioms
           │         ├── Field
           │         │    └── Order
           │         └── Order
           └── Continuity
                └── Delta
```

## Mathematical Content by Phase

### Phase 1: Foundation (Bell Ch. 1)

**Order.lean** — Strict constructive order
- `class StrictOrder`: irreflexive, transitive, cotransitive (`a < b → ∀ c, a < c ∨ c < b`)
- `≤` defined as `¬ (b < a)`
- Apartness: `a ≠ b → a < b ∨ b < a`
- Lemmas: `le_refl`, `le_trans`, `le_lt_trans`, `lt_ne`

**Field.lean** — Constructive ordered field
- `class ConstructiveOrderedField`: extends `CommRing`, `StrictOrder`
- Order-compatible addition and multiplication
- `0 < 1`
- Lemmas: `lt_neg_flip`, `le_add_left`, `le_mul_pos_left`, etc.

**Axioms.lean** — The SIA axiom system
- `Delta R := { d : R // d * d = 0 }` with `0 : Delta R`
- `class SIA`: extends `ConstructiveOrderedField`
  - `exists_unique_sqrt`: positive elements have unique square roots
  - `kock_lawvere`: ∀ f : Delta R → R, ∃! b, ∀ d, f d = f 0 + b * d.val

**Delta.lean** — Properties of nilsquare infinitesimals
- `neg_delta`: d ∈ Δ → -d ∈ Δ
- `mul_delta`: d ∈ Δ → ∀ a, d*a ∈ Δ
- `delta_near_zero`: ∀ d ∈ Δ, 0 ≤ d ∧ d ≤ 0
- `delta_nondegenerate`: Δ ≠ {0}
- `delta_indistinguishable_zero`: ∀ d ∈ Δ, ¬¬(d = 0)
- **`not_lem_on_delta`**: ¬ (∀ d ∈ Δ, d = 0 ∨ d ≠ 0) — LEM is refutable!
- `microcancellation`: (∀ d ∈ Δ, a*d = b*d) → a = b
- `microaffinity`: ∀ f : R → R, ∀ x, ∃! a, ∀ d ∈ Δ, f(x+d) = f(x) + a*d

**Continuity.lean** — All functions are continuous
- Neighbor relation: `neighbors a b ↔ (a-b)² = 0`
- `all_continuous`: ∀ f : R → R, ∀ x y, neighbors x y → neighbors (f x) (f y)
- Neighbor is symmetric but NOT transitive (Δ not microstable)

**CheckAxioms.lean** — Automated LEM-freedom check
- Meta-program that iterates all declarations in `SIA` namespace
- Asserts none depend on `Classical.choice`
- Runs at compile time; build fails if any classical axiom is detected

### Phase 2: Derivatives (Bell Ch. 2)

**Derivative.lean**
- `deriv f x`: extract the unique slope from microaffinity
- `deriv_const`: (fun _ => c)' = fun _ => 0
- `deriv_id`: id' = fun _ => 1
- `deriv_add`: (f + g)' = f' + g'
- `deriv_mul`: (f * g)' x = f'(x) * g(x) + f(x) * g'(x)
- `deriv_comp` (chain rule): (f ∘ g)' x = f'(g x) * g'(x)
- `deriv_neg`: (-f)' = -f'

### Phase 3: Higher Infinitesimals (Bell Ch. 3)

**HigherOrder.lean**
- `Delta_k R k := { d : R // d ^ (k+1) = 0 }`
- Generalized Kock-Lawvere for Δ_k (polynomial representation)
- Taylor's theorem: f(x+d) = Σ f^(n)(x) * d^n / n! for d ∈ Δ_k

### Phase 4: Integration & FTC (Bell Ch. 4-5)

**Integration.lean**
- Define integration via antiderivatives
- Additivity: ∫_a^b + ∫_b^c = ∫_a^c
- Linearity

**FTC.lean**
- FTC Part 1: if F' = f then ∫_a^b f = F(b) - F(a)
- FTC Part 2: (∫_a^x f)' = f(x)

## Design Decisions

### Apartness vs Negated Equality

We use `a ≠ b → a < b ∨ b < a` (following the existing Lean 3 code and Bell).
This makes `≠` and the order-apartness `a # b ≔ a < b ∨ b < a` equivalent,
which simplifies the development. A more refined approach would separate these,
but for SIA this is sufficient and matches the standard presentation.

### Field Inverses

Invertibility requires apartness from zero (`0 < a ∨ a < 0`), not mere `a ≠ 0`.
Since these are equivalent in our system (via `ne_lt`), we can use Lean's standard
`Field` notion with `a ≠ 0 → a has inverse`, knowing that our `ne_lt` axiom makes
this constructively acceptable.

### No Mathlib

We sacrifice tactics like `ring`, `linarith`, `field_simp` etc. for complete axiom
control. We prove basic algebraic lemmas (commutativity, associativity, distributivity
manipulations) by hand. The existing Lean 3 code demonstrates this is feasible.

### Derivative Extraction

Defining `deriv f x` requires extracting the witness from `∃! b, ...`. In constructive
logic, we use `ExistsUnique.choose` (or define our own) to extract the unique element.
This is constructively valid because uniqueness gives us a definite description.

## Relationship to Existing Lean 3 Code

The `src/` directory contains a working Lean 3 formalization covering most of Phase 1.
The mathematical structure (class hierarchy, proof strategies) is preserved in the
Lean 4 rewrite. The Lean 3 code serves as a reference but is not imported or compiled.

Key correspondences:
- `src/ordered_field.lean` → `SIA/Order.lean` + `SIA/Field.lean`
- `src/sia.lean` → `SIA/Axioms.lean`
- `src/basic.lean` → `SIA/Delta.lean`
- `src/exercises.lean` → `SIA/Continuity.lean` + `SIA/Delta.lean`
