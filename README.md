# Smooth Infinitesimal Analysis in Lean 4

A formalization of Smooth Infinitesimal Analysis (SIA) in the Lean 4 theorem prover.
SIA develops calculus using nilpotent infinitesimals instead of limits, working entirely
within intuitionistic logic — the Law of the Excluded Middle is not just avoided, it is
*provably refutable* from the axioms.

Based on J.L. Bell, *A Primer of Infinitesimal Analysis* (2nd ed., Cambridge, 2008).

**Disclaimer**: All code in this project was written by Claude (Anthropic's AI assistant)
and has not yet been verified by a human. While the code compiles and Lean's type checker
accepts all proofs, this only guarantees logical validity relative to the stated axioms —
it does not guarantee that the theorem *statements* accurately capture the intended
mathematical claims.

## Documentation

The [`docs/`](docs/) directory contains a series of articles explaining every line of
code in this project. The articles are written for someone who knows traditional calculus
but not Lean or formal algebra — they cover both the math and the Lean syntax from the
ground up. Start with [Article 1: The Big Picture](docs/01-big-picture.md).

## What is SIA?

In SIA, the number line R contains *nilsquare infinitesimals*: elements d where d*d = 0
but d is not necessarily zero. The set of all such elements is called **Delta** (Δ).
The **Kock-Lawvere axiom** states that every function on Delta is affine:

> For every f : Delta -> R, there exists a unique b such that for all d in Delta,
> f(d) = f(0) + b * d.

This single axiom gives us derivatives without limits, makes every function infinitely
differentiable, and is fundamentally incompatible with classical logic.

## Key Results

- **LEM is refutable**: we prove `¬ (∀ d : Delta R, d = 0 ∨ d ≠ 0)`
- **Every function is continuous**: all f : R → R preserve the neighbor relation
- **Microaffinity**: every f : R → R has a unique derivative at every point
- **Derivative rules**: sum, product, chain rule — all from microcancellation
- **Higher-order infinitesimals**: Delta_k for nilpotent elements d^(k+1) = 0
- **Integration**: antiderivative axiom, linearity, additivity
- **Fundamental Theorem of Calculus**: both parts, plus integration by parts
- **No classical axioms used**: verified by an automated compile-time checker

## Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean version manager):

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
```

This project pins its Lean version via `lean-toolchain`, so elan will automatically
download the correct version.

## Building

```bash
lake build
```

This compiles all files and runs the axiom checker. If any theorem depends on
`Classical.choice`, the build will fail.

## Verifying LEM-freedom

The build automatically checks that no declaration uses classical axioms. You can
also manually inspect individual theorems:

```lean
#print axioms SIA.not_lem_on_delta
-- propext  (no Classical.choice!)
```

## Project Structure

```
SIA/
├── Order.lean          Strict constructive order
├── Field.lean          Constructive ordered field
├── Axioms.lean         SIA axioms (Kock-Lawvere)
├── Delta.lean          Nilsquare infinitesimal properties
├── Derivative.lean     Derivatives via microaffinity
├── Continuity.lean     All functions are continuous
├── HigherOrder.lean    Higher-order infinitesimals (Delta_k)
├── Integration.lean    Antiderivatives and integration
├── FTC.lean            Fundamental Theorem of Calculus
├── CheckAxioms.lean    Compile-time classical axiom detector
```

## How We Ensure No Classical Logic

SIA is *incompatible* with classical logic — the Kock-Lawvere axiom and the Law of the
Excluded Middle together lead to a contradiction. So avoiding classical reasoning is not
a stylistic choice but a mathematical necessity. Our approach:

1. **No Mathlib dependency.** Mathlib uses `Classical` pervasively. We build all
   algebraic and order-theoretic infrastructure from scratch.

2. **No `Classical.choice`.** Lean 4's core has three extra-logical axioms:
   - `propext` (propositional extensionality) — constructively acceptable
   - `Quot.sound` (quotient soundness) — constructively acceptable
   - `Classical.choice` — this gives LEM; we never use it

3. **No classical tactics.** We avoid `by_contra`, `Decidable.em`, `open Classical`,
   and anything else that introduces classical reasoning.

4. **Compile-time verification.** `SIA/CheckAxioms.lean` uses `#print axioms` on every
   key theorem. If any depends on `Classical.choice`, the build output shows it
   immediately. Only `propext` appears.

## Design Decisions

**Apartness vs negated equality.** We use `a ≠ b → a < b ∨ b < a`, making `≠` and
order-apartness equivalent. A more refined approach would separate these, but for SIA
this is sufficient and matches Bell's presentation.

**Field inverses.** Invertibility requires apartness from zero (`0 < a ∨ a < 0`), not
mere `a ≠ 0`. Since these are equivalent in our system (via `ne_lt`), we use Lean's
standard approach with `a ≠ 0 → a has inverse`.

**No Mathlib.** We sacrifice tactics like `ring`, `linarith`, and `field_simp` for
complete axiom control. Every algebraic lemma is proved by hand. This makes proofs
longer but guarantees no classical logic sneaks in through library dependencies.

**Conditional statements over witness extraction.** The Kock-Lawvere and integration
axioms assert existence via `ExistsUnique`. Extracting the witness as a Lean function
would require `Exists.choose`, which depends on `Classical.choice`. Instead, all
theorems are stated conditionally: "if F is an antiderivative of f, then..." The axioms
guarantee such witnesses exist (and are unique), so the theorems are not vacuously true.

## Future Work

The following extensions would build naturally on the current formalization:

- **Generalized Kock-Lawvere axiom.** Every function `f : Delta_k k → R` is a polynomial
  of degree ≤ k. The infrastructure (`Delta_k`, `npow`, `natCast`) is already in
  `HigherOrder.lean`; what remains is stating the axiom (requiring a polynomial evaluation
  function and factorial) and adding it as a class extending `SIAIntegral`.

- **Taylor's theorem.** For `d ∈ Delta_k k`: `f(x+d) = f(x) + f'(x)*d + f''(x)*d²/2! + ...`
  Follows from the generalized KL axiom applied to `g(d) = f(x+d)`. Requires iterated
  derivatives and factorial, both of which need to be built from scratch.

- **Inverse function theorem.** If f'(x) ≠ 0, then f is locally invertible and
  `(f⁻¹)'(f(x)) = 1/f'(x)`. Requires field division (already axiomatized) applied to
  derivatives.

- **L'Hopital's rule.** Follows from the microaffinity representation: if f(x) = g(x) = 0
  and g'(x) ≠ 0, then f(x+d)/g(x+d) = f'(x)/g'(x) for infinitesimal d, since the
  higher-order terms vanish.

- **Differential forms and the wedge product.** SIA provides a natural setting for
  differential forms via the exterior algebra on infinitesimals. The nilsquare condition
  `d² = 0` is precisely what makes `dx ∧ dx = 0` automatic.

- **Intermediate Value Theorem (constructive version).** In SIA, IVT takes a weaker form
  than in classical analysis — you cannot prove that a continuous function achieves every
  intermediate value, but you can prove approximate versions.

## Legacy Code

The `archive/` directory contains an earlier Lean 3 formalization that served as a
starting point for the mathematical development.
