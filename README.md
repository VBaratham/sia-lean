# Smooth Infinitesimal Analysis in Lean 4

A formalization of Smooth Infinitesimal Analysis (SIA) in the Lean 4 theorem prover.
SIA develops calculus using nilpotent infinitesimals instead of limits, working entirely
within intuitionistic logic — the Law of the Excluded Middle is not just avoided, it is
*provably refutable* from the axioms.

Based on J.L. Bell, *A Primer of Infinitesimal Analysis* (2nd ed., Cambridge, 2008).

## What is SIA?

In SIA, the number line R contains *nilsquare infinitesimals*: elements d where d*d = 0
but d is not necessarily zero. The **Kock-Lawvere axiom** states that every function
on these infinitesimals is affine:

> For every f : Delta -> R, there exists a unique b such that for all d in Delta,
> f(d) = f(0) + b * d.

This single axiom gives us derivatives without limits, makes every function infinitely
differentiable, and is fundamentally incompatible with classical logic.

## Key Results

- **LEM is refutable**: we prove `¬ (∀ d : Delta R, d = 0 ∨ d ≠ 0)`
- **Every function is continuous**: all f : R → R preserve the neighbor relation
- **Microaffinity**: every f : R → R has a unique derivative at every point
- **Derivative rules**: sum, product, chain rule — all from microcancellation
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
-- propext, Quot.sound  (no Classical.choice!)
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
├── CheckAxioms.lean    Compile-time classical axiom detector
```

See [PLAN.md](PLAN.md) for the full implementation plan and mathematical details.

## Legacy Code

The `src/` directory contains an earlier Lean 3 formalization that served as a
starting point for the mathematical development.
