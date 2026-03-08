# Appendix: Lean Proof Patterns Reference

A quick-reference for Lean patterns used in this project. Articles 1b and 1c
cover the conceptual foundations (Curry-Howard, propositions-as-types); this
appendix is a lookup table for specific patterns as they arise in proofs.

---

## `.elim` — case analysis and contradiction elimination

The `.elim` method appears on several types with different meanings:

### `Or.elim` — case analysis on a disjunction

If you have `h : P ∨ Q` and you want to prove `R`, you write:

```lean
h.elim (fun hp => ...) (fun hq => ...)
```

The first function handles the case where `P` holds; the second handles `Q`.
Both must return something of type `R`.

Example from `le_le_eq_nn`:

```lean
(ne_lt hne).elim (fun h => hba h) (fun h => hab h)
```

Here `ne_lt hne : a < b ∨ b < a`. The `.elim` splits into two cases. In each
case, the hypothesis contradicts one of `hab` or `hba`, producing `False`.

### `False.elim` — anything from a contradiction

If you have `h : False`, then `h.elim` produces a value of any type. This is
*ex falso quodlibet*: from a contradiction, anything follows.

You'll see this in expressions like `(hab h).elim` where `hab : ¬ X` and
`h : X`, so `hab h : False`, and `.elim` converts it to whatever type is
needed.

Note: when the goal type is already `False` (e.g., inside a proof of `¬ P`),
you don't need `.elim` — you can just produce the `False` value directly.
That's why `le_le_eq_nn` doesn't use `False.elim`: both branches of the
`Or.elim` return `False`, which is already the goal type.
