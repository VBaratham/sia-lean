# Article 1c: Reading Lean Proofs — A Worked Exercise Set

Article 1b introduced the core idea: propositions are types, proofs are terms.
This article builds fluency through worked examples and exercises, starting
simple and building up. Each example uses real code from the project.

## Warm-up: reading theorem signatures

Before reading proofs, practice reading *statements*. Every theorem in Lean
has this shape:

    theorem name {implicit args} (explicit args) : conclusion := proof

The part before `:=` is the statement. The part after is the proof. Let's read
some statements without worrying about the proofs.

### Example 1: `sub_self`

```lean
theorem sub_self (a : R) : a - a = 0
```

- `sub_self` — the name (anything minus itself)
- `(a : R)` — for any element `a` of type `R`
- `: a - a = 0` — we're proving that `a - a = 0`

English: "For any a, a minus a equals zero."

### Example 2: `add_left_cancel`

```lean
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c
```

- `{a b c : R}` — for any a, b, c in R (curly braces = Lean infers these)
- `(h : a + b = a + c)` — given a proof `h` that a + b = a + c
- `: b = c` — we're proving b = c

English: "If a + b = a + c, then b = c." (You can cancel from the left.)

### Example 3: `le_of_lt`

```lean
theorem le_of_lt {a b : R} (h : a < b) : a ≤ b
```

English: "If a < b, then a ≤ b."

### Example 4: `lt_trans`

```lean
theorem lt_trans {a b c : R} : a < b → b < c → a < c
```

This one has no named arguments in parentheses — the hypotheses are part of the
conclusion type, written with arrows. This is equivalent to:

```lean
theorem lt_trans {a b c : R} (h1 : a < b) (h2 : b < c) : a < c
```

Both say: "Given a < b and b < c, conclude a < c." The arrow `→` is just
another way of writing a function that takes a proof as input.

### Curly braces vs parentheses

You'll notice `{a b : R}` uses curly braces and `(h : a < b)` uses
parentheses. The difference:

- **Curly braces `{...}`** — implicit arguments. Lean figures these out from
  context. When you *use* `lt_trans`, you don't write `lt_trans a b c h1 h2`,
  you just write `lt_trans h1 h2` and Lean infers `a`, `b`, `c` from the
  types of `h1` and `h2`.
- **Parentheses `(...)`** — explicit arguments. You must provide these
  yourself.

In a theorem signature, implicit arguments are typically the data (which
elements of R are we talking about?) and explicit arguments are the
hypotheses (what do we know about them?).

### Exercise 1

Read this signature and translate it to English:

```lean
theorem le_trans {a b c : R} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c
```

<details>
<summary>Answer</summary>

"If a ≤ b and b ≤ c, then a ≤ c." (Transitivity of ≤.)

The names `hab` and `hbc` are just the author's shorthand for "hypothesis
about a and b" and "hypothesis about b and c."
</details>

### Exercise 2

Read this signature:

```lean
theorem neg_unique {a b : R} (h : a + b = 0) : b = -a
```

<details>
<summary>Answer</summary>

"If a + b = 0, then b = -a." (The additive inverse is unique — if something
acts like the negation of a, it must *be* the negation of a.)
</details>

### Exercise 3

Read this signature:

```lean
theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b
```

<details>
<summary>Answer</summary>

"For any a and b, (-a) * (-b) = a * b." (A negative times a negative is
positive — or more precisely, the two negations cancel.)
</details>

---

## Reading tactic proofs

Most proofs in this project use **tactic mode**: you write `by` and then a
sequence of commands that build the proof step by step. Each tactic
transforms the current goal (what remains to prove).

### The key tactics

Here are the tactics you'll see most often:

| Tactic | What it does | Paper proof analogue |
|--------|-------------|---------------------|
| `rw [lemma]` | Rewrite the goal using an equation | "By [lemma], this equals..." |
| `intro h` | Assume something and name it `h` | "Suppose h." |
| `exact term` | Provide the final proof | "...which is what we wanted." |
| `have h : T := proof` | Prove an intermediate fact | "First, note that..." |
| `constructor` | Split an "and" goal into two parts | "We prove each part separately." |
| `calc` | Chain equalities step by step | "We compute: ... = ... = ..." |
| `show` | Restate the goal (for clarity) | "It suffices to show..." |
| `congr 1` | Reduce to showing subterms match | "The outer structure matches, so..." |

### Example 5: `sub_self`

```lean
theorem sub_self (a : R) : a - a = 0 := by
  rw [sub_eq, add_neg]
```

The proof has two steps:

1. `rw [sub_eq]` — The lemma `sub_eq` says `a - b = a + (-b)`. This rewrites
   the goal from `a - a = 0` to `a + (-a) = 0`.
2. `rw [add_neg]` — The lemma `add_neg` says `a + (-a) = 0`. This rewrites
   the goal from `a + (-a) = 0` to `0 = 0`, which is trivially true.

On paper: "By definition of subtraction, a - a = a + (-a). By the additive
inverse axiom, a + (-a) = 0."

### Example 6: `neg_add_cancel_left`

```lean
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add, zero_add]
```

Three rewrites:

1. `← add_assoc` — The `←` means rewrite *backwards*. `add_assoc` says
   `(x + y) + z = x + (y + z)`. Backwards, it rewrites
   `-a + (a + b)` to `(-a + a) + b`.
2. `neg_add` — rewrites `(-a) + a` to `0`, giving `0 + b`.
3. `zero_add` — rewrites `0 + b` to `b`. Goal closed.

### Exercise 4

Read this proof and explain each step:

```lean
theorem sub_add_cancel (a b : R) : a - b + b = a := by
  rw [sub_eq, add_assoc, neg_add, add_zero]
```

<details>
<summary>Answer</summary>

1. `sub_eq` — rewrites `a - b` to `a + (-b)`, giving goal `(a + (-b)) + b = a`
2. `add_assoc` — reassociates to `a + ((-b) + b) = a`
3. `neg_add` — rewrites `(-b) + b` to `0`, giving `a + 0 = a`
4. `add_zero` — rewrites `a + 0` to `a`, giving `a = a`. Done.

On paper: "a - b + b = a + (-b) + b = a + ((-b) + b) = a + 0 = a."
</details>

---

## Reading term-mode proofs

Some proofs are written without `by`, as a single expression. These are
**term-mode proofs**. They're more concise but can be harder to read because
you have to work inside-out.

### Example 7: `le_refl`

```lean
theorem le_refl (a : R) : a ≤ a := lt_irrefl a
```

Wait — where's the proof? It's just `lt_irrefl a`. Let's work through why
this type-checks.

Lean unfolds `a ≤ a` to `¬(a < a)` (by the definition of ≤), which is
`(a < a) → False`. And `lt_irrefl a` has exactly that type — it's the axiom
that says a < a is impossible. So `lt_irrefl a` is already a term of the type
we need. Done.

The key insight: the "proof" is just citing a fact that already has the right
type. Lean does the definitional unfolding silently.

### Example 8: `lt_ne`

```lean
theorem lt_ne {a b : R} (h : a < b) : a ≠ b :=
  fun hab => lt_irrefl a (hab ▸ h)
```

We want to prove: if `a < b`, then `a ≠ b`.

First, Lean unfolds `a ≠ b` to `(a = b) → False`. So we need a function
that takes a proof of `a = b` and produces `False`.

- `fun hab =>` — assume `a = b` (Lean infers the type of `hab` as `a = b`,
  since that's what the unfolded goal requires)
- `hab ▸ h` — the `▸` symbol means "substitute". `hab` is a proof that
  `a = b`. We use it to substitute `b` with `a` in `h : a < b`, getting a
  proof of `a < a`.
- `lt_irrefl a (...)` — a < a is impossible, so this produces `False`.

### Example 9: `le_of_lt` (revisited)

```lean
theorem le_of_lt {a b : R} (h : a < b) : a ≤ b :=
  fun hba => lt_irrefl a (lt_trans h hba)
```

Lean unfolds `a ≤ b` to `¬(b < a)` to `(b < a) → False`.

- `fun hba =>` — assume `b < a`
- `lt_trans h hba` — chain `h : a < b` and `hba : b < a` to get `a < a`
- `lt_irrefl a (...)` — `a < a` is impossible, producing `False`

### Exercise 5

Read this proof and explain it:

```lean
theorem two_ne_zero : (1 + 1 : R) ≠ 0 :=
  lt_ne zero_lt_two
```

Hint: `zero_lt_two` is a proof that `0 < 1 + 1`. And `lt_ne` is Example 8
above — it says `a < b → a ≠ b`.

<details>
<summary>Answer</summary>

`lt_ne zero_lt_two` applies the theorem "if a < b then a ≠ b" to the fact
that 0 < 1 + 1, giving 0 ≠ 1 + 1.

But wait — the conclusion is `(1 + 1) ≠ 0`, not `0 ≠ (1 + 1)`. In Lean, `≠`
is symmetric by definition: `a ≠ b` means `(a = b) → False`, and since
equality is symmetric, `(a = b) → False` and `(b = a) → False` are
interconvertible. Lean handles this automatically.

(Actually, `lt_ne` gives `0 ≠ 1 + 1` which is `(0 = 1 + 1) → False`. Lean
can treat this as `(1 + 1 = 0) → False` since if `1 + 1 = 0` then `0 = 1 + 1`
by symmetry. The details of how Lean resolves this are subtle, but the
mathematical content is clear: 1 + 1 can't be zero because 0 < 1 + 1.)
</details>

---

## Reading `calc` proofs

The `calc` tactic chains a sequence of equalities (or inequalities). Each
line transforms one side using a justification.

### Example 10: `neg_unique`

```lean
theorem neg_unique {a b : R} (h : a + b = 0) : b = -a := by
  calc b = 0 + b := by rw [zero_add]
    _ = ((-a) + a) + b := by rw [neg_add]
    _ = (-a) + (a + b) := by rw [add_assoc]
    _ = (-a) + 0 := by rw [h]
    _ = -a := by rw [add_zero]
```

Each `_` stands for "the previous expression." The chain reads:

    b = 0 + b             (because 0 + b = b)
      = ((-a) + a) + b    (because (-a) + a = 0, applied backwards)
      = (-a) + (a + b)    (by associativity)
      = (-a) + 0          (because a + b = 0, which is our hypothesis h)
      = -a                (because (-a) + 0 = -a)

On paper you might write this as a single chain:
"b = 0 + b = (-a + a) + b = -a + (a + b) = -a + 0 = -a."

The strategy: start with `b`, introduce `0` (as `-a + a`), reassociate to
isolate `a + b`, use the hypothesis to replace `a + b` with `0`, clean up.

### Exercise 6

Read this `calc` proof and explain the strategy:

```lean
theorem mul_eq_zero_of_ne_zero {c x : R} (hc : c ≠ 0) (h : c * x = 0) : x = 0 :=
  calc x = 1 * x := by rw [one_mul]
    _ = (c⁻¹ * c) * x := by rw [CField.inv_mul hc]
    _ = c⁻¹ * (c * x) := by rw [mul_assoc]
    _ = c⁻¹ * 0 := by rw [h]
    _ = 0 := by rw [mul_zero]
```

<details>
<summary>Answer</summary>

Statement: if c ≠ 0 and c * x = 0, then x = 0. (You can cancel a nonzero
factor.)

The chain:

    x = 1 * x              (1 is the multiplicative identity)
      = (c⁻¹ * c) * x      (because c⁻¹ * c = 1, using the fact that c ≠ 0)
      = c⁻¹ * (c * x)      (by associativity)
      = c⁻¹ * 0            (because c * x = 0, which is our hypothesis h)
      = 0                  (anything times 0 is 0)

Strategy: multiply both sides by c⁻¹. This is the standard "divide by c"
argument, written out in excruciating algebraic detail because we don't have
a `ring` tactic.
</details>

---

## Reading proofs with `intro` and `have`

More complex proofs introduce hypotheses (`intro`) and prove intermediate
facts (`have`).

### Example 11: `add_right_cancel`

```lean
theorem add_right_cancel {a b c : R} (h : a + c = b + c) : a = b := by
  have : (a + c) + -c = (b + c) + -c := by rw [h]
  rw [add_assoc, add_neg, add_zero, add_assoc, add_neg, add_zero] at this
  exact this
```

Statement: if a + c = b + c, then a = b. (You can cancel from the right.)

- `have : (a + c) + -c = (b + c) + -c := by rw [h]` — "First, note that..."
  We add `-c` to both sides of the hypothesis `h`. The `have` tactic proves
  an intermediate fact. (When no name is given after `have`, Lean names it
  `this`.)
- `rw [...] at this` — the `at this` means we rewrite the intermediate fact,
  not the goal. The six rewrites simplify both sides:
  `(a + c) + -c = a + (c + -c) = a + 0 = a`, and similarly for the right side.
  After rewriting, `this` becomes `a = b`.
- `exact this` — the intermediate fact `this` is now exactly our goal. Done.

On paper: "Add -c to both sides: (a + c) + (-c) = (b + c) + (-c).
Simplify both sides: a = b."

The proof does in six rewrite steps what you'd do in one line on paper. This
is the cost of working without a `ring` tactic — every algebraic simplification
must be justified by name.

---

## Cheat sheet: reading Lean at a glance

When you encounter a Lean proof you don't understand, here's a process:

1. **Read the signature first.** Ignore the proof. Just read the part before
   `:=` and translate it to English.

2. **Unfold definitions.** If the conclusion uses `≤`, `≠`, or `¬`, remember:
   - `a ≤ b` means `¬(b < a)` means `(b < a) → False`
   - `a ≠ b` means `(a = b) → False`
   - `¬P` means `P → False`

3. **For tactic proofs (`by ...`)**: read each tactic as a step in a paper
   proof. `rw` is "rewrite using," `intro` is "suppose," `exact` is "done."

4. **For term proofs**: read inside-out. The outermost function is the last
   step; the innermost expressions are the first steps.

5. **Ignore names.** `h`, `hba`, `hab`, `hF` are just variable names chosen
   by the author. What matters is their *type*, which Lean infers.

6. **Follow the types.** Every expression has a type. A proof works because
   the types line up — each function receives arguments of the right type and
   produces output of the right type. When in doubt, ask: "What type does
   this expression have?"
