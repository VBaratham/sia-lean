# Article 1c: Reading Lean Proofs — A Worked Exercise Set

Article 1b introduced the core idea: propositions are types, proofs are terms.
This article builds fluency through worked examples and exercises, starting
simple and building up. Each example uses real code from the project.

## Definitions you need to know

Several symbols in our code are defined in terms of simpler concepts. Lean
silently unfolds these definitions when type-checking proofs:

| Expression | Definition | English |
|-----------|------------|---------|
| `¬P` | `P → False` | "P leads to a contradiction" |
| `a ≠ b` | `(a = b) → False` | "a = b leads to a contradiction" |
| `a ≤ b` | `¬(b < a)` | "b < a is impossible" |
| `a - b` | `a + (-b)` | "a plus the negation of b" |

These compose. For instance, `a ≤ b` unfolds to `¬(b < a)`, which unfolds to
`(b < a) → False`. When you see a proof that starts with `fun h =>`, ask:
"what type must `h` have?" The answer comes from unfolding the goal.

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
| `simp [lemmas]` | Apply simplification rules automatically | "This simplifies to..." |

### Example 5: `sub_self`

```lean
theorem sub_self (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg]
```

The proof has two steps:

1. `rw [sub_eq_add_neg]` — The lemma `sub_eq_add_neg` says `a - b = a + (-b)`. This rewrites
   the goal from `a - a = 0` to `a + (-a) = 0`.
2. `rw [add_neg]` — The lemma `add_neg` says `a + (-a) = 0`. This rewrites
   the goal from `a + (-a) = 0` to `0 = 0`, which is trivially true.

On paper: "By definition of subtraction, a - a = a + (-a). By the additive
inverse axiom, a + (-a) = 0."

### Which occurrence does `rw` rewrite?

`rw [lemma]` rewrites the **first** matching occurrence in the goal, scanning
left to right. If the goal has multiple matches, only the first one changes.

For example, if the goal were `(a - b) + (c - d) = ...`, then `rw [sub_eq_add_neg]`
would rewrite only `a - b` to `a + (-b)`, leaving `c - d` untouched. To
rewrite both, you'd chain two rewrites: `rw [sub_eq_add_neg, sub_eq_add_neg]`.

You can also be explicit about *which* occurrence to rewrite by providing
arguments to the lemma. `sub_eq_add_neg` says `∀ (a b : R), a - b = a + (-b)`. If
you write `rw [sub_eq_add_neg c d]`, Lean will specifically rewrite `c - d` and leave
other subtractions alone. For example, if the goal is:

    (a - b) + (c - d) = ...

then `rw [sub_eq_add_neg c d]` rewrites only the second subtraction, giving
`(a - b) + (c + (-d)) = ...`.

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
  rw [sub_eq_add_neg, add_assoc, neg_add, add_zero]
```

<details>
<summary>Answer</summary>

1. `sub_eq_add_neg` — rewrites `a - b` to `a + (-b)`, giving goal `(a + (-b)) + b = a`
2. `add_assoc` — reassociates to `a + ((-b) + b) = a`
3. `neg_add` — rewrites `(-b) + b` to `0`, giving `a + 0 = a`
4. `add_zero` — rewrites `a + 0` to `a`, giving `a = a`. Done.

On paper: "a - b + b = a + (-b) + b = a + ((-b) + b) = a + 0 = a."
</details>

### Example 7: `zero_lt_two` — using `have` and `exact`

Not every tactic proof is a chain of rewrites. Often you need to establish
intermediate facts (`have`) and then combine them.

```lean
theorem zero_lt_two : (0 : R) < 1 + 1 := by
  have h1 : (0 : R) < 1 := zero_lt_one
  have h2 : 1 + (0 : R) < 1 + 1 := lt_add_left h1 1
  rw [add_zero] at h2
  exact lt_trans h1 h2
```

A note on syntax: `(0 : R)` means "the zero of type R." Lean has many types
that each have their own zero (natural numbers, integers, etc.), so the `: R`
tells Lean which one we mean. You'll see this annotation whenever Lean can't
figure out the type on its own.

We want to prove 0 < 1 + 1 (i.e., 0 < 2). There's no single lemma that
gives this directly, so we build it in steps:

1. `have h1 : (0 : R) < 1 := lt_zero_one` — "First, note that 0 < 1."
   The `have` tactic proves an intermediate fact and gives it a name (`h1`).
   Here `zero_lt_one` is an axiom of our ordered field.
2. `have h2 : 1 + 0 < 1 + 1 := lt_add_left h1 1` — "Since 0 < 1, adding 1
   to both sides gives 1 + 0 < 1 + 1." The lemma `lt_add_left` says you can
   add the same thing to both sides of an inequality.
3. `rw [add_zero] at h2` — Simplify `h2`: rewrite `1 + 0` to `1`, so `h2`
   becomes `1 < 1 + 1`. The `at h2` means we're rewriting the intermediate
   fact, not the goal.
4. `exact lt_trans h1 h2` — "By transitivity, 0 < 1 and 1 < 1 + 1 give
   0 < 1 + 1." The `exact` tactic says "this term is the proof we need."

On paper: "Since 0 < 1 and 1 < 1 + 1 (by adding 1 to both sides of 0 < 1),
we have 0 < 1 + 1 by transitivity."

### Example 8: `neg_lt_zero` — using `have` without a name

```lean
theorem neg_lt_zero {a : R} (h : 0 < a) : -a < 0 := by
  have := lt_neg_flip h; rw [neg_zero] at this; exact this
```

Statement: if 0 < a, then -a < 0. (Negating a positive number gives a
negative number.)

This proof uses a shorthand: `have := ...` without giving a name. When you
omit the name, Lean calls it `this`. So:

1. `have := lt_neg_flip h` — the lemma `lt_neg_flip` says if a < b then
   -b < -a. Applied to `h : 0 < a`, it gives `this : -a < -0`.
2. `rw [neg_zero] at this` — rewrite `-0` to `0` in `this`, giving
   `this : -a < 0`.
3. `exact this` — that's our goal. Done.

### Example 9: proving an "and" with `constructor` and `intro`

When the goal is `P ∧ Q` ("P and Q"), the `constructor` tactic splits it into
two subgoals: first prove P, then prove Q. When the goal is a negation like
`¬P` (which is `P → False`), the `intro` tactic assumes P and asks you to
derive `False`.

Here's a simplified version of a proof from `Delta.lean`. Don't worry about
what `Delta` means yet — focus on the structure:

```lean
theorem delta_near_zero (d : Delta R) : (0 : R) ≤ d.val ∧ d.val ≤ 0 := by
  constructor
  · -- first goal: 0 ≤ d.val  (which means ¬(d.val < 0))
    intro h_neg
    ...            -- derive a contradiction from d.val < 0
  · -- second goal: d.val ≤ 0  (which means ¬(0 < d.val))
    intro h_pos
    ...            -- derive a contradiction from 0 < d.val
```

The `·` (center dot) introduces each subgoal after `constructor` splits the
"and." Within each branch, `intro` assumes the thing being negated (since
`≤` is defined as the negation of `<`), and the `...` is where you'd derive
a contradiction. The details of the contradiction aren't important here — the
pattern is:

1. `constructor` — "We prove each part separately."
2. `·` — "For the first part..."
3. `intro` — "Suppose the opposite..."
4. (derive contradiction)
5. `·` — "For the second part..."
6. `intro` — "Suppose the opposite..."
7. (derive contradiction)

This pattern appears throughout the project whenever we need to prove two
things at once.

### Example 10: `simp`

Here's a proof using `rw`:

```lean
theorem sub_zero (a : R) : a - 0 = a := by
  rw [sub_eq_add_neg, neg_zero, add_zero]
```

Three steps: expand subtraction (`a - 0` → `a + (-0)`), simplify `-0` to `0`,
then drop `+ 0`. With `simp`, this becomes:

```lean
theorem sub_zero (a : R) : a - 0 = a := by
  simp
```

Where `rw` applies one named lemma at a time, `simp` applies many at once.
It knows about `sub_eq_add_neg`, `neg_zero`, and `add_zero` because they are
registered as `@[simp]` lemmas (via the `attribute [simp]` or `@[simp]`
annotations in `Algebra.lean`). It figures out the right sequence of rewrites
automatically.

You can also give `simp` extra lemmas: `simp [foo, bar]` uses `foo` and `bar`
in addition to the registered `@[simp]` lemmas. You'll see this in the project
for routine cleanup that would take several `rw` steps to spell out.

Under the hood, `simp` just loops: scan for a matching lemma, rewrite, repeat
until nothing changes. The `@[simp]` lemmas must always go from "complex" to
"simple" — if both directions were registered, `simp` would loop forever.

---

## Reading term-mode proofs

Some proofs are written without `by`, as a single expression. These are
**term-mode proofs**. They're more concise but can be harder to read because
you have to work inside-out.

### Example 11: `le_refl`

```lean
theorem le_refl (a : R) : a ≤ a := lt_irrefl a
```

Wait — where's the proof? It's just `lt_irrefl a`. Let's work through why
this type-checks.

Lean unfolds `a ≤ a` to `¬(a < a)` (by the definition of ≤), which is
`(a < a) → False` (by the definition of `¬`). And `lt_irrefl a` has exactly
that type — it's the axiom that says a < a is impossible. So `lt_irrefl a` is already a term of the type
we need. Done.

The key insight: the "proof" is just citing a fact that already has the right
type. Lean does the definitional unfolding silently.

### Example 12: `lt_ne`

```lean
theorem lt_ne {a b : R} (h : a < b) : a ≠ b :=
  fun hab => lt_irrefl a (hab ▸ h)
```

We want to prove: if `a < b`, then `a ≠ b`.

First, Lean unfolds `a ≠ b` to `(a = b) → False`. So we need a function
that takes a proof of `a = b` and produces `False`.

- `fun hab =>` — assume `a = b` (Lean infers the type of `hab` as `a = b`,
  since that's what the unfolded goal requires)
- `hab ▸ h` — the `▸` symbol means "substitute". Given `hab : a = b`, the
  `▸` replaces `b` with `a` (right-to-left). So it turns `h : a < b` into a
  proof of `a < a`. (If you wanted the other direction — replacing `a` with
  `b` — you'd write `hab.symm ▸ h`, where `.symm` flips `a = b` to `b = a`.)
- `lt_irrefl a (...)` — a < a is impossible, so this produces `False`.

### Example 13: `le_of_lt` (revisited)

```lean
theorem le_of_lt {a b : R} (h : a < b) : a ≤ b :=
  fun hba => lt_irrefl a (lt_trans h hba)
```

Lean unfolds `a ≤ b` to `¬(b < a)` to `(b < a) → False`.

- `fun hba =>` — assume `b < a`
- `lt_trans h hba` — chain `h : a < b` and `hba : b < a` to get `a < a`
- `lt_irrefl a (...)` — `a < a` is impossible, producing `False`

### Example 14: `two_ne_zero`

```lean
theorem two_ne_zero : (1 + 1 : R) ≠ 0 :=
  Ne.symm (lt_ne zero_lt_two)
```

We want to prove `(1 + 1) ≠ 0`. Working inside-out:

1. `zero_lt_two` is a proof that `0 < 1 + 1`.
2. `lt_ne zero_lt_two` applies Example 12 ("if a < b then a ≠ b") to get
   `0 ≠ 1 + 1`.
3. But we need `(1 + 1) ≠ 0`, not `0 ≠ (1 + 1)`. These are *not* the same
   type: `0 ≠ 1 + 1` unfolds to `(0 = 1 + 1) → False`, while `(1 + 1) ≠ 0`
   unfolds to `(1 + 1 = 0) → False`. Lean does not silently convert between
   them.
4. `Ne.symm` flips `a ≠ b` to `b ≠ a`. Given a proof of `(a = b) → False`, it
   produces `(b = a) → False` by using `Eq.symm` to convert between the two
   equality directions. So `Ne.symm (lt_ne zero_lt_two)` has the type we need.

---

## Reading `calc` proofs

The `calc` tactic chains a sequence of equalities (or inequalities). Each
line transforms one side using a justification.

### Example 15: `neg_unique`

```lean
theorem neg_unique {a b : R} (h : a + b = 0) : b = -a := by
  calc b = 0 + b := by rw [zero_add]
    _ = ((-a) + a) + b := by rw [neg_add]
    _ = (-a) + (a + b) := by rw [add_assoc]
    _ = (-a) + 0 := by rw [h]
    _ = -a := by rw [add_zero]
```

Each `_` stands for "the previous expression." The chain reads:

    b = 0 + b             (by zero_add)
      = ((-a) + a) + b    (by neg_add, applied backwards)
      = (-a) + (a + b)    (by associativity)
      = (-a) + 0          (by hypothesis h: a + b = 0)
      = -a                (by add_zero)

**A note on how `rw` works inside `calc`.** Reading the chain, it looks like
each step transforms the LHS into the RHS — e.g., the first step rewrites `b`
into `0 + b`. But the tactic mechanism works in the opposite direction. The
goal for the first step is `b = 0 + b`, and `rw [zero_add]` rewrites
left-to-right (`0 + a` → `a`), so it simplifies the *RHS* `0 + b` to `b`,
giving `b = b`, which closes automatically. Similarly, the second step's goal
is `0 + b = ((-a) + a) + b`, and `rw [neg_add]` rewrites `(-a) + a` → `0` on
the RHS, giving `0 + b = 0 + b`. The calc block *presents* a chain building
up from left to right, but each `rw` tactic *proves* the step by simplifying
the right side to match the left.

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
argument, written out step by step.
</details>

### Example 16: calc steps without `rw`

In this project, every calc step happens to use `rw`. But calc doesn't
require this — each step just needs *some* proof that the equality holds.
You can use `exact`, a term-mode expression, or any other tactic. For
example, this proof from `Algebra.lean`:

```lean
theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  calc (-a) * (-b) = -(a * (-b)) := by rw [← neg_mul_left]
    _ = -(-(a * b)) := by rw [← neg_mul_right]
    _ = a * b := by rw [neg_neg]
```

Every step uses `rw`, but the last step could equally be written as:

```lean
    _ = a * b := neg_neg (a * b)
```

Here `neg_neg (a * b)` is a term-mode proof — we directly apply the lemma
`neg_neg : ∀ (a : R), -(-a) = a` to `a * b`, producing a proof that
`-(-(a * b)) = a * b`. No `by` or `rw` needed. Calc doesn't care *how*
you justify each step, only that the proof has the right type.

### Example 17: `add_right_cancel` — combining everything

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

The proof does in six rewrite steps what you'd do in one line on paper —
every algebraic simplification must be justified by name.

### Example 18: `lt_neg_flip` — combining everything

```lean
theorem lt_neg_flip {a b : R} (h : a < b) : -b < -a := by
  have h1 : -b + a < -b + b := lt_add_left h (-b)
  rw [neg_add] at h1
  have h2 : (-b + a) + -a < 0 + -a := lt_add_right h1 (-a)
  rw [zero_add, add_assoc, add_neg, add_zero] at h2
  exact h2
```

Statement: if a < b, then -b < -a. (Negation flips the direction of an
inequality.)

This proof uses `have` with term-mode proofs, `rw` on hypotheses (not the
goal), and `exact`. Let's trace through it:

1. `have h1 : -b + a < -b + b := lt_add_left h (-b)` — the lemma
   `lt_add_left` says: if a < b, then c + a < c + b. We apply it with
   c = -b to get `h1 : -b + a < -b + b`. This is a term-mode proof on the
   right side of `:=`.
2. `rw [neg_add] at h1` — rewrite `h1` using `neg_add` (which says
   -b + b = 0). Now `h1 : -b + a < 0`.
3. `have h2 : ... := lt_add_right h1 (-a)` — `lt_add_right` says: if
   x < y, then x + c < y + c. We add -a to both sides, getting
   `h2 : (-b + a) + -a < 0 + -a`.
4. `rw [zero_add, add_assoc, add_neg, add_zero] at h2` — four rewrites
   simplify `h2`. The left side: `(-b + a) + -a = -b + (a + -a) = -b + 0 = -b`.
   The right side: `0 + -a = -a`. So `h2` becomes `-b < -a`.
5. `exact h2` — that's our goal. Done.

On paper: "Add -b to both sides of a < b to get -b + a < 0. Add -a to both
sides to get -b < -a."

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

5. **Read names as hints.** Variable names are not meaningful to Lean — what
   matters is their *type*. But authors follow conventions that help you read
   proofs: `h` for a generic hypothesis, `hab` for a hypothesis about `a` and
   `b`, `hc` for a hypothesis about `c`, `h_neg` or `h_pos` for sign
   assumptions. Theorem names follow `conclusion_of_hypothesis` — e.g.,
   `le_of_lt` means "≤ from <" and `lt_ne` means "< implies ≠".

6. **Follow the types.** Every expression has a type. A proof works because
   the types line up — each function receives arguments of the right type and
   produces output of the right type. When in doubt, ask: "What type does
   this expression have?"

---

## Quick reference: symbols

| Symbol | Type | Meaning | Example |
|--------|------|---------|---------|
| `→` | `\to` or `\r` | implies / function type | `a < b → a ≤ b` |
| `∀` | `\forall` | for all | `∀ (a : R), a + 0 = a` |
| `∃` | `\exists` | there exists | `∃ x, x > 0` |
| `∧` | `\and` | and | `0 ≤ d ∧ d ≤ 0` |
| `∨` | `\or` | or | `a < b ∨ b < a` |
| `¬` | `\neg` | not (`P → False`) | `¬(a < a)` |
| `≠` | `\ne` | not equal (`(a = b) → False`) | `a ≠ 0` |
| `≤` | `\le` | less or equal (`¬(b < a)`) | `a ≤ b` |
| `▸` | `\t` | substitute an equality | `hab ▸ h` rewrites `h` using `hab` |
| `⟨ ⟩` | `\langle` `\rangle` | build a pair or structure | `⟨proof_of_P, proof_of_Q⟩` |
| `⁻¹` | `\inv` | inverse | `a⁻¹` |
| `·` | `\cdot` | subgoal marker | used after `constructor` |
| `←` | `\l` | rewrite backwards | `rw [← add_assoc]` |
| `_` | | "the previous expression" | used in `calc` chains |
| `:=` | | "here is the proof/definition" | |
| `(x : T)` | | "`x` has type `T`" | `(a : R)`, `(h : a < b)` |
