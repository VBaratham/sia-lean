# Article 1b: Lean as a Proof Language

Article 1 gave a brief sketch of Lean: types, terms, theorems, tactics. This article
goes deeper. If you want to actually *read* the proofs in this project and convince
yourself they're correct, you need to understand *why* Lean's approach works — why
writing a program can constitute a mathematical proof.

## The core idea: propositions are types

In ordinary math, you work with two separate worlds:

1. **Mathematical objects**: numbers, functions, sets, etc.
2. **Logical statements**: "2 < 3", "every continuous function is integrable", etc.

You construct objects and you *prove* statements. These feel like different activities.

Lean unifies them. In Lean, a logical statement *is* a type, and a proof of that
statement *is* a value (called a "term") of that type. This is known as the
**Curry-Howard correspondence**, and it's the foundation of how Lean works.

Here's the analogy. Think of a type as a box with a label on it. The label describes
what's inside. Some boxes have things in them; some are empty.

- The type `Nat` is a box labeled "natural numbers." It contains 0, 1, 2, 3, ...
- The type `String` is a box labeled "strings." It contains "hello", "world", etc.
- The type `2 + 2 = 4` is a box labeled "proofs that 2 + 2 = 4." It's not empty — you
  can construct a proof of this.
- The type `2 + 2 = 5` is a box labeled "proofs that 2 + 2 = 5." This box is empty.
  There is no proof, because the statement is false.

A true statement is a type that has at least one term (a "proof"). A false statement is
a type with no terms (an "empty type"). Proving a theorem means constructing a term that
Lean's type checker accepts as inhabiting the theorem's type. If the code compiles, the
proof is valid.

### How can a type have no values?

If you're coming from a programming background, this might seem strange. In most
languages, every type you can write down has at least one value. But Lean's type system
is more expressive — it supports **dependent types**, where a type can depend on a
specific *value*, not just on other types.

In most languages, types can depend on types: `List<Int>`, `Map<String, Bool>`. But the
type can't refer to a specific runtime value. In Lean, it can. The type `a = b` depends
on the specific values `a` and `b`. The type `Vector n` depends on the specific number
`n`.

This is where uninhabitable types come from naturally. In Lean, a type is defined by
listing its **constructors** — the ways you can create a value. The equality type has
one constructor, `rfl`, whose signature says: given any value `a`, produce a proof that
`a = a`. Both sides of the equality must be the same. So `rfl` can produce a proof of
`4 = 4` or `7 = 7`, but to produce a proof of `4 = 5`, you'd need a value that is
simultaneously 4 and 5. No such value exists, so the constructor can't be called with
valid inputs. The type `4 = 5` is empty — not because anyone declared it empty, but as
a *consequence* of the definition.

The simplest empty type is `False`, which is defined as an inductive type with zero
constructors — there's simply no way to build a value of type `False`. This is what
makes it work as logical falsehood: the type exists, but no term can ever be
constructed.

## A concrete example

Suppose we have a theorem statement:

    theorem add_comm : ∀ (a b : Nat), a + b = b + a

Reading this in English: "For all natural numbers a and b, a + b equals b + a."

In Lean's view, `∀ (a b : Nat), a + b = b + a` is a *type*. The `theorem` keyword
tells Lean we're about to construct a term of this type — i.e., a proof.

What comes after `:=` (or after `by`, which starts "tactic mode") is the proof term.
If Lean can type-check it, the theorem is proved. If not, you get a compile error.

## What does a proof term actually look like?

You can write proofs in Lean two ways:

**1. Term-mode proofs** — you directly construct the proof object, much like writing a
function. Here's a real example from our code:

    theorem le_of_lt {a b : R} (h : a < b) : a ≤ b :=
      fun hba => lt_irrefl a (lt_trans h hba)

The name `le_of_lt` reads as "less-or-equal from less-than" — a naming convention used
throughout Lean: `conclusion_of_hypothesis`. We want to prove: if `a < b`, then `a ≤ b`.

But what does `a ≤ b` actually *mean* in Lean? It's defined in terms of simpler concepts:

- `a ≤ b` is defined as `¬(b < a)` ("b is not less than a")
- `¬(b < a)` is defined as `(b < a) → False` ("a proof of `b < a` would give a contradiction")

So to prove `a ≤ b`, we need to build a function that takes a hypothetical proof of
`b < a` and produces `False`. On paper, you'd write: "Suppose for contradiction that
b < a. Then ... contradiction." In Lean, "suppose for contradiction" becomes `fun`,
and the contradiction becomes the function body.

(A note on terminology: this is *not* "proof by contradiction" in the classical sense.
Classical proof by contradiction proves a positive statement P by assuming ¬P and
deriving False, which requires LEM. Here we are proving a *negative* statement —
`¬(b < a)` — by assuming `b < a` and deriving False. That is the *definition* of
proving a negation, and it is constructively valid.)

The proof `fun hba => lt_irrefl a (lt_trans h hba)` is exactly that function:

- `fun hba =>` introduces a hypothetical proof that `b < a`. The name `hba` is
  arbitrary — we could have called it `x` or `assumption`. Lean figures out that
  `hba` has type `b < a` by unfolding the definitions above: we need to produce a
  term of type `a ≤ b`, which is `¬(b < a)`, which is `(b < a) → False`, so the
  input to `fun` must have type `b < a`. All of this unfolding happens silently
  inside Lean's type checker.
- `lt_trans h hba` chains `h : a < b` with `hba : b < a` to get a proof of `a < a`.
  (Here `lt_trans` is a previously proved theorem with type `a < b → b < c → a < c` —
  we apply it to our two proofs and get a proof of `a < a`.)
- `lt_irrefl a` is a proof that `¬(a < a)`, i.e., a function `(a < a) → False`.
  Applying it to our proof of `a < a` produces `False`. This is the contradiction.

The result is a term of type `(b < a) → False`, which is `¬(b < a)`, which is `a ≤ b`.
Proof complete.

This is the key mechanism: axioms and previously proved theorems are functions that
produce proofs. You combine them — applying one result to another — to build proofs
of new statements.

**2. Tactic-mode proofs** — you use `by` to enter a step-by-step mode where Lean
tracks a "goal" (what you still need to prove) and you chip away at it:

    theorem sub_self (a : R) : a - a = 0 := by
      rw [sub_eq_add_neg, add_neg]

Here, Lean starts with the goal `a - a = 0`. The tactic `rw [sub_eq_add_neg]` rewrites `a - a`
to `a + (-a)` (using the definition of subtraction), changing the goal to
`a + (-a) = 0`. Then `rw [add_neg]` rewrites that to `0 = 0`, which is trivially true.
Goal closed, proof done.

Both styles produce the same thing: a term of the right type. Tactics are just a
convenient way to build the term incrementally.

## Why "propositions are types" makes sense

This isn't just a trick — there's a deep reason the analogy works. Logical connectives
correspond to type-forming operations:

### Implication is a function type

The proposition "if P then Q" (written `P → Q`) is the type of functions from P to Q.

Why does this make sense? If you have a proof of P (a term `h : P`) and a function
`f : P → Q`, you can apply it to get `f h : Q` — a proof of Q. That's exactly what
"if P then Q" means: given a proof of P, you can produce a proof of Q.

When you see a Lean proof that says:

    theorem le_of_lt {a b : R} (h : a < b) : a ≤ b :=
      fun hba => lt_irrefl a (lt_trans h hba)

This is a function. It takes a proof `h` that `a < b` and returns a proof that `a ≤ b`.
Since `a ≤ b` is defined as `¬(b < a)`, which is `(b < a) → False`, the proof needs to
be a function taking a hypothetical proof `hba : b < a` and producing a contradiction
(`False`). It does this by chaining `h : a < b` and `hba : b < a` via transitivity to
get `a < a`, then applying irreflexivity to get `False`.

### "For all" is a dependent function type

`∀ (x : T), P x` is the type of functions that, given any `x` of type `T`, produce a
proof of `P x`. This is a "dependent" function type because the output type `P x`
depends on the input `x`.

    theorem delta_near_zero (d : Delta R) : 0 ≤ d.val ∧ d.val ≤ 0 := ...

This is a function from `d : Delta R` to a proof of `0 ≤ d.val ∧ d.val ≤ 0`. The
output type depends on which `d` you give it.

### "And" is a pair (product type)

`P ∧ Q` is the type of pairs where the first element is a proof of P and the second is
a proof of Q. To prove `P ∧ Q`, you need to provide both proofs.

In the proof of `delta_near_zero`, you'll see:

    constructor

This tactic splits the goal `P ∧ Q` into two subgoals: prove P, then prove Q.
It's building a pair.

### "Or" is a tagged union (sum type)

`P ∨ Q` is a type whose terms are either a proof of P (tagged "left") or a proof of Q
(tagged "right"). To *use* a proof of `P ∨ Q`, you need to handle both cases — you
don't know which one you have.

This is why `.elim` appears so often in our proofs:

    (ne_lt hne).elim (fun h => ...) (fun h => ...)

The term `ne_lt hne` has type `a < b ∨ b < a`. The `.elim` says: "either we get
`a < b` (handle in the first branch) or we get `b < a` (handle in the second branch)."

### Negation is a function to False

`¬P` is defined as `P → False`. A proof of "not P" is a function that takes any
hypothetical proof of P and produces a contradiction. Since `False` is the empty type
(with no terms), this function can only exist if P itself has no proofs — i.e., if P
is false.

### "There exists" is a dependent pair

`∃ (x : T), P x` is the type of pairs `⟨witness, proof⟩` where `witness : T` and
`proof : P witness`. To prove something exists, you produce a specific example and a
proof that it satisfies the property.

## Why this matters for our project

Understanding propositions-as-types is essential for reading our code because it
explains what's *really happening* in every proof:

1. When we write `theorem not_lem_on_delta : ¬ (∀ (d : Delta R), d.val = 0 ∨ d.val ≠ 0)`,
   we're defining a type and promising to construct a term of that type. The type
   unfolds to: a *function* that takes a hypothetical proof that every Delta element is
   decidably zero, and produces `False`.

2. When a proof says `intro lem`, it's saying: "I'm building a function. Let `lem` be
   the input." This is literally lambda abstraction — `fun lem => ...`.

3. When a proof says `exact h`, it's saying: "The term `h` already has the right type.
   I'm done."

4. When a proof says `rw [add_comm]`, it's transforming the goal type using the fact
   that `a + b = b + a`, then continuing to build a term of the transformed type.

The entire proof is just a program. Lean's type checker verifies that the program has
the right type, and that's what makes the proof valid. No trust required beyond the type
checker itself.

## What "compiles means it's correct" really means

This is the key payoff. In a traditional math paper, a proof is an argument written in
English (or a mix of English and symbols) that a human reader checks for correctness.
Humans make mistakes. Referees miss gaps. Errors can persist for years.

In Lean, the proof is a program. Lean's kernel — a small, well-studied piece of code —
checks that every term has the type it claims. If the type checker accepts your proof of
`∀ (d : Delta R), ¬¬(d.val = 0)`, then it *really is* a valid proof, assuming only
Lean's kernel is correct. The kernel is small enough (a few thousand lines) that it can
be (and has been) independently audited and verified.

This is why the `#print axioms` checks in Article 9 are so powerful. When Lean tells us
that `not_lem_on_delta` depends only on `propext`, we know — with machine certainty —
that the proof never used classical logic. Not "we think it didn't" or "we were careful
not to." The computer verified it.

## A note on constructive logic

One more thing that's important for our project. Lean's type theory is
*constructive* by default. This means:

- To prove `∃ x, P x`, you must *produce* a specific `x`. You can't just argue "suppose
  no x exists, then contradiction." (That would require LEM.)
- To prove `P ∨ Q`, you must *produce* either a proof of P or a proof of Q. You can't
  just argue "if not P then Q." (That would also require LEM.)

Lean *does* offer classical reasoning through the `Classical` module, which adds the
axiom `Classical.choice`. If you import it, you can use proof by contradiction, the law
of the excluded middle, and nonconstructive existence proofs. Most Lean projects
(including Mathlib, the big math library) use this freely.

But we don't. Our project deliberately avoids `Classical.choice`, which is what lets us
work in the constructive setting that SIA requires. Article 9 verifies that we
succeeded.

## Quick reference

| Logic | Type theory | Lean syntax |
|-------|-------------|-------------|
| "if P then Q" | function `P → Q` | `fun (h : P) => ...` |
| "P and Q" | pair `P × Q` | `⟨proof_of_P, proof_of_Q⟩` |
| "P or Q" | tagged union `P ⊕ Q` | `Or.inl h` or `Or.inr h` |
| "for all x, P(x)" | dependent function `(x : T) → P x` | `fun (x : T) => ...` |
| "there exists x, P(x)" | dependent pair `Σ x, P x` | `⟨witness, proof⟩` |
| "not P" | function `P → False` | `fun (h : P) => ...` |
| "P is true" | type `P` is inhabited | some term `t : P` exists |
| "P is false" | type `P` is empty | no term of type `P` exists |

If you'd like more practice reading Lean syntax before diving into the code,
[Article 1c](01c-reading-lean-proofs.md) works through a series of examples and
exercises using real proofs from this project.

Otherwise, you're ready to read the actual code. Article 2 starts with the algebraic
foundations.
