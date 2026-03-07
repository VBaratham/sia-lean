# Article 2: Algebra.lean — Building a Number System from Scratch

In the previous article, we described the big picture: Smooth Infinitesimal Analysis
(SIA) is a way to do calculus using infinitesimals instead of limits, and we are
formalizing it in Lean 4. Before we can talk about infinitesimals, derivatives, or
continuity, we need a number system. This file builds one from the ground up.

If you have taken an algebra course, you know that the real numbers form a
**commutative ring** and a **field**. You can add, subtract, multiply, and divide
(except by zero), and these operations satisfy familiar laws like commutativity and
distributivity. In standard math, you might just say "let R be a field" and move on.
In Lean, we have to spell out exactly what that means — every axiom, every operation,
every compatibility condition.

This article walks through `SIA/Algebra.lean` line by line. We will explain every piece
of Lean syntax as it comes up, so no prior Lean knowledge is required.

## Why build from scratch?

Lean 4 has a massive mathematical library called **Mathlib** that already defines
commutative rings, fields, and thousands of theorems about them. So why not use it?

The reason is that Mathlib is built on **classical logic** — it freely uses the Law of
the Excluded Middle (LEM), which says that every proposition is either true or false.
As we discussed in Article 1, SIA is *incompatible* with LEM. If we imported Mathlib's
ring and field definitions, classical axioms would leak into our foundations, and we
could no longer guarantee that our proofs are constructive.

By building from scratch, we have complete control. Every axiom is something we wrote
down explicitly, and at the end (Article 9) we can ask Lean to verify that no classical
axioms were used anywhere.

## The file header and universe declaration

```lean
/-
  SIA.Algebra — Basic algebraic structures without Mathlib
  ...
-/

universe u
```

The `/-` ... `-/` block is a comment. Lean ignores it entirely.

`universe u` is more interesting. In Lean, every type lives at a **universe level**.
You can think of universe levels as a way to avoid paradoxes (like "the set of all
sets"). Ordinary types like natural numbers live at level 0, written `Type 0` or just
`Type`. The type of all `Type 0` types lives at `Type 1`. And so on.

By writing `universe u`, we are declaring a universe variable. When we later write
`Type u`, we are saying "some type at some universe level — we don't care which one."
This makes our definitions work for any universe level, not just level 0.

For the purposes of this series, you can mostly ignore universe annotations. They are
a technicality that keeps Lean's foundations consistent. Think of `Type u` as meaning
"any type."

## The CommRing class

Here is the heart of the file:

```lean
class CommRing (R : Type u) extends Add R, Mul R, Neg R, Sub R, Zero R, One R where
  add_assoc     : ∀ (a b c : R), (a + b) + c = a + (b + c)
  add_comm      : ∀ (a b : R), a + b = b + a
  add_zero      : ∀ (a : R), a + 0 = a
  add_neg       : ∀ (a : R), a + (-a) = 0
  sub_eq        : ∀ (a b : R), a - b = a + (-b)
  mul_assoc     : ∀ (a b c : R), (a * b) * c = a * (b * c)
  mul_comm      : ∀ (a b : R), a * b = b * a
  mul_one       : ∀ (a : R), a * 1 = a
  left_distrib  : ∀ (a b c : R), a * (b + c) = a * b + a * c
```

There is a lot going on here. Let's take it piece by piece.

### What is a `class`?

In Lean, a `class` is a way to bundle together operations and axioms that a type must
satisfy. Think of it as a contract. When you write `class CommRing (R : Type u)`, you
are defining a contract called `CommRing` that any type `R` can sign up for. To sign
the contract, `R` must provide all the operations and prove all the axioms listed
inside.

If you have used interfaces in Java or protocols in Swift, it is the same idea. A
`class` says "any type that wants to call itself a CommRing must provide these things."

The crucial feature of Lean classes is **instance resolution**: once you declare that
some type `R` is a `CommRing`, Lean will automatically find and use that declaration
whenever it needs ring operations on `R`. You write `[CommRing R]` (with square
brackets) and Lean handles the rest. We will see this in action shortly.

### What does `extends` mean?

```lean
class CommRing (R : Type u) extends Add R, Mul R, Neg R, Sub R, Zero R, One R where
```

The `extends` keyword says that `CommRing` builds on top of other, simpler classes.
Lean 4 already provides basic **operation classes** out of the box:

- `Add R` means "`R` has an addition operation `+`"
- `Mul R` means "`R` has a multiplication operation `*`"
- `Neg R` means "`R` has a negation operation `-`" (as a prefix, like `-a`)
- `Sub R` means "`R` has a subtraction operation `-`" (as an infix, like `a - b`)
- `Zero R` means "`R` has a distinguished element called `0`"
- `One R` means "`R` has a distinguished element called `1`"

These built-in classes provide the *notation* — they tell Lean what `+`, `*`, `-`, `0`,
and `1` mean for a given type — but they say nothing about how these operations behave.
You could have a type where `a + b` means something completely different from what you
expect. The `CommRing` class adds the *rules* (axioms) that these operations must
follow.

By writing `extends Add R, Mul R, ...`, we are saying: "A CommRing automatically
inherits all six operation classes. If you know something is a CommRing, you
automatically know it has `+`, `*`, etc."

### The axioms, one by one

After the `where` keyword come the axioms. Each one has a name and a type. In Lean,
a theorem statement *is* a type — the type of all proofs of that statement. So
`add_assoc : ...` is saying "a CommRing must come with a proof of associativity,
and that proof is called `add_assoc`."

Let's read the symbol `∀`. In Lean, `∀ (a : R), ...` means "for all `a` of type `R`,
the following holds." This is the universal quantifier from logic. `∀ (a b c : R), ...`
is shorthand for "for all `a`, `b`, and `c` of type `R`."

Now the axioms themselves. If you have taken any algebra course, these will be familiar:

**Addition axioms:**

- `add_assoc`: `(a + b) + c = a + (b + c)` — Parentheses don't matter for addition.
- `add_comm`: `a + b = b + a` — Order doesn't matter for addition.
- `add_zero`: `a + 0 = a` — Zero is a right identity.
- `add_neg`: `a + (-a) = 0` — Every element has a right additive inverse.

**Subtraction:**

- `sub_eq`: `a - b = a + (-b)` — Subtraction is just addition of the negative. This
  *defines* subtraction in terms of addition and negation.

**Multiplication axioms:**

- `mul_assoc`: `(a * b) * c = a * (b * c)` — Parentheses don't matter for multiplication.
- `mul_comm`: `a * b = b * a` — Order doesn't matter for multiplication. (This is
  the "commutative" part of "commutative ring.")
- `mul_one`: `a * 1 = a` — One is a right identity.

**Distributivity:**

- `left_distrib`: `a * (b + c) = a * b + a * c` — Multiplication distributes over
  addition from the left.

### Why only 9 axioms?

If you've seen commutative rings defined elsewhere, you might be used to seeing more
axioms — left identity *and* right identity, left inverse *and* right inverse, and so
on. We derive all of those as theorems from the 9 axioms above.

The key insight is **commutativity**. Since we have `add_comm` (a + b = b + a), we
only need *one* of `add_zero`/`zero_add`, and the other follows:

```lean
theorem zero_add (a : R) : 0 + a = a := by rw [add_comm, add_zero]
```

The same applies to `neg_add` (from `add_neg`), `one_mul` (from `mul_one`),
`right_distrib` (from `left_distrib`), and `neg_mul_right` (from `neg_mul_left`).

Even more interestingly, several properties that *look* like they should be axioms
can be derived from the 9 above using algebraic reasoning:

- **`mul_zero`** (`a * 0 = 0`): Since `a * 0 + a * 0 = a * (0 + 0) = a * 0`,
  we can cancel to get `a * 0 = 0`.
- **`neg_neg`** (`-(-a) = a`): Since `-a + a = 0`, uniqueness of inverses gives
  `a = -(-a)`.
- **`neg_zero`** (`-0 = 0`): Since `0 + 0 = 0`, uniqueness of inverses gives
  `0 = -0`.
- **`neg_mul_left`** (`-(a * b) = (-a) * b`): Since `a*b + (-a)*b = (a + (-a))*b
  = 0*b = 0`, uniqueness of inverses gives `(-a)*b = -(a*b)`.

All of these are proved as theorems in the file. The result is a minimal set of
axioms — just the 9 that are truly independent.

## The CommRing namespace and derived lemmas

```lean
namespace CommRing

variable {R : Type u} [CommRing R]
```

### Namespaces

A `namespace CommRing` block is an organizational tool. Everything defined between
`namespace CommRing` and `end CommRing` gets the prefix `CommRing.` attached to its
name. So a theorem called `sub_self` inside this namespace has the full name
`CommRing.sub_self`. This prevents name collisions — if we later defined a different
`sub_self` in a different context, they would not conflict.

Namespaces also provide convenient access: when you `open CommRing`, you can use
`sub_self` without the prefix.

### The `variable` declaration

```lean
variable {R : Type u} [CommRing R]
```

This line says: "For everything that follows in this namespace, assume we have a type
`R` (at universe level `u`) that is a CommRing."

The **curly braces** `{R : Type u}` make `R` an **implicit argument**. This means Lean
will figure out what `R` is from context, so we don't have to write it explicitly every
time. When we later write `sub_self (a : R)`, Lean infers which `R` we mean from the
type of `a`.

The **square brackets** `[CommRing R]` are the syntax for **instance arguments** (also
called typeclass arguments). This tells Lean: "Find a CommRing instance for R
automatically." When we later use `add_neg` or `mul_comm` in a proof, Lean knows these
come from the CommRing instance and finds them without us having to point to them
explicitly. This is the instance resolution mechanism we mentioned earlier.

Together, this `variable` line means: "Everything below works for any type `R` that
is a commutative ring, and Lean should figure out `R` and its ring structure
automatically from context."

### The `attribute [simp]` declaration

```lean
attribute [simp] add_zero zero_add add_neg neg_add mul_one one_mul mul_zero zero_mul
                 neg_neg neg_zero
```

This line registers a collection of lemmas as **simplification lemmas**. The `simp`
tactic in Lean is an automated simplifier — it repeatedly applies a set of rewrite
rules to try to reduce an expression to a simpler form. By marking `add_zero` as a
simp lemma, we are telling Lean: "Whenever you see `a + 0`, you can simplify it to
`a`."

The lemmas chosen here are all of the form "something complicated equals something
simpler": `a + 0` simplifies to `a`, `a * 1` simplifies to `a`, `-(-a)` simplifies
to `a`, and so on. Some of these are axioms (`add_zero`, `add_neg`, `mul_one`) and
some are derived theorems (`zero_add`, `neg_add`, `one_mul`, `mul_zero`, `zero_mul`,
`neg_neg`, `neg_zero`), but Lean treats them identically once they are registered.

### Derived lemma: `sub_self`

```lean
@[simp] theorem sub_self (a : R) : a - a = 0 := by
  rw [sub_eq, add_neg]
```

This is a **derived lemma** — a theorem proved from the axioms, rather than
assumed. Let's read every part of this line.

`@[simp]` is an **attribute annotation**. It does the same thing as the `attribute
[simp]` line above, but for a single theorem. It registers `sub_self` as a
simplification rule: whenever Lean sees `a - a`, it can simplify to `0`.

`theorem` introduces a theorem (or lemma — Lean does not distinguish between the two
keywords `theorem` and `lemma`).

`sub_self` is the name of the theorem.

`(a : R)` is an explicit argument: this theorem takes an element `a` of type `R`.

`: a - a = 0` is the statement: "a minus a equals zero."

`:= by` begins the proof. The keyword `by` switches Lean into **tactic mode**. In
tactic mode, you give step-by-step instructions for building the proof, rather than
writing the proof term directly. Think of it like giving directions ("turn left, then
go straight") rather than specifying the destination's GPS coordinates.

Now the proof itself:

- `rw [sub_eq]` — The `rw` tactic stands for **rewrite**. It takes a lemma and
  replaces the left-hand side with the right-hand side wherever it appears in the goal.
  Here, `sub_eq` says `a - b = a + (-b)`, so `rw [sub_eq]` transforms the goal
  from `a - a = 0` to `a + (-a) = 0`.

- `rw [add_neg]` — Now `add_neg` says `a + (-a) = 0`, so this rewrite transforms
  `a + (-a) = 0` into `0 = 0`, which Lean accepts as trivially true.

That is the pattern for most proofs in this file: rewrite using known facts until the
goal becomes trivially true.

### Cancellation lemmas

```lean
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add, zero_add]
```

This says: if you add `-a`, then `a`, then `b`, you just get `b`. The negative and
positive cancel out.

The proof introduces one new piece of syntax: the **left arrow** `←` (typed as
`\l` or `\leftarrow` in Lean). Normally, `rw [add_assoc]` rewrites left-to-right:
it replaces `(x + y) + z` with `x + (y + z)`. The arrow `← add_assoc` rewrites
right-to-left: it replaces `x + (y + z)` with `(x + y) + z`.

So the proof goes:

1. Start with: `-a + (a + b) = b`
2. `rw [← add_assoc]`: regroup as `(-a + a) + b = b`
3. `rw [neg_add]`: replace `-a + a` with `0`, giving `0 + b = b`
4. `rw [zero_add]`: replace `0 + b` with `b`, giving `b = b`. Done.

The next lemma is symmetric:

```lean
theorem add_neg_cancel_left (a b : R) : a + (-a + b) = b := by
  rw [← add_assoc, add_neg, zero_add]
```

Same idea: regroup, cancel `a + (-a)` to `0`, then drop the `0 +`.

### Uniqueness of negation

```lean
theorem neg_unique {a b : R} (h : a + b = 0) : b = -a := by
  calc b = 0 + b := by rw [zero_add]
    _ = ((-a) + a) + b := by rw [neg_add]
    _ = (-a) + (a + b) := by rw [add_assoc]
    _ = (-a) + 0 := by rw [h]
    _ = -a := by rw [add_zero]
```

This theorem says: if `a + b = 0`, then `b` must be `-a`. In other words, the additive
inverse is unique. You might already know this intuitively — there is only one number
you can add to 5 to get 0, and it is -5.

The curly braces `{a b : R}` make `a` and `b` implicit arguments — Lean will infer
them from context. The parenthesized `(h : a + b = 0)` is an explicit **hypothesis**:
a proof that `a + b = 0`. Think of `h` as "the thing the caller must hand us."

This proof uses a new tactic: `calc`. The `calc` tactic lets you write a chain of
equalities, like a calculation on a whiteboard. Each line has the form
`_ = (something) := by (justification)`. The underscore `_` stands for "whatever the
previous line ended with."

Walking through it:

1. `b = 0 + b` — True by `zero_add` (0 is a left identity).
2. `0 + b = ((-a) + a) + b` — Replace the `0` with `(-a) + a`, which we know equals
   zero by `neg_add`. (The rewrite goes right-to-left here.)
3. `((-a) + a) + b = (-a) + (a + b)` — Reassociate using `add_assoc`.
4. `(-a) + (a + b) = (-a) + 0` — Replace `a + b` with `0` using the hypothesis `h`.
5. `(-a) + 0 = -a` — Drop the zero using `add_zero`.

The chain shows `b = -a`, which is exactly what we wanted to prove.

### Negation distributes over addition

```lean
theorem neg_add_distrib (a b : R) : -(a + b) = -a + -b := by
  have h : (a + b) + (-a + -b) = 0 := by
    calc (a + b) + (-a + -b)
      = a + (b + (-a + -b)) := by rw [add_assoc]
    _ = a + ((b + -a) + -b) := by rw [add_assoc]
    _ = a + ((-a + b) + -b) := by rw [add_comm b (-a)]
    _ = a + (-a + (b + -b)) := by rw [add_assoc]
    _ = a + (-a + 0) := by rw [add_neg]
    _ = a + -a := by rw [add_zero]
    _ = 0 := by rw [add_neg]
  exact (neg_unique h).symm
```

This is the most involved proof so far. It says `-(a + b) = -a + -b` — negation
distributes over addition, just like the minus sign distributes in ordinary algebra:
`-(x + y) = -x + -y`.

The proof strategy is clever. Rather than manipulating `-(a + b)` directly, it uses
`neg_unique`: if we can show that `(a + b) + (-a + -b) = 0`, then by uniqueness of
inverses, `-a + -b` must equal `-(a + b)`.

The `have` keyword introduces an intermediate result. `have h : ... := by ...` says
"let me first prove this intermediate fact, and call it `h`." Then we use `h` in the
final step.

The `calc` block proves the intermediate fact by a long chain of associativity and
commutativity manipulations — the kind of routine rearrangement you would do on paper
without writing down every step. In Lean, every step must be justified.

The final line `exact (neg_unique h).symm` deserves explanation:

- `exact` is a tactic that says "here is the proof term directly."
- `neg_unique h` gives us a proof that `-a + -b = -(a + b)` (the inverse of `a + b`
  is `-a + -b`).
- But our goal is `-(a + b) = -a + -b` — the sides are swapped.
- `.symm` flips an equality: if `p` is a proof of `x = y`, then `p.symm` is a proof
  of `y = x`.

### Negative times negative

```lean
theorem neg_mul_neg (a b : R) : (-a) * (-b) = a * b := by
  calc (-a) * (-b) = -(a * (-b)) := by rw [← neg_mul_left]
    _ = -(-(a * b)) := by rw [← neg_mul_right]
    _ = a * b := by rw [neg_neg]
```

A negative times a negative is positive. The proof uses the axioms about pulling
negation signs into and out of products, then cancels the double negation.

### Subtraction and multiplication

```lean
theorem mul_sub (a b c : R) : a * (b - c) = a * b - a * c := by
  rw [sub_eq, sub_eq, left_distrib, neg_mul_right]

theorem sub_mul (a b c : R) : (a - b) * c = a * c - b * c := by
  rw [sub_eq, sub_eq, right_distrib, neg_mul_left]
```

These distribute multiplication over subtraction. The proofs expand subtraction as
"add the negative" (using `sub_eq`), apply distributivity, then fold a negation back
into the product.

### Additive cancellation

```lean
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have : -a + (a + b) = -a + (a + c) := by rw [h]
  rw [neg_add_cancel_left, neg_add_cancel_left] at this
  exact this
```

If `a + b = a + c`, then `b = c`. You can cancel from the left. The proof adds `-a`
to both sides. (The `have :` without a name creates an anonymous hypothesis; Lean calls
it `this`.)

The `at this` syntax tells `rw` to rewrite in the hypothesis `this` rather than in the
goal. After the two rewrites, `this` becomes `b = c`, and `exact this` finishes the
proof.

```lean
theorem add_right_cancel {a b c : R} (h : a + c = b + c) : a = b := by
  have : (a + c) + -c = (b + c) + -c := by rw [h]
  rw [add_assoc, add_neg, add_zero, add_assoc, add_neg, add_zero] at this
  exact this
```

Same idea, canceling from the right. The proof adds `-c` to both sides and simplifies.
Notice the chain of rewrites: `add_assoc` regroups, `add_neg` cancels `c + (-c)` to
`0`, and `add_zero` drops the zero. This chain is applied to both sides (Lean applies
each rewrite to the first match it finds, working through both sides of the equation
in `this`).

### Subtraction and addition cancellation

```lean
theorem sub_add_cancel (a b : R) : a - b + b = a := by
  rw [sub_eq, add_assoc, neg_add, add_zero]

theorem add_sub_cancel (a b : R) : a + b - b = a := by
  rw [sub_eq, add_assoc, add_neg, add_zero]
```

These say that subtraction and addition are inverse operations: subtracting `b` and
then adding it back (or vice versa) gives you back what you started with. The proofs
expand subtraction, reassociate, cancel the inverse pair, and drop the zero.

### Zero and subtraction

```lean
@[simp] theorem sub_zero (a : R) : a - 0 = a := by
  rw [sub_eq, neg_zero, add_zero]

@[simp] theorem zero_sub (a : R) : 0 - a = -a := by
  rw [sub_eq, zero_add]
```

Subtracting zero does nothing. Subtracting from zero gives the negation. Both are
marked `@[simp]` because they are straightforward simplifications.

### Negation of a difference

```lean
theorem neg_sub (a b : R) : -(a - b) = b - a := by
  rw [sub_eq, sub_eq, neg_add_distrib, neg_neg, add_comm]
```

Negating a difference flips the order: `-(a - b) = b - a`. The proof expands both
subtractions, distributes the negation, cancels the double negative on `b`, and swaps
the order using commutativity.

```lean
end CommRing
```

This closes the `CommRing` namespace. Everything defined between `namespace CommRing`
and `end CommRing` has the `CommRing.` prefix.

## The CField class

With commutative rings in hand, we now define fields — rings where you can also divide.

```lean
class CField (R : Type u) extends CommRing R, Inv R, Div R where
  div_eq      : ∀ (a b : R), a / b = a * b⁻¹
  mul_inv     : ∀ {a : R}, a ≠ 0 → a * a⁻¹ = 1
  inv_zero    : (0 : R)⁻¹ = 0
```

### Why "CField" and not "Field"?

The name `CField` stands for "constructive field" (though it could also be read as
"custom field"). We avoid the name `Field` to prevent any confusion or collision with
Mathlib's `Field` class.

### The structure

`CField` extends three things:

- `CommRing R` — everything we just defined (addition, multiplication, all the axioms).
- `Inv R` — provides the notation `a⁻¹` for multiplicative inverse. (The superscript
  `⁻¹` is Unicode for "inverse." Lean lets you type it as `\inv` or `\-1`.)
- `Div R` — provides the notation `a / b` for division.

Just as `CommRing` extended the basic operation classes and added axioms, `CField`
extends `CommRing` and adds axioms about inversion and division.

### The field axioms

- `div_eq`: `a / b = a * b⁻¹` — Division is multiplication by the inverse. This
  *defines* division in terms of multiplication and inversion, just as `sub_eq` defined
  subtraction in terms of addition and negation.

- `mul_inv`: `a ≠ 0 → a * a⁻¹ = 1` — Every nonzero element times its inverse is 1.
  Note the `a ≠ 0 →` prefix: this is a conditional axiom. The arrow `→` means
  "implies," so the full reading is "if `a` is not zero, then `a * a⁻¹ = 1`." The
  curly braces around `{a : R}` make `a` implicit.

  The notation `a ≠ 0` in Lean is actually defined as `a = 0 → False`. That is,
  "`a ≠ 0` is not zero" means "assuming `a = 0` leads to a contradiction."

  As with the CommRing axioms, we only need one direction — `inv_mul` (the reverse
  order, `a⁻¹ * a = 1`) is derived via commutativity.

- `inv_zero`: `(0 : R)⁻¹ = 0` — The inverse of zero is defined to be zero.

### The curious choice: `inv_zero`

This last axiom deserves special discussion. In ordinary mathematics, `0⁻¹` (or `1/0`)
is **undefined**. You are told in school that you cannot divide by zero, full stop.

But in Lean (and in type theory more broadly), every function must be **total** — it
must return a value for every input. The inverse function `⁻¹` has type `R → R`. It
takes any element of `R` and returns an element of `R`. There is no way to say "this
function is undefined at 0." It *must* return something.

So what should `0⁻¹` be? We have a few options:

1. Make the function return some arbitrary "junk" value at 0.
2. Change the type so that `⁻¹` only accepts nonzero inputs.
3. Pick a specific convenient value.

Option 2 is used in some formalizations but makes everything more complicated — you
would need to carry around a proof that the denominator is nonzero everywhere you use
division. Option 1 is what Mathlib does (and it also picks 0 as the junk value).
Option 3, which we also use, picks `0⁻¹ = 0` as an explicit axiom.

The choice of `0` is arbitrary but harmless. The axiom `mul_inv` only applies when
`a ≠ 0`, so you can never derive `0 * 0⁻¹ = 1` — that would require `a ≠ 0` with
`a = 0`, which is a contradiction. The value of `0⁻¹` is essentially inert: it exists
because the function must be total, but no important theorem ever depends on its
specific value.

## The CField namespace and derived theorems

```lean
namespace CField

variable {R : Type u} [CField R]
```

Same pattern as before: open a namespace, declare that `R` is a `CField`.

### The inverse of a nonzero element is nonzero

```lean
theorem inv_ne_zero {a : R} (h : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro hinv
  have h1 : a * a⁻¹ = 1 := mul_inv h
  rw [hinv, CommRing.mul_zero] at h1
  exact absurd h1.symm (fun h01 => h (by
    calc a = a * 1 := by rw [CommRing.mul_one]
      _ = a * 0 := by rw [h01]
      _ = 0 := by rw [CommRing.mul_zero]))
```

This is the most complex proof in the file. It says: if `a` is nonzero, then `a⁻¹` is
also nonzero. (The inverse of a nonzero number is nonzero — 5 is nonzero, and so is
1/5.)

The proof is by contradiction (but a *constructive* contradiction — we are not using
LEM). Let's walk through it:

`intro hinv` — Recall that `a⁻¹ ≠ 0` means `a⁻¹ = 0 → False`. The `intro` tactic
takes the antecedent of an implication and moves it into the hypothesis list. So after
`intro hinv`, we have `hinv : a⁻¹ = 0` as a hypothesis, and our goal becomes `False`
(we need to derive a contradiction).

`have h1 : a * a⁻¹ = 1 := mul_inv h` — Since `a ≠ 0` (by hypothesis `h`), we know
`a * a⁻¹ = 1`.

`rw [hinv, CommRing.mul_zero] at h1` — Substitute `a⁻¹ = 0` into `h1`, getting
`a * 0 = 1`. Then apply `mul_zero` to get `0 = 1`. Now `h1 : 0 = 1`.

`exact absurd h1.symm (...)` — The `absurd` function takes two contradictory facts
and produces `False`. Here, `h1.symm` is `1 = 0`, and the second argument shows that
`1 = 0` is absurd. Specifically, if `1 = 0`, then:

- `a = a * 1` (by `mul_one`)
- `a * 1 = a * 0` (replace `1` with `0` using the assumption `1 = 0`)
- `a * 0 = 0` (by `mul_zero`)

So `a = 0`, contradicting the hypothesis `h : a ≠ 0`.

This proof pattern — assume the thing you want to disprove, derive a contradiction —
is the standard way to prove "not" statements in constructive logic.

### Division cancellation

```lean
theorem mul_div_cancel {a : R} (b : R) (h : a ≠ 0) : b / a * a = b := by
  rw [div_eq, CommRing.mul_assoc, inv_mul h, CommRing.mul_one]
```

Dividing by `a` and then multiplying by `a` gives you back what you started with. The
proof expands division as "multiply by inverse," reassociates, uses `a⁻¹ * a = 1`,
and drops the `* 1`.

```lean
theorem div_mul_cancel {a : R} (b : R) (h : a ≠ 0) : a * (b / a) = b := by
  rw [div_eq, CommRing.mul_comm b, ← CommRing.mul_assoc, mul_inv h, CommRing.one_mul]
```

The other direction: multiplying by `a` and then dividing by `a` (or equivalently,
`a *` the quotient `b / a`) gives `b`. The proof rearranges the terms using
commutativity and associativity to put `a` and `a⁻¹` next to each other, cancels them
to `1`, and drops the `1 *`.

Notice that in both theorems, the hypothesis `h : a ≠ 0` is required. You cannot cancel
division by zero — and Lean enforces this by requiring the proof.

### Inverse cancellation

```lean
theorem mul_inv_cancel_left {a b : R} (h : a ≠ 0) : a⁻¹ * (a * b) = b := by
  rw [← CommRing.mul_assoc, inv_mul h, CommRing.one_mul]
```

If you multiply by `a` and then by `a⁻¹`, the `a` cancels. This is the multiplicative
analogue of `neg_add_cancel_left` from the ring section. The proof reassociates to
put `a⁻¹` and `a` next to each other, cancels them to `1`, and drops the `1 *`.

```lean
end CField
```

## Summary: What we built

This file establishes two algebraic structures:

1. **CommRing** — A commutative ring: a type with `+`, `*`, `-`, `0`, `1`, built from
   just 9 axioms (associativity, commutativity, identity, inverse, distributivity, and
   the definition of subtraction). From these axioms, we derived everything else:
   commuted versions (`zero_add`, `one_mul`, etc.), `mul_zero`, `neg_neg`, `neg_zero`,
   `neg_mul_left`, and many additional lemmas about cancellation, subtraction, and
   distribution.

2. **CField** — A (constructive) field: a commutative ring with an additional inverse
   operation `⁻¹` and division `/`, satisfying 3 more axioms. We derived `inv_mul`
   (via commutativity) and theorems about inverse nonzero-ness and division
   cancellation.

None of this mentions infinitesimals, derivatives, or anything specific to SIA. This
is pure algebraic infrastructure — the foundation that everything else builds on. In
the next article, we will add ordering (less-than, greater-than) to our number system,
which will bring us one step closer to the SIA axioms.

### Quick reference: Lean syntax introduced in this article

| Syntax | Meaning |
|--------|---------|
| `universe u` | Declare a universe level variable |
| `Type u` | A type at universe level `u` |
| `class Foo (R : Type u) where` | Define a typeclass with fields/axioms |
| `extends Bar R` | Inherit from another class |
| `∀ (a : R), ...` | "For all `a` of type `R`, ..." |
| `namespace X` ... `end X` | Group definitions under the prefix `X.` |
| `variable {R : Type u}` | Implicit type argument (inferred by Lean) |
| `variable [CommRing R]` | Instance argument (found automatically) |
| `theorem name : statement := by` | Begin a tactic proof |
| `rw [lemma]` | Rewrite using a lemma (left to right) |
| `rw [← lemma]` | Rewrite right to left |
| `rw [...] at h` | Rewrite in hypothesis `h` instead of the goal |
| `calc x = y := by ...` | Chain of equalities |
| `have h : T := ...` | Prove an intermediate fact |
| `intro h` | Assume the antecedent of an implication |
| `exact e` | Provide the proof term directly |
| `.symm` | Flip an equality |
| `@[simp]` | Mark a lemma for the simplifier |
| `attribute [simp]` | Mark existing lemmas for the simplifier |
| `a ≠ 0` | Shorthand for `a = 0 → False` |
| `a⁻¹` | Multiplicative inverse of `a` |
