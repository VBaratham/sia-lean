/-
  SIA.Derivative — Derivatives via microaffinity

  Defines the derivative f'(x) as the unique slope from microaffinity,
  then proves the standard derivative rules: sum, product, chain, constant, identity.

  IMPORTANT: We avoid Exists.choose (which uses Classical.choice) by never
  extracting the witness. Instead, all derivative rules are proved by showing
  that a candidate satisfies the microaffinity condition, then using uniqueness.
-/
import SIA.Delta

universe u

namespace SIA

variable {R : Type u} [SIA R]
open CommRing StrictOrder

-- Instead of defining deriv via Exists.choose (which is classical),
-- we prove derivative rules directly from microaffinity + uniqueness.
-- The key technique: to show (f+g)' = f' + g', we show that if
-- a satisfies ∀d, f(x+d) = f(x) + a*d and b satisfies ∀d, g(x+d) = g(x) + b*d,
-- then a+b satisfies ∀d, (f+g)(x+d) = (f+g)(x) + (a+b)*d.
-- By uniqueness, the slope for f+g must equal a+b.

-- Constant function: slope is 0
theorem deriv_const_slope (c : R) (x : R) :
    ∀ (d : Delta R), (fun _ => c) (x + d.val) = (fun _ => c) x + 0 * d.val := by
  intro d; rw [zero_mul, add_zero]

-- Identity: slope is 1
theorem deriv_id_slope (x : R) :
    ∀ (d : Delta R), id (x + d.val) = id x + 1 * d.val := by
  intro d; simp [id, one_mul]

-- Sum rule: if f has slope a and g has slope b, then f+g has slope a+b
theorem deriv_add_slope (f g : R → R) (x a b : R)
    (ha : ∀ (d : Delta R), f (x + d.val) = f x + a * d.val)
    (hb : ∀ (d : Delta R), g (x + d.val) = g x + b * d.val) :
    ∀ (d : Delta R), (f (x + d.val) + g (x + d.val)) = (f x + g x) + (a + b) * d.val := by
  intro d
  rw [ha d, hb d, right_distrib]
  rw [add_assoc, ← add_assoc (a * d.val), add_comm (a * d.val) (g x),
      add_assoc, add_assoc]

-- Negation rule: if f has slope a, then -f has slope -a
theorem deriv_neg_slope (f : R → R) (x a : R)
    (ha : ∀ (d : Delta R), f (x + d.val) = f x + a * d.val) :
    ∀ (d : Delta R), (-(f (x + d.val))) = (-(f x)) + (-a) * d.val := by
  intro d
  rw [ha d, neg_add_distrib, neg_mul_left]

-- Scalar multiplication: if f has slope a, then c*f has slope c*a
theorem deriv_const_mul_slope (c : R) (f : R → R) (x a : R)
    (ha : ∀ (d : Delta R), f (x + d.val) = f x + a * d.val) :
    ∀ (d : Delta R), (c * f (x + d.val)) = (c * f x) + (c * a) * d.val := by
  intro d
  rw [ha d, left_distrib, mul_assoc]

-- Product rule: if f has slope a and g has slope b, then f*g has slope a*g(x) + f(x)*b
theorem deriv_mul_slope (f g : R → R) (x a b : R)
    (ha : ∀ (d : Delta R), f (x + d.val) = f x + a * d.val)
    (hb : ∀ (d : Delta R), g (x + d.val) = g x + b * d.val) :
    ∀ (d : Delta R), (f (x + d.val) * g (x + d.val)) =
      (f x * g x) + (a * g x + f x * b) * d.val := by
  intro d
  rw [ha d, hb d]
  rw [left_distrib, right_distrib, right_distrib]
  -- last term: (a*d)*(b*d) = a*b*d² = 0
  have last_zero : (a * d.val) * (b * d.val) = 0 := by
    calc (a * d.val) * (b * d.val)
        = a * (d.val * (b * d.val)) := by rw [mul_assoc]
      _ = a * ((d.val * b) * d.val) := by rw [mul_assoc d.val]
      _ = a * ((b * d.val) * d.val) := by rw [mul_comm d.val b]
      _ = a * (b * (d.val * d.val)) := by rw [mul_assoc b]
      _ = a * (b * 0) := by rw [d.property]
      _ = 0 := by rw [mul_zero, mul_zero]
  rw [last_zero, add_zero]
  rw [right_distrib]
  -- Goal shape: fxgx + fx(bd) + (ad)gx + 0 = fxgx + (agx*d + fxb*d)
  -- After rw [add_assoc]:
  --   fxgx + (fx(bd) + (ad)gx) = fxgx + (agx*d + fxb*d)
  rw [add_assoc]; congr 1
  -- (a*d)*gx + fx*(b*d) = a*gx*d + fx*b*d
  calc a * d.val * g x + f x * (b * d.val)
      = a * (d.val * g x) + f x * (b * d.val) := by rw [mul_assoc a]
    _ = a * (g x * d.val) + f x * (b * d.val) := by rw [mul_comm d.val (g x)]
    _ = (a * g x) * d.val + f x * (b * d.val) := by rw [← mul_assoc a]
    _ = (a * g x) * d.val + (f x * b) * d.val := by rw [← mul_assoc (f x)]

-- Chain rule: if g has slope b at x, and f has slope a at g(x),
-- then f∘g has slope a*b at x
theorem deriv_comp_slope (f g : R → R) (x a b : R)
    (ha : ∀ (d : Delta R), f (g x + d.val) = f (g x) + a * d.val)
    (hb : ∀ (d : Delta R), g (x + d.val) = g x + b * d.val) :
    ∀ (d : Delta R), f (g (x + d.val)) = f (g x) + (a * b) * d.val := by
  intro d
  -- g(x+d) = g(x) + b*d, and b*d ∈ Delta
  have gd_sq : (b * d.val) * (b * d.val) = 0 := by
    calc (b * d.val) * (b * d.val)
        = b * (d.val * (b * d.val)) := by rw [mul_assoc]
      _ = b * ((d.val * b) * d.val) := by rw [mul_assoc d.val]
      _ = b * ((b * d.val) * d.val) := by rw [mul_comm d.val b]
      _ = b * (b * (d.val * d.val)) := by rw [mul_assoc b]
      _ = b * (b * 0) := by rw [d.property]
      _ = 0 := by rw [mul_zero, mul_zero]
  let gd : Delta R := ⟨b * d.val, gd_sq⟩
  rw [hb d, ha gd, mul_assoc]

-- Now the "user-facing" derivative rules using ExistsUnique directly.
-- These state: if the microaffinity slope for (combined function) exists and is unique,
-- then it equals the expected combination of slopes.

-- The derivative of f+g equals f' + g'
theorem deriv_add_eq (f g : R → R) (x : R) :
    ∀ (af ag afg : R),
    (∀ (d : Delta R), f (x + d.val) = f x + af * d.val) →
    (∀ (d : Delta R), g (x + d.val) = g x + ag * d.val) →
    (∀ (d : Delta R), (f (x + d.val) + g (x + d.val)) = (f x + g x) + afg * d.val) →
    afg = af + ag := by
  intro af ag afg hf hg hfg
  have hab := deriv_add_slope f g x af ag hf hg
  exact (microaffinity (fun t => f t + g t) x).unique hfg hab

-- The derivative of f*g equals f'*g + f*g'
theorem deriv_mul_eq (f g : R → R) (x : R) :
    ∀ (af ag afg : R),
    (∀ (d : Delta R), f (x + d.val) = f x + af * d.val) →
    (∀ (d : Delta R), g (x + d.val) = g x + ag * d.val) →
    (∀ (d : Delta R), (f (x + d.val) * g (x + d.val)) = (f x * g x) + afg * d.val) →
    afg = af * g x + f x * ag := by
  intro af ag afg hf hg hfg
  have hab := deriv_mul_slope f g x af ag hf hg
  exact (microaffinity (fun t => f t * g t) x).unique hfg hab

-- The derivative of f∘g equals f'(g(x)) * g'(x)
theorem deriv_comp_eq (f g : R → R) (x : R) :
    ∀ (af ag afg : R),
    (∀ (d : Delta R), f (g x + d.val) = f (g x) + af * d.val) →
    (∀ (d : Delta R), g (x + d.val) = g x + ag * d.val) →
    (∀ (d : Delta R), f (g (x + d.val)) = f (g x) + afg * d.val) →
    afg = af * ag := by
  intro af ag afg hf hg hfg
  have hab := deriv_comp_slope f g x af ag hf hg
  exact (microaffinity (fun t => f (g t)) x).unique hfg hab

end SIA
