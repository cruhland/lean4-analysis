import Lean4Axiomatic.Integer.Impl.Difference
import Lean4Axiomatic.Natural.Impl.Nat
import Lean4Axiomatic.Rational
import Lean4Axiomatic.Rational.Impl.Fraction

namespace AnalysisI.Ch4.Sec3

open Lean4Axiomatic
open Lean4Axiomatic.Logic (AP)
open Lean4Axiomatic.Metric (abs dist)
open Lean4Axiomatic.Rational
open Lean4Axiomatic.Signed (Negative Positive sgn)

variable {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Rational (ℤ := ℤ) ℚ]

namespace evaluation

abbrev ℕ' : Type := Nat
abbrev ℤ' : Type := Integer.Impl.Difference ℕ'
abbrev ℚ' : Type := Rational.Impl.Fraction ℤ'

def natural : Natural ℕ' := inferInstance
scoped instance natural_induction_inst : Natural.Induction ℕ' :=
  natural.toInduction
scoped instance natural_induction₁_inst : Natural.Induction.{1} ℕ' :=
  Natural.Impl.Nat.induction
scoped instance integer_induction₁_inst : Integer.Induction.{1} ℤ' :=
  Integer.Impl.Difference.induction
scoped instance rational_inst : Rational (ℤ := ℤ') ℚ' := inferInstance

end evaluation

/-! # 4.3 Absolute value and exponentiation -/

-- Definition 4.3.1 (Absolute value).
-- If `x` is a rational number, the _absolute value_ `abs x` of `x` is defined
-- as follows.
-- [Rational axiom for absolute value]
example : ℚ → ℚ := Rational.Metric.toOps._abs

-- If `x` is positive, then `abs x := x`.
example {x : ℚ} : Positive x → abs x ≃ x := by
  intro (_ : Positive x)
  show abs x ≃ x
  have : sgn x ≃ 1 := sgn_positive.mp ‹Positive x›
  have : abs x ≃ x := abs_positive this
  exact this

-- If `x` is negative, then `abs x := -x`.
example {x : ℚ} : Negative x → abs x ≃ -x := by
  intro (_ : Negative x)
  show abs x ≃ -x
  have : sgn x ≃ -1 := sgn_negative.mp ‹Negative x›
  have : abs x ≃ -x := abs_negative this
  exact this

-- If `x` is zero, then `abs x := 0`.
example {x : ℚ} : x ≃ 0 → abs x ≃ 0 := abs_zero.mpr

-- Definition 4.3.2 (Distance).
-- Let `x` and `y` be rational numbers. The quantity `abs (x - y)` is called
-- the _distance between `x` and `y`_ and is sometimes denoted `dist x y`, thus
-- `dist x y := abs (x - y)`.
-- [Rational axiom for distance].
example : ℚ → ℚ → ℚ := Rational.Metric.toOps._dist

example {x y : ℚ} : dist x y ≃ abs (x - y) := dist_abs

namespace evaluation

-- For instance, `dist 3 5 ≃ 2`.
example : dist (3 : ℚ') 5 ≃ 2 := rfl
/-
Showing steps with `calc` is causing problems, using comments for now
    dist 3 5
  ≃ abs (3 - 5)
  ≃ abs (-2)
  ≃ 2
-/

end evaluation

section prop_4_3_3
-- Exercise 4.3.1.
-- Proposition 4.3.3 (Basic properties of absolute value and distance).
-- Let `x`, `y`, `z` be rational numbers.
variable {x y z : ℚ}

-- (a) (Non-degeneracy of absolute value)
-- We have `abs x ≥ 0`. Also, `abs x ≃ 0` if and only if `x` is `0`.

-- [Wikipedia calls this "non-negativity".]
example : abs x ≥ 0 := Rational.abs_nonneg

-- [Wikipedia calls this "positive-definiteness".]
example : abs x ≃ 0 ↔ x ≃ 0 := Rational.abs_zero

-- (b) (Triangle inequality for absolute value) We have
example : abs (x + y) ≤ abs x + abs y := Rational.abs_compat_add

-- (c) We have the inequalities `-y ≤ x ≤ y` if and only if `y ≥ abs x`.
example : -y ≤ x ∧ x ≤ y ↔ y ≥ abs x := Rational.abs_upper_bound.symm

-- In particular, we have
example : -(abs x) ≤ x ∧ x ≤ abs x := abs_upper_bound.mp le_refl

-- (d) (Multiplicativity of absolute value) We have
example : abs (x * y) ≃ abs x * abs y := Rational.abs_compat_mul

-- In particular,
example : abs (-x) ≃ abs x := Rational.abs_absorb_neg

-- (e) (Non-degeneracy of distance) We have
example : dist x y ≥ 0 := Rational.dist_nonneg

-- Also,
example : dist x y ≃ 0 ↔ x ≃ y := Rational.dist_zero

-- (f) (Symmetry of distance)
example : dist x y ≃ dist y x := Rational.dist_comm

-- (g) (Triangle inequality for distance)
example : dist x z ≤ dist x y + dist y z := Rational.dist_triangle

end prop_4_3_3

-- Definition 4.3.4 (`ε`-closeness).
-- Let `ε > 0` be a rational number, and let `x`, `y` be rational numbers. We
-- say that `y` is _`ε`-close_ to `x` iff we have `dist y x ≤ ε`.
-- [Rational axiom for `ε`-closeness]
example : ℚ → ℚ → ℚ → Prop := Rational.Metric.toOps._close

-- [The syntax `y ⊢ε⊣ x` for "`y` is `ε`-close to `x`" is easier to support
-- with Lean's `notation` macro than my first attempt of `y ε-close x`.]
example {ε x y : ℚ} : y ⊢ε⊣ x ↔ dist y x ≤ ε := Rational.close_dist

namespace evaluation

-- Examples 4.3.6.
-- The numbers `0.99` and `1.01` are `0.1`-close,
example : (0.99 : ℚ') ⊢0.1⊣ 1.01 := by
  have : sgn ((0.02 : ℚ') - 0.1) ≃ -1 := rfl
  have : sgn ((0.02 : ℚ') - 0.1) ≄ 1 :=
    AA.neqv_substL (Rel.symm this) Integer.neg_one_neqv_one
  have : dist (0.99 : ℚ') 1.01 ≤ 0.1 := calc
    _ ≃ dist (0.99 : ℚ') 1.01 := eqv_refl
 -- _ ≃ abs (0.99 - 1.01)     := dist_abs -- [causes max recursion error]
 -- _ ≃ abs (-0.02)
    _ ≃ 0.02                  := rfl
    _ ≤ 0.1                   := le_sgn.mpr this
  have : (0.99 : ℚ') ⊢0.1⊣ 1.01 := close_dist.mpr this
  exact this

-- but they are not `0.01`-close, because
example : ¬((0.99 : ℚ') ⊢0.01⊣ 1.01) := by
  intro (_ : (0.99 : ℚ') ⊢0.01⊣ 1.01)
  show False
  have : (0.02 : ℚ') ≤ 0.01 := calc
    _ ≃ (0.02 : ℚ')           := eqv_refl
    _ ≃ dist (0.99 : ℚ') 1.01 := rfl
    _ ≤ 0.01                  := close_dist.mp ‹(0.99 : ℚ') ⊢0.01⊣ 1.01›
  have notOne : sgn ((0.02 : ℚ') - 0.01) ≄ 1 := le_sgn.mp this
  have one : sgn ((0.02 : ℚ') - 0.01) ≃ 1 := rfl
  exact absurd one notOne

-- The numbers `2` and `2` are `ε`-close for every positive `ε`.
example {ε : ℚ'} : ε > 0 → (2 : ℚ') ⊢ε⊣ 2 := by
  intro (_ : ε > 0)
  show (2 : ℚ') ⊢ε⊣ 2
  have : dist (2 : ℚ') 2 ≤ ε := calc
    _ ≃ dist (2 : ℚ') 2 := eqv_refl
    _ ≃ 0               := dist_zero.mpr eqv_refl
    _ ≤ ε               := le_cases.mpr (Or.inl ‹0 < ε›)
  have : (2 : ℚ') ⊢ε⊣ 2 := close_dist.mpr this
  exact this

end evaluation

-- We do not bother defining a notion of `ε`-close when `ε` is zero or
-- negative, because if `ε` is zero then `x` and `y` are only `ε`-close when
-- they are equal, and when `ε` is negative then `x` and `y` are never
-- `ε`-close.
-- [It seems better to define it in those cases for completeness, though.]
example {x y : ℚ} : x ⊢0⊣ y ↔ x ≃ y := close_zero

example {ε x y : ℚ} : ε < 0 → ¬(x ⊢ε⊣ y) := by
  intro (_ : ε < 0) (_ : x ⊢ε⊣ y)
  show False
  have : ε ≥ 0 := close_nonneg ‹x ⊢ε⊣ y›
  have : False := le_gt_false ‹0 ≤ ε› ‹0 > ε›
  exact this

section prop_4_3_7

-- Exercise 4.3.2.
-- Proposition 4.3.7.
-- Let `x`, `y`, `z`, `w` be rational numbers.
variable {x y z w : ℚ}

-- (a) If `x ≃ y`, then `x` is `ε`-close to `y` for every `ε > 0`. Conversely,
-- if `x` is `ε`-close to `y` for every `ε > 0`, then we have `x ≃ y`.
example : x ≃ y ↔ {ε : ℚ} → ε > 0 → x ⊢ε⊣ y := close_eqv.symm

-- (b) Let `ε > 0`. If `x` is `ε`-close to `y`, then `y` is `ε`-close to `x`.
example {ε : ℚ} : ε > 0 → x ⊢ε⊣ y → y ⊢ε⊣ x := λ (_ : ε > 0) => close_symm

-- (c) Let `ε,δ > 0`. If `x` is `ε`-close to `y`, and `y` is `δ`-close to `z`,
-- then `x` and `z` are `(ε + δ)`-close.
example {ε δ : ℚ} : ε > 0 → δ > 0 → x ⊢ε⊣ y → y ⊢δ⊣ z → x ⊢ε+δ⊣ z :=
  λ (_ : ε > 0) (_ : δ > 0) => close_trans

-- (d) Let `ε,δ > 0`. If `x` and `y` are `ε`-close, and `z` and `w` are
-- `δ`-close, then `x + z` and `y + w` are `(ε + δ)`-close, and `x - z` and
-- `y - w` are also `(ε + δ)`-close.
example {ε δ : ℚ} : ε > 0 → δ > 0 → x ⊢ε⊣ y → z ⊢δ⊣ w → x + z ⊢ε+δ⊣ y + w :=
  λ (_ : ε > 0) (_ : δ > 0) => close_add_pointwise

example {ε δ : ℚ} : ε > 0 → δ > 0 → x ⊢ε⊣ y → z ⊢δ⊣ w → x - z ⊢ε+δ⊣ y - w :=
  λ (_ : ε > 0) (_ : δ > 0) => close_sub_pointwise

-- (e) Let `ε > 0`. If `x` and `y` are `ε`-close, they are also `ε'`-close for
-- every `ε' > ε`.
example {ε ε' : ℚ} : ε > 0 → x ⊢ε⊣ y → ε' > ε → x ⊢ε'⊣ y :=
  λ (_ : ε > 0) => close_widen

-- (f) Let `ε > 0`. If `y` and `z` are both `ε`-close to `x`, and `w` is
-- between `y` and `z` (i.e., `y ≤ w ≤ z` or `z ≤ w ≤ y`), then `w` is also
-- `ε`-close to `x`.
example
    {ε : ℚ} : ε > 0 → y ⊢ε⊣ x → z ⊢ε⊣ x →
    y ≤ w ∧ w ≤ z ∨ z ≤ w ∧ w ≤ y → w ⊢ε⊣ x
    := by
  intro (_ : ε > 0) (_ : y ⊢ε⊣ x) (_ : z ⊢ε⊣ x)
  intro (_ : y ≤ w ∧ w ≤ z ∨ z ≤ w ∧ w ≤ y)
  show w ⊢ε⊣ x
  have : x ⊢ε⊣ y := close_symm ‹y ⊢ε⊣ x›
  have : x ⊢ε⊣ z := close_symm ‹z ⊢ε⊣ x›
  have : y⊣ w ⊢z := between_order.mpr ‹y ≤ w ∧ w ≤ z ∨ z ≤ w ∧ w ≤ y›
  have : x ⊢ε⊣ w := between_preserves_close ‹x ⊢ε⊣ y› ‹x ⊢ε⊣ z› ‹y⊣ w ⊢z›
  have : w ⊢ε⊣ x := close_symm this
  exact this

-- (g) Let `ε > 0`. If `x` and `y` are `ε`-close, and `z` is non-zero, then
-- `x * z` and `y * z` are `ε * abs z`-close.
example {ε : ℚ} : ε > 0 → x ⊢ε⊣ y → z ≄ 0 → x * z ⊢ε * abs z⊣ y * z := by
  intro (_ : ε > 0) (_ : x ⊢ε⊣ y) (_ : z ≄ 0)
  show x * z ⊢ε * abs z⊣ y * z
  exact close_substL_mul ‹x ⊢ε⊣ y›

-- (h) Let `ε,δ > 0`. If `x` and `y` are `ε`-close, and `z` and `w` are
-- `δ`-close, then `x * z` and `y * w` are
-- `(ε * abs z + δ * abs x + ε * δ)`-close.
example
    {ε δ : ℚ} : ε > 0 → δ > 0 → x ⊢ε⊣ y → z ⊢δ⊣ w →
    x * z ⊢ε * abs z + δ * abs x + ε * δ⊣ y * w
    :=
  λ (_ : ε > 0) (_ : δ > 0) => close_mul_pointwise

end prop_4_3_7

-- Definition 4.3.9 (Exponentiation to a natural number).
-- Let `x` be a rational number. To raise `x` to the power `0`, we define
-- `x^0 := 1`;
example {x : ℚ} : x^(0:ℕ) ≃ 1 := Natural.pow_zero

-- in particular we define `0^0 := 1`.
example : (0:ℚ)^(0:ℕ) ≃ 1 := Natural.pow_zero

-- Now suppose inductively that `x^n` has been defined for some natural number
-- `n`, then we define `x^(n+1) := x^n * x`.
example {x : ℚ} {n : ℕ} : x^(n+1) ≃ x^n * x := calc
  _ ≃ x^(n+1)            := eqv_refl
  _ ≃ x^(Natural.step n) := Natural.pow_substR Natural.add_one_step
  _ ≃ x^n * x            := Natural.pow_step

section prop_4_3_10

-- Exercise 4.3.3.
-- Proposition 4.3.10 (Properties of exponentiation, I).
-- Let `x`, `y` be rational numbers, and let `n`, `m` be natural numbers.
variable {x y : ℚ} {n m : ℕ}

-- (a) We have `x^n * x^m ≃ x^(n+m)`,
example : x^n * x^m ≃ x^(n+m) := eqv_symm Natural.pow_compatL_add

-- `(x^n)^m ≃ x^(n*m)`,
example : (x^n)^m ≃ x^(n*m) := Natural.pow_flatten

-- and `(x*y)^n ≃ x^n * y^n`.
example : (x*y)^n ≃ x^n * y^n := Natural.pow_distribR_mul (mul := (· * ·))

-- (b) Suppose `n > 0`. Then we have `x^n ≃ 0` if and only if `x ≃ 0`.
example : n > 0 → (x^n ≃ 0 ↔ x ≃ 0) := by
  intro (_ : n > 0)
  show x^n ≃ 0 ↔ x ≃ 0
  apply Iff.intro
  case mp =>
    intro (_ : x^n ≃ 0)
    show x ≃ 0
    have (And.intro (_ : x ≃ 0) _) :=
      Natural.pow_inputs_for_output_zero ‹x^n ≃ 0›
    exact ‹x ≃ 0›
  case mpr =>
    intro (_ : x ≃ 0)
    show x^n ≃ 0
    have : Positive n := Natural.lt_zero_pos.mpr ‹n > 0›
    have : n ≄ 0 := Signed.positive_defn.mp this
    have : x ≃ 0 ∧ n ≄ 0 := And.intro ‹x ≃ 0› ‹n ≄ 0›
    have : x^n ≃ 0 := Natural.pow_eqv_zero.mpr this
    exact this

-- (c) If `x ≥ y ≥ 0`, then `x^n ≥ y^n ≥ 0`.
example : x ≥ y ∧ y ≥ 0 → x^n ≥ y^n ∧ y^n ≥ 0 := pow_substL_ge_nonneg

-- If `x > y ≥ 0` and `n > 0`, then `x^n > y^n ≥ 0`.
example : x > y ∧ y ≥ 0 ∧ n > 0 → x^n > y^n ∧ y^n ≥ 0 := by
  intro (And.intro (_ : x > y) (And.intro (_ : y ≥ 0) (_ : n > 0)))
  show x^n > y^n ∧ y^n ≥ 0
  have : x > y ∧ y ≥ 0 := And.intro ‹x > y› ‹y ≥ 0›
  have : x^n > y^n ∧ y^n ≥ 0 := pow_pos_substL_gt_nonneg ‹n > 0› this
  exact this

-- (d) We have `abs (x^n) ≃ (abs x)^n`.
example : abs (x^n) ≃ (abs x)^n := pow_scompatL_abs

end prop_4_3_10

-- Definition 4.3.11 (Exponentiation to a negative number).
-- Let `x` be a non-zero rational number. Then for any negative integer `-n`,
-- we define `x^(-n) := 1/x^n`.
example {x : ℚ} [AP (x ≄ 0)] {n : ℕ} : x^(-(n:ℤ)) ≃ 1/x^n := pow_neg

namespace evaluation

-- Thus for instance
example {x : ℚ'} [AP (x ≄ 0)] : x^(-3:ℤ') ≃ 1/(x * x * x) := calc
  _ = x^(-3:ℤ')            := rfl
  _ ≃ 1/x^(3:ℕ')           := pow_neg
  _ ≃ 1/(x^(2:ℕ') * x)     := div_substR Natural.pow_step
  _ ≃ 1/(x^(1:ℕ') * x * x) := div_substR (AA.substL Natural.pow_step)
  _ ≃ 1/(x * x * x)        := div_substR (AA.substL (AA.substL Natural.pow_one))

end evaluation

section prop_4_3_12

-- Exercise 4.3.4.
-- Proposition 4.3.12 (Properties of exponentiation, II).
-- Let `x`, `y` be nonzero rational numbers, and let `n`, `m` be integers.
variable {x y : ℚ} [AP (x ≄ 0)] [AP (y ≄ 0)] {n m : ℤ}

-- (a) We have `x^n * x^m ≃ x^(n+m)`,
example : x^n * x^m ≃ x^(n + m) := eqv_symm pow_compatL_add

-- `(x^n)^m ≃ x^(n * m)`,
example : (x^n)^m ≃ x^(n * m) := pow_flatten

end prop_4_3_12

end AnalysisI.Ch4.Sec3
