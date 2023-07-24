import Lean4Axiomatic.Integer.Impl.Difference
import Lean4Axiomatic.Natural.Impl.Nat
import Lean4Axiomatic.Rational
import Lean4Axiomatic.Rational.Impl.Fraction

namespace AnalysisI.Ch4.Sec3

open Lean4Axiomatic
open Lean4Axiomatic.Metric (abs dist)
open Lean4Axiomatic.Rational
open Lean4Axiomatic.Signed (Negative Positive sgn)

variable {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Rational (ℤ := ℤ) ℚ]

section evaluation

abbrev ℕ' : Type := Nat
abbrev ℤ' : Type := Integer.Impl.Difference ℕ'
abbrev ℚ' : Type := Rational.Impl.Fraction ℤ'

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

section evaluation

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
example : abs x ≥ 0 := Rational.abs_ge_zero

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
example : dist x y ≥ 0 := Rational.dist_ge_zero

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

section evaluation

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

example {ε x y : ℚ} : sgn ε ≃ -1 → ¬(x ⊢ε⊣ y) := by
  intro (_ : sgn ε ≃ -1) (_ : x ⊢ε⊣ y)
  show False
  have : x ⊢ε⊣ y ∧ sgn ε ≃ -1 := And.intro ‹x ⊢ε⊣ y› ‹sgn ε ≃ -1›
  exact close_negative this

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

end AnalysisI.Ch4.Sec3
