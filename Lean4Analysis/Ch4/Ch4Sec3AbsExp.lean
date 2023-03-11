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
  have : (sgn x : ℚ) ≃ 1 := from_integer_subst (sgn_positive.mp ‹Positive x›)
  have : abs x ≃ x := calc
    abs x     ≃ _ := abs_sgn
    x * sgn x ≃ _ := mul_substR ‹(sgn x : ℚ) ≃ 1›
    x * 1     ≃ _ := mul_identR
    x         ≃ _ := eqv_refl
  exact this

-- If `x` is negative, then `abs x := -x`.
example {x : ℚ} : Negative x → abs x ≃ -x := by
  intro (_ : Negative x)
  show abs x ≃ -x
  have : (sgn x : ℚ) ≃ -1 := calc
    (sgn x : ℚ)    ≃ _ := from_integer_subst (sgn_negative.mp ‹Negative x›)
    ((-1 : ℤ) : ℚ) ≃ _ := neg_compat_from_integer
    (-1 : ℚ)       ≃ _ := eqv_refl
  have : abs x ≃ -x := calc
    abs x     ≃ _ := abs_sgn
    x * sgn x ≃ _ := mul_substR ‹(sgn x : ℚ) ≃ -1›
    x * -1    ≃ _ := mul_comm
    (-1) * x  ≃ _ := mul_neg_one
    (-x)      ≃ _ := eqv_refl
  exact this

-- If `x` is zero, then `abs x := 0`.
example {x : ℚ} : x ≃ 0 → abs x ≃ 0 := by
  intro (_ : x ≃ 0)
  show abs x ≃ 0
  calc
    abs x           ≃ _ := abs_sgn
    x * sgn x       ≃ _ := mul_substL ‹x ≃ 0›
    (0 * sgn x : ℚ) ≃ _ := mul_absorbL
    0               ≃ _ := eqv_refl

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

end AnalysisI.Ch4.Sec3
