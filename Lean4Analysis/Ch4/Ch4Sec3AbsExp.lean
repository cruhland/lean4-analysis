import Lean4Axiomatic.Rational

namespace AnalysisI.Ch4.Sec3

open Lean4Axiomatic
open Lean4Axiomatic.Metric (abs)
open Lean4Axiomatic.Rational
open Lean4Axiomatic.Signed (Negative Positive sgn)

variable {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Rational (ℤ := ℤ) ℚ]

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

end AnalysisI.Ch4.Sec3
