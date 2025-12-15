import Lean4Axiomatic.Rational

namespace AnalysisI.Ch4.Sec4

open Lean4Axiomatic (Integer Natural Rational)

/-! # 4.4 Gaps in the rational numbers -/

variable {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Rational (ℤ := ℤ) ℚ]

/--
**Proposition 4.4.1** (Interspersing of integers by rationals).
Let `x` be a rational number. Then there exists an integer `n` such that
`n ≤ x < n + 1`.
-/
example {x : ℚ} : ∃ n : ℤ, n ≤ x ∧ x < n + 1 := Rational.between_integers

end AnalysisI.Ch4.Sec4
