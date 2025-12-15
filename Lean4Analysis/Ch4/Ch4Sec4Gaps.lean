import Lean4Axiomatic.Rational

namespace AnalysisI.Ch4.Sec4

open Lean4Axiomatic (Integer Natural Rational)
open Lean4Axiomatic.Rational
open Lean4Axiomatic.Relation.Equivalence (Unique)

/-! # 4.4 Gaps in the rational numbers -/

variable {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Rational (ℤ := ℤ) ℚ]

/--
**Proposition 4.4.1** (Interspersing of integers by rationals).
Let `x` be a rational number. Then there exists an integer `n` such that
`n ≤ x < n + 1`.
-/
example {x : ℚ} : ∃ n : ℤ, n ≤ x ∧ x < n + 1 :=
  Exists.intro (floor x) floor_bounds

/--
In fact, this integer is unique (i.e., for each `x` there is only one `n` for
which `n ≤ x < n + 1`).
-/
example {x : ℚ} : Unique (λ n : ℤ => n ≤ x ∧ x < n + 1) :=
  have lt_impossible
      {a b : ℤ} : a < b → a ≤ x ∧ x < a + 1 → b ≤ x ∧ x < b + 1 → False
      := by
    intro (_ : a < b) (And.intro _ (_ : x < a + 1)) (And.intro (_ : b ≤ x) _)
    show False

    have : (b:ℚ) < ((a + 1 : ℤ):ℚ) := calc
      _ = (b:ℚ)           := rfl
      _ ≤ x               := ‹b ≤ x›
      _ < (a:ℚ) + 1       := ‹x < a + 1›
      _ ≃ ((a + 1 : ℤ):ℚ) := eqv_symm add_compat_from_integer
    have : b < a + 1 := lt_respects_from_integer.mpr ‹(b:ℚ) < ((a + 1 : ℤ):ℚ)›
    have : b ≤ a := Integer.le_iff_lt_incR.mpr ‹b < a + 1›

    exact Integer.lt_ge_false ‹a < b› ‹a ≥ b›

  have atMostOne
      {n₁ n₂ : ℤ}
      : n₁ ≤ x ∧ x < n₁ + 1 → n₂ ≤ x ∧ x < n₂ + 1 → n₁ ≃ n₂
      := by
    intro (bounds₁ : n₁ ≤ x ∧ x < n₁ + 1) (bounds₂ : n₂ ≤ x ∧ x < n₂ + 1)
    show n₁ ≃ n₂

    match (Integer.order_trichotomy n₁ n₂).atLeastOne with
    | .first (_ : n₁ < n₂) =>
      exact (lt_impossible ‹n₁ < n₂› bounds₁ bounds₂).elim
    | .second (_ : n₁ ≃ n₂) =>
      exact ‹n₁ ≃ n₂›
    | .third (_ : n₁ > n₂) =>
      exact (lt_impossible ‹n₂ < n₁› bounds₂ bounds₁).elim

  show Unique (λ n : ℤ => n ≤ x ∧ x < n + 1) from {
    val := floor x
    atLeastOne := floor_bounds
    atMostOne := atMostOne
  }

end AnalysisI.Ch4.Sec4
