import Lean4Axiomatic.Rational

namespace AnalysisI.Ch4.Sec4

open Lean4Axiomatic -- to use Rel namespace
open Lean4Axiomatic.Rational
open Lean4Axiomatic.Relation.Equivalence (Unique)

/-! # 4.4 Gaps in the rational numbers -/

variable {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Rational (ℤ := ℤ) ℚ]

-- Exercise 4.4.1.
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

/--
In particular, there exists a natural number `N` such that `N > x` (i.e., there
is no such thing as a rational number which is larger than all the natural
numbers).
-/
example {x : ℚ} : ∃ N : ℕ, N > x :=
  have : Decidable (x ≥ 0) := le_decidable
  match this with
  | .isTrue (_ : x ≥ 0) =>
    have : floor x + 1 > 0 := calc
      _ = floor x + 1 := rfl
      _ > floor x     := Integer.lt_inc
      _ ≥ 0           := floor_lb ‹x ≥ 0›
    have (Subtype.mk (n : ℕ) (And.intro (_ : floor x + 1 ≃ n) _)) :=
      Integer.pos_to_natural ‹floor x + 1 > 0›
    have (And.intro _ (_ : x < floor x + 1)) := floor_bounds
    have : (n:ℚ) > x := calc
      _ = (n:ℚ)                 := rfl
      _ ≃ ((floor x + 1 : ℤ):ℚ) := by srw [←‹floor x + 1 ≃ n›]
      _ ≃ (floor x : ℚ) + 1     := add_compat_from_integer
      _ > x                     := ‹x < floor x + 1›
    Exists.intro n ‹n > x›
  | .isFalse (_ : ¬(x ≥ 0)) =>
    have : x < 0 := not_ge_iff_lt.mp ‹¬(x ≥ 0)›
    Exists.intro 0 ‹0 > x›

end AnalysisI.Ch4.Sec4
