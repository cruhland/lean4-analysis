import Lean4Axiomatic.Rational

namespace AnalysisI.Ch4.Sec4

open Lean4Axiomatic -- to use Rel namespace
open Lean4Axiomatic.Logic (AP)
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

/--
**Remark 4.4.2.**
The integer `n` for which `n ≤ x < n + 1` is sometimes referred to as the
_integer part_ of `x` and is sometimes denoted `n = ⌊x⌋`.
[note: in this project we denote it with the `floor` function]
-/
example {x : ℚ} : floor x ≤ x ∧ x < floor x + 1 := floor_bounds

/--
**Proposition 4.4.3** (Interspersing of rationals by rationals).
If `x` and `y` are two rationals such that `x < y`, then there exists a third
rational `z` such that `x < z < y`.
-/
example {x y : ℚ} : x < y → ∃ z : ℚ, x < z ∧ z < y := by
  intro (_ : x < y)
  show ∃ z : ℚ, x < z ∧ z < y
  exact Exists.intro ((x + y)/2) (average ‹x < y›)

/--
**Proposition 4.4.4.**
There does not exist any rational number `x` for which `x^2 ≃ 2`.
-/
example : ¬∃ x : ℚ, x^(2:ℕ) ≃ 2 := by
  intro (Exists.intro (x : ℚ) (_ : x^(2:ℕ) ≃ 2))
  show False

  have : x^(2:ℕ) ≄ 2 := sqrt2_irrational
  have : False := absurd ‹x^(2:ℕ) ≃ 2› ‹x^(2:ℕ) ≄ 2›
  exact this

/--
**Proposition 4.4.5.**
For every rational number `ε > 0`, there exists a non-negative rational number
`x` such that `x^2 < 2 < (x + ε)^2`.

[Note: we can only prove the double-negation of this statement constructively,
when using Tao's approach in the book.]
-/
example {ε : ℚ}
    : ε > 0 → ¬¬∃ x : ℚ, x ≥ 0 ∧ x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ)
    := by
  intro (_ : ε > 0) (_ : ¬∃ x : ℚ, x ≥ 0 ∧ x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ))
  show False

  have boundsFn : (x : ℚ) → ¬(x ≥ 0 ∧ x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ)) :=
    sorry
  have : (x : ℚ) → x ≥ 0 → x^(2:ℕ) < 2 → (x + ε)^(2:ℕ) < 2 := sorry
  have : ¬((0:ℚ) ≥ 0 ∧ (0:ℚ)^(2:ℕ) < 2 ∧ 2 < (0 + ε)^(2:ℕ)) := boundsFn 0
  have : ¬((0:ℚ) ≥ 0 ∧ (0:ℚ)^(2:ℕ) < 2) ∨ ¬(2 < (0 + ε)^(2:ℕ)) := sorry
  have : (¬((0:ℚ) ≥ 0)) ∨ (¬((0:ℚ)^(2:ℕ) < 2)) ∨ (¬(2 < (0 + ε)^(2:ℕ))) := sorry
  have : False := match ‹(¬((0:ℚ) ≥ 0)) ∨ (¬((0:ℚ)^(2:ℕ) < 2)) ∨ (¬(2 < (0 + ε)^(2:ℕ)))› with
  | .inl (_ : ¬((0:ℚ) ≥ 0)) =>
    have : (0:ℚ) < 0 := sorry
    have : False := sorry
    this
  | .inr (.inl (_ : ¬((0:ℚ)^(2:ℕ) < 2))) =>
    have : (0:ℚ)^(2:ℕ) < 2 := sorry
    have : False := absurd ‹(0:ℚ)^(2:ℕ) < 2› ‹¬((0:ℚ)^(2:ℕ) < 2)›
    this
  | .inr (.inr (_ : ¬(2 < (0 + ε)^(2:ℕ)))) =>
    have : 2 ≥ (0 + ε)^(2:ℕ) := sorry
    have : ε^(2:ℕ) < 2 := sorry
    sorry
  have sqr_bound (n : ℤ) : (n * ε)^(2:ℕ) < 2 := sorry

  have : AP (ε ≄ 0) := sorry
  let k : ℚ := floor (2/ε) + 1
  have (And.intro _ (_ : 2/ε < k)) := floor_bounds
  have : (k * ε)^(2:ℕ) ≥ 2 := sorry
  have : (floor k * ε)^(2:ℕ) < 2 := sqr_bound (floor k)
  have : (k * ε)^(2:ℕ) < 2 := sorry
  have : False := le_gt_false ‹2 ≤ (k * ε)^(2:ℕ)› ‹2 > (k * ε)^(2:ℕ)›
  exact this

end AnalysisI.Ch4.Sec4
