import Lean4Axiomatic.Integer.Impl.Difference
import Lean4Axiomatic.Natural.Impl.Nat
import Lean4Axiomatic.Rational
import Lean4Axiomatic.Rational.Impl.Fraction

namespace AnalysisI.Ch4.Sec4

open Lean4Axiomatic -- to use Rel namespace
open Lean4Axiomatic.Logic (AP)
open Lean4Axiomatic.Natural (step)
open Lean4Axiomatic.Rational
open Lean4Axiomatic.Relation.Equivalence (Unique)
open Lean4Axiomatic.Signed (sgn)

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

-- Exercise 4.4.3.
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

[Note: when using Tao's approach in the book, we can only prove the
double-negation of this statement constructively.]
-/
example {ε : ℚ}
    : ε > 0 → ¬¬∃ x : ℚ, x ≥ 0 ∧ x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ)
    := by
  intro (_ : ε > 0) (_ : ¬∃ x : ℚ, x ≥ 0 ∧ x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ))
  show False

  /- Every underestimate of sqrt 2 remains so after adding `ε` -/
  have under2 {x : ℚ} : x ≥ 0 → x^(2:ℕ) < 2 → (x + ε)^(2:ℕ) < 2 := by
    intro (_ : x ≥ 0) (_ : x^(2:ℕ) < 2)
    show (x + ε)^(2:ℕ) < 2

    match (order_trichotomy ((x + ε)^(2:ℕ)) 2).atLeastOne with
    | AA.OneOfThree.first (_ : (x + ε)^(2:ℕ) < 2) =>
      exact ‹(x + ε)^(2:ℕ) < 2›
    | AA.OneOfThree.second (_ : (x + ε)^(2:ℕ) ≃ 2) =>
      exact absurd ‹(x + ε)^(2:ℕ) ≃ 2› sqrt2_irrational
    | AA.OneOfThree.third (_ : (x + ε)^(2:ℕ) > 2) =>
      let magic_x_exists := ∃ x : ℚ, x ≥ 0 ∧ x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ)
      have : x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ) :=
        And.intro ‹x^(2:ℕ) < 2› ‹2 < (x + ε)^(2:ℕ)›
      have : magic_x_exists :=
        Exists.intro x (And.intro ‹x ≥ 0› ‹x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ)›)
      exact absurd ‹magic_x_exists› ‹¬magic_x_exists›

  /- Any finite number of `ε`s is not enough to exceed sqrt 2 -/
  have sqr_bound {n : ℤ} : n ≥ 0 → (n * ε)^(2:ℕ) < 2 := by
    intro (_ : n ≥ 0)

    let motive (k : ℤ) := (k * ε)^(2:ℕ) < 2
    have motive_subst {k₁ k₂ : ℤ} : k₁ ≃ k₂ → motive k₁ → motive k₂ := by
      intro (_ : k₁ ≃ k₂) (_ : motive k₁)
      show motive k₂
      prw [‹k₁ ≃ k₂›] ‹motive k₁›
    apply Integer.ind_from motive_subst ‹n ≥ 0›
    case base =>
      show motive 0

      have : (0:ℚ) ≃ 0 ∧ 2 ≄ 0 := And.intro eqv_refl Natural.two_neqv_zero
      have : (0 * ε)^(2:ℕ) < 2 := calc
        _ = (0 * ε)^(2:ℕ) := rfl
        _ ≃ 0^(2:ℕ)       := by srw [mul_absorbL]
        _ ≃ 0             := Natural.pow_eqv_zero.mpr ‹(0:ℚ) ≃ 0 ∧ 2 ≄ 0›
        _ < 2             := two_pos
      have : motive 0 := ‹(0 * ε)^(2:ℕ) < 2›
      exact this
    case next =>
      intro (k : ℤ) (_ : k ≥ 0) (_ : motive k)
      show motive (k + 1)

      have : k * ε ≥ 0 := calc
        _ = k * ε     := rfl
        _ ≥ (0:ℤ) * ε := le_substL_mul_pos ‹ε > 0› (by srw [‹k ≥ 0›])
        _ ≃ 0         := mul_absorbL
      have : (k * ε)^(2:ℕ) < 2 := ‹motive k›
      have : (k * ε + ε)^(2:ℕ) < 2 := under2 ‹k * ε ≥ 0› ‹(k * ε)^(2:ℕ) < 2›

      have : ((k + 1 : ℤ) * ε)^(2:ℕ) < 2 := calc
        _ = ((k + 1 : ℤ) * ε)^(2:ℕ) := rfl
        _ ≃ ((k + (1:ℤ)) * ε)^(2:ℕ) := by srw [add_compat_from_integer]
        _ = ((k + 1) * ε)^(2:ℕ)     := rfl
        _ ≃ (k * ε + 1 * ε)^(2:ℕ)   := by srw [mul_distribR]
        _ ≃ (k * ε + ε)^(2:ℕ)       := by srw [mul_identL]
        _ < 2                       := ‹(k * ε + ε)^(2:ℕ) < 2›
      have : motive (k + 1) := ‹((k + 1 : ℤ) * ε)^(2:ℕ) < 2›
      exact this

  /- Pick a specific number of `ε`s for a possible sqrt 2 approximation -/
  have : AP (ε ≄ 0) := AP.mk (pos_nonzero ‹ε > 0›)
  let k : ℚ := floor (2/ε) + 1

  /- By `sqr_bound` the approximation must be less than sqrt 2 -/
  have : (k * ε)^(2:ℕ) < 2 :=
    have : (floor k : ℚ) ≃ k := calc
      _ = (floor k : ℚ)                     := rfl
      _ = floor ((floor (2/ε) : ℚ) + (1:ℤ)) := rfl
      _ ≃ floor ((floor (2/ε) + 1 : ℤ):ℚ)   := by srw [←add_compat_from_integer]
      _ ≃ ((floor (2/ε) + 1 : ℤ):ℚ)         := by srw [floor_int]
      _ ≃ (floor (2/ε) : ℚ) + 1             := add_compat_from_integer
      _ = k                                 := rfl
    have : ε ≥ -2 := calc
      _ = ε  := rfl
      _ ≥ 0  := le_cases.mpr (.inl ‹ε > 0›)
      _ ≃ -0 := neg_eqv_zero.mpr eqv_refl
      _ ≥ -2 := by srw [le_cases.mpr (.inl two_pos)]
    have : (-1:ℤ) ≤ 2/ε := calc
      _ = ((-1:ℤ):ℚ) := rfl
      _ ≃ -1         := neg_compat_from_integer
      _ ≃ -(ε/ε)     := by srw [←div_same]
      _ ≃ -ε/ε       := neg_scompatL_div
      _ ≤ -(-2)/ε    := le_substN_div_gt_zero ‹ε > 0› (by srw [‹ε ≥ -2›])
      _ ≃ 2/ε        := by srw [neg_involutive]
    have : -1 ≤ floor (2/ε) := floor_lb ‹(-1:ℤ) ≤ 2/ε›
    have : (floor k : ℚ) ≥ 0 := calc
      _ = (floor k : ℚ)   := rfl
      _ ≃ k               := ‹(floor k : ℚ) ≃ k›
      _ = floor (2/ε) + 1 := rfl
      _ ≥ (-1:ℤ) + 1      := by srw [‹-1 ≤ floor (2/ε)›]
      _ ≃ -(1:ℤ) + 1      := by srw [neg_compat_from_integer]
      _ = -1 + 1          := rfl
      _ ≃ 0               := add_inverseL
    have : floor k ≥ 0 := le_respects_from_integer.mpr ‹(floor k : ℚ) ≥ 0›
    show (k * ε)^(2:ℕ) < 2 from calc
      _ = (k * ε)^(2:ℕ)       := rfl
      _ ≃ (floor k * ε)^(2:ℕ) := by srw [←‹(floor k : ℚ) ≃ k›]
      _ < 2                   := sqr_bound ‹floor k ≥ 0›

  /-
  But the definition of `k` implies that the approximation must also be greater
  than or equivalent to sqrt 2
  -/
  have : (k * ε)^(2:ℕ) ≥ 2 :=
    have (And.intro _ (_ : 2/ε < k)) := floor_bounds
    have : (k * ε)^(2:ℕ) > (2:ℚ)^(2:ℕ) :=
      have : k * ε > 2 := calc
        _ = k * ε   := rfl
        _ > 2/ε * ε := lt_substL_mul_pos ‹ε > 0› ‹k > 2/ε›
        _ ≃ 2       := div_mul_cancel
      have : (2:ℚ) ≥ 0 := ge_cases.mpr (.inl two_pos)
      have : (2:ℕ) ≥ 1 := Natural.le_split.mpr (.inl Natural.two_gt_one)
      show (k * ε)^(2:ℕ) > (2:ℚ)^(2:ℕ) from
        pow_pos_preserves_gt_nonneg ‹k * ε > 2› ‹(2:ℚ) ≥ 0› ‹(2:ℕ) ≥ 1›
    have : (k * ε)^(2:ℕ) > 2 := calc
      _ = (k * ε)^(2:ℕ) := rfl
      _ > (2:ℚ)^(2:ℕ)   := ‹(k * ε)^(2:ℕ) > (2:ℚ)^(2:ℕ)›
      _ ≃ 2 * 2         := Natural.pow_two
      _ > 1 * 2         := lt_substL_mul_pos two_pos two_gt_one
      _ ≃ 2             := mul_identL
    show (k * ε)^(2:ℕ) ≥ 2 from le_cases.mpr (.inl ‹(k * ε)^(2:ℕ) > 2›)

  have : False := le_gt_false ‹2 ≤ (k * ε)^(2:ℕ)› ‹2 > (k * ε)^(2:ℕ)›
  exact this

/--
**Proposition 4.4.5 (alternate).**
For every rational number `ε > 0`, there exists a non-negative rational number
`x` such that `x^2 < 2 < (x + ε)^2`.

[Note: using a direct constructive approach.]
-/
example {ε : ℚ}
    : ε > 0 → ∃ x : ℚ, x ≥ 0 ∧ x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ)
    := by
  intro (_ : ε > 0)
  show ∃ x : ℚ, x ≥ 0 ∧ x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ)

  let res : Sqrt2Approx ε := sqrt2_approx ‹ε > 0›
  let x := res.val
  have : x ≥ 0 := res.nonneg
  have : x^(2:ℕ) < 2 := res.lower
  have : 2 < (x + ε)^(2:ℕ) := res.upper
  have : x ≥ 0 ∧ x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ) :=
    And.intro ‹x ≥ 0› (And.intro ‹x^(2:ℕ) < 2› ‹2 < (x + ε)^(2:ℕ)›)
  exact Exists.intro x ‹x ≥ 0 ∧ x^(2:ℕ) < 2 ∧ 2 < (x + ε)^(2:ℕ)›

namespace evaluation

abbrev ℕ' : Type := Nat
abbrev ℤ' : Type := Integer.Impl.Difference ℕ'
abbrev ℚ' : Type := Rational.Impl.Fraction ℤ'

/-
**Example 4.4.6.**
If `ε = 0.001`, we can take `x = 1.414`, since `x^2 = 1.999396` and
`(x + ε) = 2.002225`.
-/
def ε : ℚ' := 0.001
def x : ℚ' := 1.414

example : x^(2:ℕ') = 1.999396 := rfl

/-
Note: equivalence is needed because adding fractions produces denominators that
aren't in lowest terms.
-/
example : (x + ε : ℚ')^(2:ℕ') ≃ 2.002225 := rfl

/-
Using the constructive implementation, we can actually compute the
approximation.
-/
namespace compute_approx

/- [Note: for an unknown reason, Lean can't infer this automatically] -/
scoped instance fcInst : FloorCeil ℚ' :=
  (inferInstance : Rational ℚ').toFloorCeil

set_option maxRecDepth 60000 in
example : (sqrt2_approx (show ε > 0 by rfl)).val ≃ 1.414 := rfl

end compute_approx
end evaluation

-- Exercise 4.4.2.
namespace ex442

/--
A definition: a sequence `a₀, a₁, a₂, ...` of numbers (natural numbers,
integers, rationals, or reals) is said to be in _infinite descent_ if we have
`aₙ > aₙ₊₁` for all natural numbers `n` (i.e., `a₀ > a₁ > a₂ > ...`).
-/
example : Sequence ℕ ℕ → Prop := Sequence.InfiniteDescent

/--
(a) Prove the _principle of infinite descent_: that it is not possible to have
a sequence of _natural numbers_ which is in infinite descent.
-/
example {s : Sequence ℕ ℕ} : ¬(Sequence.InfiniteDescent s) :=
  Sequence.inf_desc_impossible

/-
(b) Does the principle of infinite descent work if the sequence
`a₁, a₂, a₃, ...` is allowed to take integer values instead of natural number
values?
-/
def negate : ℕ → ℤ := (-·)

theorem negate_subst {n₁ n₂ : ℕ} : n₁ ≃ n₂ → (negate n₁ : ℤ) ≃ negate n₂ := by
  intro (_ : n₁ ≃ n₂)
  show negate n₁ ≃ negate n₂
  calc
    _ = (negate n₁ : ℤ) := rfl
    _ = -n₁             := rfl
    _ ≃ -n₂             := by srw [‹n₁ ≃ n₂›]
    _ = negate n₂       := rfl

def negative_integers : Sequence ℕ ℤ := Sequence.mk negate negate_subst

example : Sequence.InfiniteDescent (α := ℤ) negative_integers := by
  intro (n : ℕ)
  show negative_integers[n] > negative_integers[step n]

  calc
    _ = negative_integers[n]                      := rfl
    _ = (Sequence.mk negate negate_subst)[n]      := rfl
    _ = negate n                                  := rfl
    _ = -(n:ℤ)                                    := rfl
    _ > -(step n)                                 := by srw [Natural.lt_step]
    _ = negate (step n)                           := rfl
    _ = (Sequence.mk negate negate_subst)[step n] := rfl
    _ = negative_integers[step n]                 := rfl

/-
What about if it is allowed to take positive rational values instead of natural
numbers?
-/
scoped instance step_nonzero {n : ℕ} : AP ((step n : ℚ) ≄ 0) :=
  have : step n ≄ 0 := Natural.step_neqv_zero
  have fn_inject {m₁ m₂ : ℕ} : (m₁:ℤ) ≃ (m₂:ℤ) → m₁ ≃ m₂ := AA.inject
  have : (step n : ℤ) ≄ 0 := mt fn_inject ‹step n ≄ 0›
  have : (step n : ℚ) ≄ 0 := mt from_integer_inject ‹(step n : ℤ) ≄ 0›
  AP.mk ‹(step n : ℚ) ≄ 0›

def reciprocate (n : ℕ) : ℚ := (step n)⁻¹

theorem reciprocate_subst
    {n₁ n₂ : ℕ} : n₁ ≃ n₂ → (reciprocate n₁ : ℚ) ≃ reciprocate n₂
    := by
  intro (_ : n₁ ≃ n₂)
  show (reciprocate n₁ : ℚ) ≃ reciprocate n₂

  calc
    _ = (reciprocate n₁ : ℚ) := rfl
    _ = (step n₁ : ℚ)⁻¹      := rfl
    _ ≃ (step n₂ : ℚ)⁻¹      := by srw [‹n₁ ≃ n₂›]
    _ = (reciprocate n₂ : ℚ) := rfl

def positive_rationals : Sequence ℕ ℚ :=
  Sequence.mk reciprocate reciprocate_subst

example : Sequence.InfiniteDescent (α := ℚ) positive_rationals := by
  intro (n : ℕ)
  show positive_rationals[n] > positive_rationals[step n]

  have prod_pos : (step n : ℚ) * (step (step n) : ℚ) > 0 :=
    let sn := step n
    have : sgn ((sn:ℚ) * (step sn : ℚ)) ≃ 1 := calc
      _ = sgn ((sn:ℚ) * (step sn : ℚ))   := rfl
      _ ≃ sgn (sn:ℚ) * sgn (step sn : ℚ) := sgn_compat_mul
      _ ≃ sgn (sn:ℤ) * sgn (step sn : ℚ) := by srw [sgn_from_integer]
      _ ≃ sgn (sn:ℤ) * sgn (step sn : ℤ) := by srw [sgn_from_integer]
      _ ≃ 1 * sgn (step sn : ℤ)          := by srw [Integer.sgn_step]
      _ ≃ sgn (step sn : ℤ)              := AA.identL
      _ ≃ 1                              := Integer.sgn_step
    show (step n : ℚ) * (step (step n) : ℚ) > 0 from
      gt_zero_sgn.mpr ‹sgn ((sn:ℚ) * (step sn : ℚ)) ≃ 1›
  have lt_step : (step n : ℚ) < (step (step n) : ℚ) := by srw [Natural.lt_step]

  calc
    _ = positive_rationals[n]      := rfl
    _ = reciprocate n              := rfl
    _ = (step n : ℚ)⁻¹             := rfl
    _ > (step (step n) : ℚ)⁻¹      := (lt_recip prod_pos).mp lt_step
    _ = reciprocate (step n)       := rfl
    _ = positive_rationals[step n] := rfl

end ex442

end AnalysisI.Ch4.Sec4
