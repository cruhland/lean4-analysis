import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Impl.Difference
import Lean4Axiomatic.Natural.Impl.Nat
import Lean4Axiomatic.Rational.Impl.Fraction

namespace AnalysisI.Ch4.Sec2

open Lean4Axiomatic
open Lean4Axiomatic.Natural (step)
open Lean4Axiomatic.Rational.Impl

abbrev ℕ : Type := Nat
abbrev ℤ : Type := Integer.Impl.Difference ℕ

/- 4.2 The rationals -/

-- Definition 4.2.1.
-- A _rational number_ is an expression of the form `a//b`, where `a` and `b`
-- are integers and `b` is non-zero; `a//0` is not considered to be a rational
-- number. Two rational numbers are considered to be equal, `a//b ≃ c//d`, if
-- and only if `a * d ≃ c * b`. The set of all rational numbers is denoted `ℚ`.
abbrev ℚ : Type := Fraction ℤ

example {a b : ℤ} : ℚ := a//b

example {a b c d : ℤ} : a//b ≃ c//d ↔ a * d ≃ c * b := Iff.intro id id

-- [definition of rational equality]
example : ℚ → ℚ → Prop := Fraction.eqv

-- Thus for instance `3//4 ≃ 6//8 ≃ -3//-4`, but `3//4 ≄ 4//3`.
example : (3 : ℤ)//4 ≃ 6//8 := by
  show (3 : ℤ) * 8 ≃ 6 * 4
  show 24 ≃ 24
  rfl

example : (6 : ℤ)//8 ≃ -3//(-4) := by
  show (6 : ℤ) * -4 ≃ -3 * 8
  show -24 ≃ -24
  rfl

example : (3 : ℤ)//4 ≄ 4//3 := by
  intro (_ : (3 : ℤ)//4 ≃ 4//3)
  show False
  have : (3 : ℤ) * 3 ≃ 4 * 4 := ‹(3 : ℤ)//4 ≃ 4//3›
  have : 9 ≃ 16 := this
  have : step 8 ≃ step 15 := this
  have : 8 ≃ 15 := AA.inject this
  have : step 7 ≃ step 14 := this
  have : 7 ≃ 14 := AA.inject this
  have : step 6 ≃ step 13 := this
  have : 6 ≃ 13 := AA.inject this
  have : step 5 ≃ step 12 := this
  have : 5 ≃ 12 := AA.inject this
  have : step 4 ≃ step 11 := this
  have : 4 ≃ 11 := AA.inject this
  have : step 3 ≃ step 10 := this
  have : 3 ≃ 10 := AA.inject this
  have : step 2 ≃ step 9 := this
  have : 2 ≃ 9 := AA.inject this
  have : step 1 ≃ step 8 := this
  have : 1 ≃ 8 := AA.inject this
  have : step 0 ≃ step 7 := this
  have : 0 ≃ 7 := AA.inject this
  have : 0 ≃ step 6 := this
  exact absurd (Rel.symm ‹0 ≃ step 6›) Natural.step_neqv_zero

-- This is a valid definition of equality.
-- Exercise 4.2.1.
-- Show that the definition of equality for the rational numbers is reflexive,
-- symmetric, and transitive. (Hint: for transitivity, use Corollary 4.1.9.)
example {p : ℚ} : p ≃ p := Fraction.eqv_refl

example {p q : ℚ} : p ≃ q → q ≃ p := Fraction.eqv_symm

example
  {p q r : ℚ} : q.denominator ≄ 0 → p ≃ q → q ≃ r → p ≃ r := Fraction.eqv_trans

-- Definition 4.2.2.
-- If `a//b` and `c//d` are rational numbers, we define their sum
example {a b c d : ℤ} : (a//b) + (c//d) ≃ (a * d + b * c)//(b * d) := rfl

-- [implementation of addition]
example : ℚ → ℚ → ℚ := Fraction.add

-- their product
example {a b c d : ℤ} : (a//b) * (c//d) ≃ (a * c)//(b * d) := rfl

-- [implementation of multiplication]
example : ℚ → ℚ → ℚ := Fraction.mul

-- and the negation
example {a b : ℤ} : -(a//b) ≃ (-a)//b := rfl

-- [implementation of negation]
example : ℚ → ℚ := Fraction.neg

end AnalysisI.Ch4.Sec2
