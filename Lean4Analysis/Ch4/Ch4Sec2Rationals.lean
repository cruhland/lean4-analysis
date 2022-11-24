import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Impl.Difference
import Lean4Axiomatic.Natural.Impl.Nat
import Lean4Axiomatic.Rational.Impl.Fraction

namespace AnalysisI.Ch4.Sec2

open Coe (coe)
open Lean4Axiomatic
open Lean4Axiomatic.Integer (Nonzero)
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

example {a b : ℤ} [Nonzero b] : ℚ := a//b

example {a b c d : ℤ} [Nonzero b] [Nonzero d] : a//b ≃ c//d ↔ a * d ≃ c * b :=
  Iff.intro id id

-- [definition of rational equality]
example : ℚ → ℚ → Prop := Fraction.eqv

def literal_nonzero {n : ℕ} : n ≄ 0 → Nonzero (coe n : ℤ) := by
  intro (_ : n ≄ 0)
  have : coe n ≄ coe 0 := AA.subst₁ (β := ℤ) ‹n ≄ 0›
  have : Nonzero (coe n) := Integer.nonzero_iff_neqv_zero.mpr ‹coe n ≄ coe 0›
  exact this

instance : Nonzero 3 := literal_nonzero Natural.step_neqv_zero
instance : Nonzero 4 := literal_nonzero Natural.step_neqv_zero
instance : Nonzero 8 := literal_nonzero Natural.step_neqv_zero

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

example {p q r : ℚ} : p ≃ q → q ≃ r → p ≃ r := Fraction.eqv_trans

-- Definition 4.2.2.
-- If `a//b` and `c//d` are rational numbers, we define their sum
example
    {a b c d : ℤ} [Nonzero b] [Nonzero d]
    : (a//b) + (c//d) ≃ (a * d + b * c)//(b * d)
    :=
  rfl

-- [implementation of addition]
example : ℚ → ℚ → ℚ := Fraction.add

-- their product
example
    {a b c d : ℤ} [Nonzero b] [Nonzero d]
    : (a//b) * (c//d) ≃ (a * c)//(b * d)
    :=
  rfl

-- [implementation of multiplication]
example : ℚ → ℚ → ℚ := Fraction.mul

-- and the negation
example {a b : ℤ} [Nonzero b] : -(a//b) ≃ (-a)//b := rfl

-- [implementation of negation]
example : ℚ → ℚ := Fraction.neg

-- Lemma 4.2.3. / Exercise 4.2.2.
-- The sum, product, and negation operations on rational numbers are
-- well-defined, in the sense that if one replaces `a//b` with another rational
-- number `a'//b'` which is equal to `a//b`, then the output of the above
-- operations remains unchanged, and similarly for `c//d`.
example
    {a a' b b' c d : ℤ} [Nonzero b] [Nonzero b'] [Nonzero d]
    : a//b ≃ a'//b' → a//b + c//d ≃ a'//b' + c//d
    :=
  Fraction.add_substL

example
    {a b c c' d d' : ℤ} [Nonzero b] [Nonzero d] [Nonzero d']
    : c//d ≃ c'//d' → a//b + c//d ≃ a//b + c'//d'
    :=
  Fraction.add_substR

example
    {a a' b b' c d : ℤ} [Nonzero b] [Nonzero b'] [Nonzero d]
    : a//b ≃ a'//b' → a//b * c//d ≃ a'//b' * c//d
    :=
  Fraction.mul_substL

example
    {a b c c' d d' : ℤ} [Nonzero b] [Nonzero d] [Nonzero d']
    : c//d ≃ c'//d' → a//b * c//d ≃ a//b * c'//d'
    :=
  Fraction.mul_substR

example
    {a a' b b' : ℤ} [Nonzero b] [Nonzero b']
    : a//b ≃ a'//b' → -(a//b) ≃ -(a'//b')
    :=
  Fraction.neg_subst

-- We note that the rational numbers `a//1` behave in a manner identical to the
-- integers `a`:
example {a b : ℤ} : a//1 + b//1 ≃ (a + b)//1 := calc
  a//1 + b//1              ≃ _ := Rel.refl
  (a * 1 + 1 * b)//(1 * 1) ≃ _ := Fraction.substL (AA.substL AA.identR)
  (a + 1 * b)//(1 * 1)     ≃ _ := Fraction.substL (AA.substR AA.identL)
  (a + b)//(1 * 1)         ≃ _ := Fraction.substR AA.identL
  (a + b)//1               ≃ _ := Rel.refl

example {a b : ℤ} : a//1 * b//1 ≃ (a * b)//1 := calc
  a//1 * b//1      ≃ _ := Rel.refl
  (a * b)//(1 * 1) ≃ _ := Fraction.substR AA.identL
  (a * b)//1       ≃ _ := Rel.refl

example {a : ℤ} : -(a//1) ≃ (-a)//1 := Rel.refl

-- Also, `a//1` and `b//1` are only equal when `a` and `b` are equal.
example {a b : ℤ} : a ≃ b ↔ a//1 ≃ b//1 := by
  apply Iff.intro
  case mp =>
    intro (_ : a ≃ b)
    show a//1 ≃ b//1
    show a * 1 ≃ b * 1
    exact AA.substL ‹a ≃ b›
  case mpr =>
    intro (_ : a//1 ≃ b//1)
    show a ≃ b
    have : a * 1 ≃ b * 1 := ‹a//1 ≃ b//1›
    exact AA.cancelRC (C := (· ≄ 0)) Integer.one_neqv_zero ‹a * 1 ≃ b * 1›

-- Because of this, we will identify `a` with `a//1` for each integer `a`:
-- `a ≡ a//1`; the above identities then guarantee that the arithmetic of the
-- integers is consistent with the arithmetic of the rationals.
-- [Note: we can't make integers equal to rationals in Lean, but we can provide
-- a coercion from integers to rationals.]
example {a : ℤ} : coe a ≃ a//1 := Rel.refl

-- Thus just as we embedded the natural numbers inside the integers, we embed
-- the integers inside the rational numbers. In particular, all natural numbers
-- are rational numbers, for instance `0` is equal to `0//1` and `1` is equal
-- to `1//1`.
example : (coe (coe (0 : ℕ) : ℤ) : ℚ) ≃ 0//1 := Rel.refl
example : (coe (coe (1 : ℕ) : ℤ) : ℚ) ≃ 1//1 := Rel.refl

-- Observe that a rational number `a//b` is equal to `0 ≃ 0//1` if and only if
-- `a * 1 ≃ b * 0`, i.e., if the numerator `a` is equal to `0`. Thus if `a` and
-- `b` are non-zero then so is `a//b`.
example {p : ℚ} : p ≃ 0 ↔ p.numerator ≃ 0 :=
  Fraction.eqv_zero_iff_numerator_eqv_zero

-- We now define a new operation on the rationals: reciprocal. If `x ≃ a//b` is
-- a non-zero rational (so that `a, b ≄ 0`) then we define the _reciprocal_
-- `x⁻¹` of `x` to be the rational number `x⁻¹ := b//a`.
example {a b : ℤ} [Nonzero a] [Nonzero b] : (a//b)⁻¹ ≃ b//a := rfl

-- [implementation of reciprocal]
example : (q : ℚ) → [Fraction.Nonzero q] → ℚ := Fraction.reciprocal

-- It is easy to check that this operation is consistent with our notion of
-- equality: if two rational numbers `a//b`, `a'//b'` are equal, then their
-- reciprocals are also equal.
example
    {p q : ℚ} [Fraction.Nonzero p] [Fraction.Nonzero q] : p ≃ q → p⁻¹ ≃ q⁻¹
    :=
  Fraction.recip_subst

section prop_4_2_4

-- Exercise 4.2.3.
-- Proposition 4.2.4 (Laws of algebra for rationals).
-- Let `x`, `y`, `z` be rationals. Then the following laws of algebra hold:
variable {x y z : ℚ}

example : x + y ≃ y + x := Fraction.add_comm

example : (x + y) + z ≃ x + (y + z) := Fraction.add_assoc

example : x + 0 ≃ x := Fraction.add_identR

example : 0 + x ≃ x := Fraction.add_identL

example : x + -x ≃ 0 := Fraction.add_inverseR

example : -x + x ≃ 0 := Fraction.add_inverseL

example : x * y ≃ y * x := Fraction.mul_comm

example : (x * y) * z ≃ x * (y * z) := Fraction.mul_assoc

example : x * 1 ≃ x := Fraction.mul_identR

example : 1 * x ≃ x := Fraction.mul_identL

example : x * (y + z) ≃ x * y + x * z := Fraction.mul_distribL

example : (y + z) * x ≃ y * x + z * x := Fraction.mul_distribR

-- If `x` is non-zero, we also have
example [Fraction.Nonzero x] : x * x⁻¹ ≃ 1 := Fraction.recip_inverseR

example [Fraction.Nonzero x] : x⁻¹ * x ≃ 1 := Fraction.recip_inverseL

end prop_4_2_4

-- We can now define the _quotient_ `x / y` of two rational numbers `x` and
-- `y`, _provided that_ `y` is non-zero, by the formula
example {x y : ℚ} [Fraction.Nonzero y] : x / y ≃ x * y⁻¹ := rfl

-- [definition of division]
example : (x y : ℚ) → [Fraction.Nonzero y] → ℚ := Fraction.div

end AnalysisI.Ch4.Sec2
