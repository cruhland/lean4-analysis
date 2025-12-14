import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Impl.Difference
import Lean4Axiomatic.Natural.Impl.Nat
import Lean4Axiomatic.Rational.Impl.Fraction

namespace AnalysisI.Ch4.Sec2

open Coe (coe)
open Lean4Axiomatic
open Lean4Axiomatic.Integer (Nonzero)
open Lean4Axiomatic.Logic (AP)
open Lean4Axiomatic.Natural (step)
open Lean4Axiomatic.Rational.Impl
open Lean4Axiomatic.Signed (Negative Positive sgn)

abbrev ℕ : Type := Nat
local instance natural_induction₁_inst : Natural.Induction.{1} ℕ :=
  Natural.Impl.Nat.induction

abbrev ℤ : Type := Integer.Impl.Difference ℕ

/- 4.2 The rationals -/

section formal_fractions

-- Definition 4.2.1.
-- A _rational number_ is an expression of the form `a//b`, where `a` and `b`
-- are integers and `b` is non-zero; `a//0` is not considered to be a rational
-- number. Two rational numbers are considered to be equal, `a//b ≃ c//d`, if
-- and only if `a * d ≃ c * b`. The set of all rational numbers is denoted `ℚ`.
abbrev ℚ : Type := Fraction ℤ

-- [Note: the implementation of rationals we're using requires denominators to
-- be _positive_, not just nonzero. Since this is a stronger requirement it
-- shouldn't impact the code here too much; we'll clarify with a note when it
-- does.]
example {a b : ℤ} [AP (Positive b)] : ℚ := a//b

example
    {a b c d : ℤ} [AP (Positive b)] [AP (Positive d)]
    : a//b ≃ c//d ↔ a * d ≃ c * b
    :=
  Iff.intro id id

-- [axiom and definition for rational equality]
example : ℚ → ℚ → Prop := Rational.eqv
example : ℚ → ℚ → Prop := Fraction.eqv

-- [helper function to generate `Nonzero` instances for integer literals]
def literal_nonzero {n : ℕ} : n ≄ 0 → Nonzero (n : ℤ) := by
  intro (_ : n ≄ 0)
  have : coe n ≄ coe 0 := AA.subst₁ (β := ℤ) ‹n ≄ 0›
  have : Nonzero (n : ℤ) := Integer.nonzero_iff_neqv_zero.mpr ‹coe n ≄ coe 0›
  exact this

-- [helper function to generate `Positive` instances for integer literals]
def literal_positive {n : ℕ} : n ≄ 0 → AP (Positive (n : ℤ)) := by
  intro (_ : n ≄ 0)
  have : Positive n := Signed.positive_defn.mpr ‹n ≄ 0›
  have : Positive (n : ℤ) := Integer.positive_intro_nat ‹Positive n› Rel.refl
  exact AP.mk this

-- [This is a default instance so that integer literals can be used without
-- type annotations. The priority is higher than both `Neg Int` and `OfNat Nat`
-- from the Prelude.]
@[default_instance mid+1]
abbrev integer_literal {n : Nat} := Integer.literal (ℤ := ℤ) (n := n)

-- [these instances are needed for literals to be denominators of fractions]
instance : Nonzero 5 := literal_nonzero Natural.step_neqv_zero
instance : AP (Positive 2) := literal_positive Natural.step_neqv_zero
instance : AP (Positive 3) := literal_positive Natural.step_neqv_zero
instance : AP (Positive 4) := literal_positive Natural.step_neqv_zero
instance : AP (Positive 5) := literal_positive Natural.step_neqv_zero
instance : AP (Positive 6) := literal_positive Natural.step_neqv_zero
instance : AP (Positive 8) := literal_positive Natural.step_neqv_zero
instance : AP (Positive 10) := literal_positive Natural.step_neqv_zero
instance : AP (Positive 20) := literal_positive Natural.step_neqv_zero

-- Thus for instance `3//4 ≃ 6//8 ≃ -3//-4`, but `3//4 ≄ 4//3`.
example : 3//4 ≃ 6//8 := by
  show 3 * 8 ≃ 6 * 4
  show 24 ≃ 24
  rfl

-- [Note: `-3//(-4)` is not a valid fraction in our definition; so we show a
-- slightly different equivalence.]
-- example : 6//8 ≃ (-3)//(-4) := by
example : (-6)//8 ≃ (-3)//4 := by
  show -6 * 4 ≃ -3 * 8
  show -24 ≃ -24
  rfl

example : 3//4 ≄ 4//3 := by
  intro (_ : 3//4 ≃ 4//3)
  show False
  have : 3 * 3 ≃ 4 * 4    := ‹3//4 ≃ 4//3›
  have : 9 ≃ 16           := this
  have : step 8 ≃ step 15 := this
  have : (8:ℕ) ≃ 15       := AA.inject this
  have : step 7 ≃ step 14 := this
  have : (7:ℕ) ≃ 14       := AA.inject this
  have : step 6 ≃ step 13 := this
  have : (6:ℕ) ≃ 13       := AA.inject this
  have : step 5 ≃ step 12 := this
  have : (5:ℕ) ≃ 12       := AA.inject this
  have : step 4 ≃ step 11 := this
  have : (4:ℕ) ≃ 11       := AA.inject this
  have : step 3 ≃ step 10 := this
  have : (3:ℕ) ≃ 10       := AA.inject this
  have : step 2 ≃ step 9  := this
  have : (2:ℕ) ≃ 9        := AA.inject this
  have : step 1 ≃ step 8  := this
  have : (1:ℕ) ≃ 8        := AA.inject this
  have : step 0 ≃ step 7  := this
  have : (0:ℕ) ≃ 7        := AA.inject this
  have : 0 ≃ step 6       := this
  have : 0 ≄ step 6       := Rel.symm Natural.step_neqv_zero
  exact absurd ‹0 ≃ step 6› ‹0 ≄ step 6›

-- This is a valid definition of equality.
-- Exercise 4.2.1.
-- Show that the definition of equality for the rational numbers is reflexive,
-- symmetric, and transitive.
-- [axioms]
example {p : ℚ} : p ≃ p := Rational.eqv_refl
example {p q : ℚ} : p ≃ q → q ≃ p := Rational.eqv_symm
example {p q r : ℚ} : p ≃ q → q ≃ r → p ≃ r := Rational.eqv_trans

-- [fraction implementations]
example {p : ℚ} : p ≃ p := Fraction.eqv_refl
example {p q : ℚ} : p ≃ q → q ≃ p := Fraction.eqv_symm
example {p q r : ℚ} : p ≃ q → q ≃ r → p ≃ r := Fraction.eqv_trans

-- Definition 4.2.2.
-- If `a//b` and `c//d` are rational numbers, we define their sum
example
    {a b c d : ℤ} [AP (Positive b)] [AP (Positive d)]
    : (a//b) + (c//d) ≃ (a * d + b * c)//(b * d)
    :=
  rfl

-- [declaration and definition of addition]
example : ℚ → ℚ → ℚ := Rational.add
example : ℚ → ℚ → ℚ := Fraction.add

-- their product
example
    {a b c d : ℤ} [AP (Positive b)] [AP (Positive d)]
    : (a//b) * (c//d) ≃ (a * c)//(b * d)
    :=
  rfl

-- [declaration and definition of multiplication]
example : ℚ → ℚ → ℚ := Rational.mul
example : ℚ → ℚ → ℚ := Fraction.mul

-- and the negation
example {a b : ℤ} [AP (Positive b)] : -(a//b) ≃ (-a)//b := rfl

-- [declaration and definition of negation]
example : ℚ → ℚ := Rational.neg
example : ℚ → ℚ := Fraction.neg

-- Lemma 4.2.3. / Exercise 4.2.2.
-- The sum, product, and negation operations on rational numbers are
-- well-defined, in the sense that if one replaces `a//b` with another rational
-- number `a'//b'` which is equal to `a//b`, then the output of the above
-- operations remains unchanged, and similarly for `c//d`.
example
    {a a' b b' c d : ℤ} [AP (Positive b)] [AP (Positive b')] [AP (Positive d)]
    : a//b ≃ a'//b' → a//b + c//d ≃ a'//b' + c//d
    :=
  Fraction.add_substL

example
    {a b c c' d d' : ℤ} [AP (Positive b)] [AP (Positive d)] [AP (Positive d')]
    : c//d ≃ c'//d' → a//b + c//d ≃ a//b + c'//d'
    :=
  Fraction.add_substR

example
    {a a' b b' c d : ℤ} [AP (Positive b)] [AP (Positive b')] [AP (Positive d)]
    : a//b ≃ a'//b' → a//b * c//d ≃ a'//b' * c//d
    :=
  Fraction.mul_substL

example
    {a b c c' d d' : ℤ} [AP (Positive b)] [AP (Positive d)] [AP (Positive d')]
    : c//d ≃ c'//d' → a//b * c//d ≃ a//b * c'//d'
    :=
  Fraction.mul_substR

example
    {a a' b b' : ℤ} [AP (Positive b)] [AP (Positive b')]
    : a//b ≃ a'//b' → -(a//b) ≃ -(a'//b')
    :=
  Fraction.neg_subst

-- [axioms for all substitution properties]
example {p p' q : ℚ} : p ≃ p' → p + q ≃ p' + q := Rational.add_substL
example {p p' q : ℚ} : p ≃ p' → q + p ≃ q + p' := Rational.add_substR
example {p p' q : ℚ} : p ≃ p' → p * q ≃ p' * q := Rational.mul_substL
example {p p' q : ℚ} : p ≃ p' → q * p ≃ q * p' := Rational.mul_substR
example {p p' : ℚ} : p ≃ p' → -p ≃ -p' := Rational.neg_subst

-- We note that the rational numbers `a//1` behave in a manner identical to the
-- integers `a`:
example {a b : ℤ} : a//1 + b//1 ≃ (a + b)//1 :=
  Fraction.eqv_symm Fraction.add_compat_from_integer

example {a b : ℤ} : a//1 * b//1 ≃ (a * b)//1 :=
  Fraction.eqv_symm Fraction.mul_compat_from_integer

example {a : ℤ} : -(a//1) ≃ (-a)//1 :=
  Fraction.eqv_symm Fraction.neg_compat_from_integer

-- Also, `a//1` and `b//1` are only equal when `a` and `b` are equal.
example {a b : ℤ} : a ≃ b ↔ a//1 ≃ b//1 :=
  Iff.intro Fraction.from_integer_subst Fraction.from_integer_inject

-- Because of this, we will identify `a` with `a//1` for each integer `a`:
-- `a ≡ a//1`; the above identities then guarantee that the arithmetic of the
-- integers is consistent with the arithmetic of the rationals.
-- [Note: we can't make integers equal to rationals in Lean, but we can provide
-- a coercion from integers to rationals.]
example {a : ℤ} : (a : ℚ) ≃ a//1 := Rel.refl

-- [corresponding axioms for integer conversion]
example : ℤ → ℚ := Rational.from_integer
example : ℤ → ℚ := coe -- typeclass, backed by `from_integer`

example {a₁ a₂ : ℤ} : a₁ ≃ a₂ → (a₁ : ℚ) ≃ (a₂ : ℚ) :=
  Rational.from_integer_subst
example {a₁ a₂ : ℤ} : (a₁ : ℚ) ≃ (a₂ : ℚ) → a₁ ≃ a₂ :=
  Rational.from_integer_inject

example {a b : ℤ} : ((a + b : ℤ) : ℚ) ≃ (a : ℚ) + (b : ℚ) :=
  Rational.add_compat_from_integer
example {a b : ℤ} : ((a * b : ℤ) : ℚ) ≃ (a : ℚ) * (b : ℚ) :=
  Rational.mul_compat_from_integer
example {a : ℤ} : ((-a : ℤ) : ℚ) ≃ -(a : ℚ) := Rational.neg_compat_from_integer

-- Thus just as we embedded the natural numbers inside the integers, we embed
-- the integers inside the rational numbers. In particular, all natural numbers
-- are rational numbers, for instance `0` is equal to `0//1` and `1` is equal
-- to `1//1`.
example : 0 ≃ 0//1 := Rational.eqv_refl
example : 1 ≃ 1//1 := Rational.eqv_refl

-- Observe that a rational number `a//b` is equal to `0 ≃ 0//1` if and only if
-- `a * 1 ≃ b * 0`, i.e., if the numerator `a` is equal to `0`. Thus if `a` and
-- `b` are non-zero then so is `a//b`.
example {p : ℚ} : p ≃ 0 ↔ p.numerator ≃ 0 :=
  Fraction.eqv_zero_iff_numerator_eqv_zero

-- We now define a new operation on the rationals: reciprocal. If `x ≃ a//b` is
-- a non-zero rational (so that `a, b ≄ 0`) then we define the _reciprocal_
-- `x⁻¹` of `x` to be the rational number `x⁻¹ := b//a`.
-- [Note: this is one place where we must use a different definition due to our
-- stronger positive-denominator constraint. The denominator of the reciprocal
-- needs to be positive, but we only know that the numerator of the original
-- fraction is nonzero. Multiply it by `sgn` of itself to ensure that it is
-- positive, then multiply the numerator of the reciprocal by the same amount
-- so that the sign of the fraction doesn't change.]
example
    {a b : ℤ} [AP (Positive b)] [AP (a//b ≄ 0)]
    : have : Integer.Nonzero a := Fraction.nonzero_numerator (a//b)
      (a//b)⁻¹ ≃ (b * sgn a)//(a * sgn a)
    :=
  rfl

-- [declaration and definition of reciprocal]
example : (q : ℚ) → [AP (q ≄ 0)] → ℚ := Rational.reciprocal
example : (q : ℚ) → [AP (q ≄ 0)] → ℚ := Fraction.reciprocal

-- It is easy to check that this operation is consistent with our notion of
-- equality: if two rational numbers `a//b`, `a'//b'` are equal, then their
-- reciprocals are also equal.
example {p q : ℚ} [AP (p ≄ 0)] [AP (q ≄ 0)] : p ≃ q → p⁻¹ ≃ q⁻¹ :=
  Rational.recip_subst (p₁ := p)
example {p q : ℚ} [AP (p ≄ 0)] [AP (q ≄ 0)] : p ≃ q → p⁻¹ ≃ q⁻¹ :=
  Fraction.recip_subst

section prop_4_2_4

-- Exercise 4.2.3.
-- Proposition 4.2.4 (Laws of algebra for rationals).
-- Let `x`, `y`, `z` be rationals. Then the following laws of algebra hold:
variable {x y z : ℚ}

example : x + y ≃ y + x := Rational.add_comm
example : x + y ≃ y + x := Fraction.add_comm

example : (x + y) + z ≃ x + (y + z) := Rational.add_assoc
example : (x + y) + z ≃ x + (y + z) := Fraction.add_assoc

example : x + 0 ≃ x := Rational.add_identR
example : x + 0 ≃ x := Fraction.add_identR

example : 0 + x ≃ x := Rational.add_identL
example : 0 + x ≃ x := Fraction.add_identL

example : x + -x ≃ 0 := Rational.add_inverseR
example : x + -x ≃ 0 := Fraction.add_inverseR

example : -x + x ≃ 0 := Rational.add_inverseL
example : -x + x ≃ 0 := Fraction.add_inverseL

example : x * y ≃ y * x := Rational.mul_comm
example : x * y ≃ y * x := Fraction.mul_comm

example : (x * y) * z ≃ x * (y * z) := Rational.mul_assoc
example : (x * y) * z ≃ x * (y * z) := Fraction.mul_assoc

example : x * 1 ≃ x := Rational.mul_identR
example : x * 1 ≃ x := Fraction.mul_identR

example : 1 * x ≃ x := Rational.mul_identL
example : 1 * x ≃ x := Fraction.mul_identL

example : x * (y + z) ≃ x * y + x * z := Rational.mul_distribL
example : x * (y + z) ≃ x * y + x * z := Fraction.mul_distribL

example : (y + z) * x ≃ y * x + z * x := Rational.mul_distribR
example : (y + z) * x ≃ y * x + z * x := Fraction.mul_distribR

-- If `x` is non-zero, we also have
example [AP (x ≄ 0)] : x * x⁻¹ ≃ 1 := Rational.mul_inverseR
example [AP (x ≄ 0)] : x * x⁻¹ ≃ 1 := Fraction.mul_inverseR

example [AP (x ≄ 0)] : x⁻¹ * x ≃ 1 := Rational.mul_inverseL
example [AP (x ≄ 0)] : x⁻¹ * x ≃ 1 := Fraction.mul_inverseL

end prop_4_2_4

-- We can now define the _quotient_ `x / y` of two rational numbers `x` and
-- `y`, _provided that_ `y` is non-zero, by the formula
example {x y : ℚ} [AP (y ≄ 0)] : x / y ≃ x * y⁻¹ := Rational.div_mul_recip

-- [declaration and definition of division]
example : (x y : ℚ) → [AP (y ≄ 0)] → ℚ := Rational.div
example : (x y : ℚ) → [AP (y ≄ 0)] → ℚ := Fraction.div

-- [instance needed for example below]
instance : AP (5//6 ≄ 0) := by
  apply AP.mk
  intro (_ : 5//6 ≃ 0)
  show False
  have : 5//6 ≃ 0//1   := ‹5//6 ≃ 0›
  have : 5 * 1 ≃ 0 * 6 := this
  have : 5 ≃ 0         := this
  have : (5:ℕ) ≃ (0:ℕ) → (5:ℤ) ≃ (0:ℤ) := Integer.Conversion.from_natural_subst
  have : (5:ℤ) ≄ (0:ℤ)                 := mt this Natural.step_neqv_zero
  exact absurd ‹5 ≃ 0› ‹5 ≄ 0›

-- Thus, for instance
example : (3//4 : ℚ) / (5//6 : ℚ) ≃ 9//10 := calc
  (3//4 : ℚ) / (5//6 : ℚ) ≃ _ := Rational.div_mul_recip
  3//4 * (5//6)⁻¹         ≃ _ := Fraction.eqv_refl
  3//4 * 6//5             ≃ _ := Fraction.eqv_refl
  (3 * 6)//(4 * 5)        ≃ _ := Fraction.eqv_refl
  18//20                  ≃ _ := Fraction.eqv_refl
  ((2 * 9)//(2 * 10) : ℚ) ≃ _ := Fraction.cancelL
  9//10                   ≃ _ := Fraction.eqv_refl

-- Using this formula, it is easy to see that `a / b ≃ a//b` for every integer
-- `a` and every non-zero integer `b`.
example {a b : ℤ} [AP (Positive b)] : (a : ℚ) / (b : ℚ) ≃ a//b :=
  Fraction.div_eqv_fraction

-- Thus we can now discard the `//` notation, and use the more customary
-- `a / b` instead of `a//b`. [Note: we enforce that in this file by only
-- allowing the `//` notation in this first section; the remainder of this
-- document does not have access to it.]

-- In a similar spirit, we define subtraction on the rationals by the formula
example {x y : ℚ} : x - y ≃ x + (-y) := Rational.sub_add_neg

-- [declaration and definition of subtraction]
example : ℚ → ℚ → ℚ := Rational.sub
example : ℚ → ℚ → ℚ := Fraction.sub

end formal_fractions

variable {ℚ : Type} [Rational (ℤ := ℤ) ℚ]

-- Definition 4.2.6
-- A rational number `x` is said to be _positive_ iff we have `x ≃ a / b` for
-- some positive integers `a` and `b`.
inductive AltPositive (x : ℚ) : Prop where
| intro
    (a b : ℤ)
    (a_pos : AP (Positive a))
    (b_pos : AP (Positive b))
    (eqv : x ≃ a / b)

def AltPositive.mk
    {a b : ℤ} {x : ℚ} [AP (Positive a)] [AP (Positive b)] (_ : x ≃ a / b)
    : AltPositive x
    :=
  AltPositive.intro a b ‹AP (Positive a)› ‹AP (Positive b)› ‹x ≃ a / b›

theorem alt_positive {x : ℚ} : Positive x ↔ AltPositive x := by
  apply Iff.intro
  case mp =>
    intro (_ : Positive x)
    show AltPositive x
    have (Rational.AsRatio.mk a b (_ : AP (b ≄ 0)) x_eqv) := Rational.as_ratio x
    have : x ≃ a / b := x_eqv
    have : Integer.Nonzero b :=
      Integer.nonzero_iff_neqv_zero.mpr ‹AP (b ≄ 0)›.ev

    have : sgn a * sgn b ≃ 1 := calc
      sgn a * sgn b     ≃ _ := Rel.symm Rational.sgn_div_integers
      sgn ((a : ℚ) / b) ≃ _ := by srw [←‹x ≃ a / b›]
      sgn x             ≃ _ := Rational.sgn_positive.mp ‹Positive x›
      1                 ≃ _ := Rel.refl
    have (And.intro (_ : Integer.Sqrt1 (sgn b)) (_ : sgn a ≃ sgn b)) :=
      Integer.mul_sqrt1_eqv.mp this
    have : sgn b ≃ 1 ∨ sgn b ≃ -1 :=
      Integer.sqrt1_cases.mp ‹Integer.Sqrt1 (sgn b)›
    match this with
    | Or.inl (_ : sgn b ≃ 1) =>
      have : sgn a ≃ 1 := Rel.trans ‹sgn a ≃ sgn b› ‹sgn b ≃ 1›
      have : AP (Positive a) := AP.mk (Integer.sgn_positive.mpr ‹sgn a ≃ 1›)
      have : AP (Positive b) := AP.mk (Integer.sgn_positive.mpr ‹sgn b ≃ 1›)
      exact AltPositive.mk ‹x ≃ a / b›
    | Or.inr (_ : sgn b ≃ -1) =>
      have : sgn (-b) ≃ 1 := calc
        sgn (-b)   ≃ _ := Integer.sgn_compat_neg
        (-(sgn b)) ≃ _ := by srw [‹sgn b ≃ -1›]
        (-(-1))    ≃ _ := Integer.neg_involutive
        1          ≃ _ := Rel.refl
      have : sgn (-a) ≃ 1 := calc
        sgn (-a)   ≃ _ := Integer.sgn_compat_neg
        (-(sgn a)) ≃ _ := by srw [‹sgn a ≃ sgn b›]
        (-(sgn b)) ≃ _ := Rel.symm Integer.sgn_compat_neg
        sgn (-b)   ≃ _ := ‹sgn (-b) ≃ 1›
        1          ≃ _ := Rel.refl
      have : Positive (-a) := Integer.sgn_positive.mpr ‹sgn (-a) ≃ 1›
      have : Positive (-b) := Integer.sgn_positive.mpr ‹sgn (-b) ≃ 1›
      have : AP (Positive (-a)) := AP.mk ‹Positive (-a)›
      have : AP (Positive (-b)) := AP.mk ‹Positive (-b)›

      have : x ≃ ((-a:ℤ):ℚ)/((-b:ℤ):ℚ) := calc
        x                     ≃ _ := ‹x ≃ a / b›
        (a:ℚ)/b               ≃ _ := Rel.symm Rational.div_neg_cancel
        (-(a:ℚ))/(-(b:ℚ))     ≃ _ := by srw [←Rational.neg_compat_from_integer]
        ((-a:ℤ):ℚ)/(-b:ℚ)     ≃ _ := by srw [←Rational.neg_compat_from_integer]
        ((-a:ℤ):ℚ)/((-b:ℤ):ℚ) ≃ _ := Rational.eqv_refl
      exact AltPositive.mk ‹x ≃ ((-a:ℤ):ℚ)/((-b:ℤ):ℚ)›
  case mpr =>
    intro (_ : AltPositive x)
    show Positive x
    have (AltPositive.intro (a : ℤ) (b : ℤ) a_pos b_pos x_eqv) :=
      ‹AltPositive x›
    have : AP (Positive a) := a_pos
    have : sgn a ≃ 1 := Integer.sgn_positive.mp this.ev
    have : AP (Positive b) := b_pos
    have : sgn b ≃ 1 := Integer.sgn_positive.mp this.ev
    have : x ≃ a / b := x_eqv

    have : sgn a ≃ sgn b := Rel.trans ‹sgn a ≃ 1› (Rel.symm ‹sgn b ≃ 1›)
    have : Integer.Nonzero b := Integer.nonzero_from_positive_inst
    have : Integer.Sqrt1 (sgn b) := Integer.sgn_nonzero.mp this
    have : sgn a * sgn b ≃ 1 :=
      Integer.mul_sqrt1_eqv.mpr (And.intro this ‹sgn a ≃ sgn b›)
    have : sgn x ≃ 1 := calc
      sgn x                   ≃ _ := by srw [‹x ≃ a / b›]
      sgn ((a : ℚ) / (b : ℚ)) ≃ _ := Rational.sgn_div_integers
      sgn a * sgn b           ≃ _ := ‹sgn a * sgn b ≃ 1›
      1                       ≃ _ := Rel.refl
    have : Positive x := Rational.sgn_positive.mpr this
    exact this

-- It is said to be _negative_ iff we have `x ≃ -y` for some positive rational
-- `y` (i.e., `x ≃ (-a)/b` for some positive integers `a` and `b`).
theorem negative_iff_neg_positive
    {x : ℚ} : Negative x ↔ ∃ (y : ℚ), Positive y ∧ x ≃ -y
    := by
  apply Iff.intro
  case mp =>
    intro (_ : Negative x)
    show ∃ (y : ℚ), Positive y ∧ x ≃ -y
    have : sgn x ≃ -1 := Rational.sgn_negative.mp ‹Negative x›
    have : sgn (-x) ≃ 1 := calc
      sgn (-x) ≃ _ := Rational.sgn_compat_neg
      (-sgn x) ≃ _ := by srw [‹sgn x ≃ -1›]
      (-(-1))  ≃ _ := Integer.neg_involutive
      1        ≃ _ := Rel.refl
    have : Positive (-x) := Rational.sgn_positive.mpr ‹sgn (-x) ≃ 1›
    have : x ≃ -(-x) := Rational.eqv_symm Rational.neg_involutive
    exact Exists.intro (-x) (And.intro ‹Positive (-x)› ‹x ≃ -(-x)›)
  case mpr =>
    intro (Exists.intro (y : ℚ) (And.intro (_ : Positive y) (_ : x ≃ -y)))
    show Negative x
    have : sgn y ≃ 1 := Rational.sgn_positive.mp ‹Positive y›
    have : sgn x ≃ -1 := calc
      sgn x      ≃ _ := by srw [‹x ≃ -y›]
      sgn (-y)   ≃ _ := Rational.sgn_compat_neg
      (-(sgn y)) ≃ _ := by srw [‹sgn y ≃ 1›]
      (-1)       ≃ _ := Rel.refl
    have : Negative x := Rational.sgn_negative.mpr this
    exact this

inductive AltNegative (x : ℚ) : Prop where
| intro
    (a b : ℤ)
    (a_pos : AP (Positive a))
    (b_pos : AP (Positive b))
    (eqv : x ≃ (-a) / b)

def AltNegative.mk
    {a b : ℤ} {x : ℚ} [AP (Positive a)] [AP (Positive b)] (_ : x ≃ (-a) / b)
    : AltNegative x
    :=
  AltNegative.intro a b ‹AP (Positive a)› ‹AP (Positive b)› ‹x ≃ (-a) / b›

theorem alt_negative {x : ℚ} : Negative x ↔ AltNegative x := by
  apply Iff.intro
  case mp =>
    intro (_ : Negative x)
    show AltNegative x
    have (Exists.intro (y : ℚ) (And.intro (_ : Positive y) (_ : x ≃ -y))) :=
      negative_iff_neg_positive.mp ‹Negative x›
    have
      (AltPositive.intro
        (a : ℤ) (b : ℤ)
        (_ : AP (Positive a)) (_ : AP (Positive b)) y_eqv_a_over_b)
      := alt_positive.mp ‹Positive y›
    have : y ≃ a / b := y_eqv_a_over_b
    have : x ≃ (-a) / b := calc
      x                ≃ _ := ‹x ≃ -y›
      (-y)             ≃ _ := by srw [‹y ≃ a / b›]
      (-((a : ℚ) / b)) ≃ _ := Rational.neg_scompatL_div
      (-a : ℚ) / b     ≃ _ := Rational.eqv_refl
    exact AltNegative.mk this
  case mpr =>
    intro (_ : AltNegative x)
    show Negative x
    have
      (AltNegative.intro
        (a : ℤ) (b : ℤ)
        (_ : AP (Positive a)) (_ : AP (Positive b)) x_eqv_neg_a_over_b)
      := ‹AltNegative x›
    have : x ≃ (-a) / b := x_eqv_neg_a_over_b
    have : AltPositive ((a : ℚ) / b) := AltPositive.mk Rational.eqv_refl
    have : Positive ((a : ℚ) / b) := alt_positive.mpr this
    have : x ≃ -((a : ℚ) / b) := calc
      x                ≃ _ := ‹x ≃ (-a) / b›
      (-a : ℚ) / b     ≃ _ := Rational.eqv_symm Rational.neg_scompatL_div
      (-((a : ℚ) / b)) ≃ _ := Rational.eqv_refl
    have : ∃ (y : ℚ), Positive y ∧ x ≃ -y :=
      Exists.intro ((a : ℚ) / b) (And.intro ‹Positive ((a : ℚ) / b)› this)
    have : Negative x := negative_iff_neg_positive.mpr this
    exact this

-- Thus for instance, every positive integer is a positive rational number, and
-- every negative integer is a negative rational number, so our new definition
-- is consistent with our old one.
example {a : ℤ} : Positive a → Positive (a : ℚ) := by
  intro (_ : Positive a)
  show Positive (a : ℚ)
  have : sgn a ≃ 1 := Integer.sgn_positive.mp ‹Positive a›
  have : sgn (a : ℚ) ≃ 1 := calc
    sgn (a : ℚ) ≃ _ := Rational.sgn_from_integer
    sgn a       ≃ _ := ‹sgn a ≃ 1›
    1           ≃ _ := Rel.refl
  have : Positive (a : ℚ) := Rational.sgn_positive.mpr this
  exact this

example {a : ℤ} : Negative a → Negative (a : ℚ) := by
  intro (_ : Negative a)
  show Negative (a : ℚ)
  have : sgn a ≃ -1 := Integer.sgn_negative.mp ‹Negative a›
  have : sgn (a : ℚ) ≃ -1 := calc
    sgn (a : ℚ) ≃ _ := Rational.sgn_from_integer
    sgn a       ≃ _ := ‹sgn a ≃ -1›
    (-1)        ≃ _ := Rel.refl
  have : Negative (a : ℚ) := Rational.sgn_negative.mpr this
  exact this

-- Exercise 4.2.4.
-- Lemma 4.2.7 (Trichotomy of rationals).
-- Let `x` be a rational number. Then exactly one of the following three
-- statements is true: (a) `x` is equal to `0`. (b) `x` is a positive rational
-- number. (c) `x` is a negative rational number.
example {x : ℚ} : AA.ExactlyOneOfThree (x ≃ 0) (Positive x) (Negative x) := by
  have : AA.OneOfThree (sgn x ≃ 0) (sgn x ≃ 1) (sgn x ≃ -1) :=
    Rational.sgn_trichotomy x
  have atLeastOne : AA.OneOfThree (x ≃ 0) (Positive x) (Negative x) :=
    this.map
      Rational.sgn_zero.mpr Rational.sgn_positive.mpr Rational.sgn_negative.mpr

  have : ¬AA.TwoOfThree (sgn x ≃ 0) (sgn x ≃ 1) (sgn x ≃ -1) :=
    Integer.signs_distinct
  have atMostOne : ¬AA.TwoOfThree (x ≃ 0) (Positive x) (Negative x) :=
    mt
      (AA.TwoOfThree.map
        Rational.sgn_zero.mp Rational.sgn_positive.mp Rational.sgn_negative.mp)
      this

  exact AA.ExactlyOneOfThree.mk atLeastOne atMostOne

-- Definition 4.2.8 (Ordering of the rationals).
-- [First, here are the axioms for the operators.]
example : ℚ → ℚ → Prop := Rational.lt -- [Less than.]
example : ℚ → ℚ → Prop := Rational.le -- [Less than or equivalent.]
-- [The "greater than" variants use `lt` and `le`, but with swapped arguments.]

-- [Here are the operator definitions.]
example : ℚ → ℚ → Prop := Rational.Impl.Generic.lt
example : ℚ → ℚ → Prop := Rational.Impl.Generic.le

-- Let `x` and `y` be rational numbers. We say that `x > y` iff `x - y` is a
-- positive rational number, and `x < y` iff `x - y` is a negative rational
-- number. We write `x ≥ y` iff either `x > y` or `x = y`, and similarly define
-- `x ≤ y`.
example {x y : ℚ} : x > y ↔ Positive (x - y) := by
  apply Iff.intro
  case mp =>
    intro (_ : x > y)
    show Positive (x - y)
    have : sgn (x - y) ≃ 1 := Rational.gt_sgn.mp ‹x > y›
    have : Positive (x - y) := Rational.sgn_positive.mpr this
    exact this
  case mpr =>
    intro (_ : Positive (x - y))
    show x > y
    have : sgn (x - y) ≃ 1 := Rational.sgn_positive.mp ‹Positive (x - y)›
    have : x > y := Rational.gt_sgn.mpr this
    exact this

example {x y : ℚ} : x < y ↔ Negative (x - y) := by
  apply Iff.intro
  case mp =>
    intro (_ : x < y)
    show Negative (x - y)
    have : sgn (x - y) ≃ -1 := Rational.lt_sgn.mp ‹x < y›
    have : Negative (x - y) := Rational.sgn_negative.mpr this
    exact this
  case mpr =>
    intro (_ : Negative (x - y))
    show x < y
    have : sgn (x - y) ≃ -1 := Rational.sgn_negative.mp ‹Negative (x - y)›
    have : x < y := Rational.lt_sgn.mpr this
    exact this

example {x y : ℚ} : x ≥ y ↔ x > y ∨ x ≃ y := Rational.ge_cases
example {x y : ℚ} : x ≤ y ↔ x < y ∨ x ≃ y := Rational.le_cases

-- Exercise 4.2.5.
-- Proposition 4.2.9 (Basic properties of order on the rationals).
-- Let `x`, `y`, `z` be rational numbers. Then the following properties hold.

-- (a) (Order trichotomy) Exactly one of the three statements `x ≃ y`, `x < y`,
-- or `x > y` is true.
example : ∀ (x y : ℚ), AA.ExactlyOneOfThree (x < y) (x ≃ y) (x > y) :=
  Rational.order_trichotomy

-- (b) (Order is anti-symmetric) One has `x < y` if and only if `y > x`.
-- [Note: This is trivial because `· > ·` is defined to be `· < ·` with swapped
-- arguments.]
example {x y : ℚ} : x < y ↔ y > x := Iff.intro id id

-- (c) (Order is transitive) If `x < y` and `y < z`, then `x < z`.
example {x y z : ℚ} : x < y → y < z → x < z := Rational.lt_trans

-- (d) (Addition preserves order) If `x < y`, then `x + z < y + z`.
example {x y z : ℚ} : x < y → x + z < y + z := Rational.lt_substL_add

-- (e) (Positive multiplication preserves order) If `x < y` and `z` is
-- positive, then `x * z < y * z`.
example {x y z : ℚ} : x < y → Positive z → x * z < y * z := by
  intro (_ : x < y) (_ : Positive z)
  show x * z < y * z
  have : sgn z ≃ 1 := Rational.sgn_positive.mp ‹Positive z›
  have : z > 0 := Rational.gt_zero_sgn.mpr this
  have : x * z < y * z := Rational.lt_substL_mul_pos this ‹x < y›
  exact this

-- Exercise 4.2.6.
-- Show that if `x`, `y`, `z` are rational numbers such that `x < y` and `z` is
-- _negative_, then `x * z > y * z`.
example {x y z : ℚ} : x < y → Negative z → x * z > y * z := by
  intro (_ : x < y) (_ : Negative z)
  show y * z < x * z
  have : sgn z ≃ -1 := Rational.sgn_negative.mp ‹Negative z›
  have : z < 0 := Rational.lt_zero_sgn.mpr this
  have : y * z < x * z := Rational.lt_substL_mul_neg this ‹x < y›
  exact this

end AnalysisI.Ch4.Sec2
