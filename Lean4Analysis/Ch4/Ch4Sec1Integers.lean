import Lean4Axiomatic.Integer
import Lean4Axiomatic.Integer.Impl.Difference
import Lean4Axiomatic.Natural.Impl.Nat

open Coe (coe)
open Lean4Axiomatic
open Signed (Negative Positive)

namespace AnalysisI.Ch4.Sec1

abbrev ℕ : Type := Nat

namespace Impl

export Integer.Impl.Difference (
  addition core from_prod from_prod_substitutive integer multiplication
  negation sign
)

end Impl

/- 4.1 The integers -/

-- Definition 4.1.1 (Integers).
-- An _integer_ is an expression of the form `a——b`, where `a` and `b` are
-- natural numbers. Two integers are considered to be equal, `a——b ≃ c——d`, if
-- and only if `a + d ≃ c + b`. We let `ℤ` denote the set of all integers.
abbrev ℤ : Type := Integer.Impl.Difference ℕ

example {a b : ℕ} : ℤ := a——b

-- [definition of the equality relation on ℤ]
example : ℤ → ℤ → Prop := Impl.core.eqvOp.tildeDash

example {a b c d : ℕ} : a——b ≃ c——d ↔ a + d ≃ c + b := Iff.intro id id

-- Thus for instance `3——5` is an integer, and is equal to `2——4`, because
-- `3 + 4 ≃ 2 + 5`.
example : 3——5 ≃ 2——4 := by
  show 3 + 4 ≃ 2 + 5
  exact Rel.refl

-- On the other hand, `3——5` is not equal to `2——3` because `3 + 3 ≄ 2 + 5`.
example : 3——5 ≄ 2——3 := by
  show 3 + 3 ≄ 2 + 5
  exact of_decide_eq_false (rfl : decide (3 + 3 ≃ 2 + 5) = false)

-- Exercise 4.1.1.
-- We have to check that this is a legitimate notion of equality. We need to
-- verify the reflexivity, symmetry, transitivity, and substitution axioms.
example {a : ℤ} : a ≃ a := Impl.core.eqvOp.refl

example {a b : ℤ} : a ≃ b → b ≃ a := Impl.core.eqvOp.symm

example {a b c : ℤ} : a ≃ b → b ≃ c → a ≃ c := Impl.core.eqvOp.trans

-- As for the substitution axiom, we cannot verify it at this stage because we
-- have not yet defined any operations on the integers. However, when we do
-- define our basic operations on the integers, such as addition,
-- multiplication, and order, we will have to verify the substitution axiom at
-- that time in order to ensure that the definition is valid.

-- Definition 4.1.2.
-- The sum of two integers, `(a——b) + (c——d)`, is defined by the formula
example {a b c d : ℕ} : a——b + c——d ≃ (a + c)——(b + d) := rfl

-- [definition of integer addition]
example : ℤ → ℤ → ℤ := Impl.addition.addOp.add

-- The product of two integers, `(a——b) * (c——d)`, is defined by
example {a b c d : ℕ} : a——b * c——d ≃ (a * c + b * d)——(a * d + b * c) := rfl

-- [definition of integer multiplication]
example : ℤ → ℤ → ℤ := Impl.multiplication.mulOp.mul

-- Thus for instance, `(3——5) + (1——4)` is equal to `(4——9)`.
example : (3——5) + (1——4) ≃ (4——9) := rfl

-- There is however one thing we have to check before we can accept these
-- definitions - we have to check that if we replace one of the integers by an
-- equal integer, that the sum or product does not change. For instance,
-- `(3——5)` is equal to `(2——4)`, so `(3——5) + (1——4)` ought to have the same
-- value as `(2——4) + (1——4)`, otherwise this would not give a consistent
-- definition of addition.
example : (3——5) ≃ (2——4) := rfl

example : (3——5) + (1——4) ≃ (2——4) + (1——4) := rfl

-- Lemma 4.1.3 (Addition and multiplication are well-defined).
-- Let `a`, `b`, `a'`, `b'`, `c`, `d` be natural numbers. If
-- `(a——b) ≃ (a'——b')`, then `(a——b) + (c——d) ≃ (a'——b') + (c——d)` and
-- `(a——b) * (c——d) ≃ (a'——b') * (c——d)`, and also
-- `(c——d) + (a——b) ≃ (c——d) + (a'——b')` and
-- `(c——d) * (a——b) ≃ (c——d) * (a'——b')`. Thus addition and multiplication are
-- well-defined operations (equal inputs give equal outputs).
section lemma_4_1_3

variable {a b a' b' c d : ℕ}
variable (_ : (a——b) ≃ (a'——b'))

example : (a——b) + (c——d) ≃ (a'——b') + (c——d) :=
  AA.substL
    (self := Impl.addition.add_substitutive.substitutiveL)
    ‹(a——b) ≃ (a'——b')›

example : (a——b) * (c——d) ≃ (a'——b') * (c——d) :=
  AA.substL
    (self := Impl.multiplication.mul_substitutive.substitutiveL)
    ‹(a——b) ≃ (a'——b')›

example : (c——d) + (a——b) ≃ (c——d) + (a'——b') :=
  AA.substR
    (self := Impl.addition.add_substitutive.substitutiveR)
    ‹(a——b) ≃ (a'——b')›

example : (c——d) * (a——b) ≃ (c——d) * (a'——b') :=
  AA.substR
    (self := Impl.multiplication.mul_substitutive.substitutiveR)
    ‹(a——b) ≃ (a'——b')›

end lemma_4_1_3

-- The integers `n——0` behave in the same way as the natural numbers `n`;
-- indeed one can check that `(n——0) + (m——0) ≃ (n + m)——0` and
-- `(n——0) * (m——0) ≃ (n * m)——0`.
example {n m : ℕ} : (n——0) + (m——0) ≃ (n + m)——0 :=
  let inst := Impl.addition.add_compatible_from_natural
  Rel.symm (AA.compat₂ (self := inst))

example {n m : ℕ} : (n——0) * (m——0) ≃ (n * m)——0 :=
  let inst := Impl.multiplication.mul_compatible_from_natural
  Rel.symm (AA.compat₂ (self := inst))

-- Furthermore, `(n——0)` is equal to `(m——0)` if and only if `n ≃ m`.
example {n m : ℕ} : (n——0) ≃ (m——0) ↔ n ≃ m := by
  apply Iff.intro
  case mp =>
    intro (_ : n——0 ≃ m——0)
    show n ≃ m
    have : n + 0 ≃ m + 0 := ‹n——0 ≃ m——0›
    exact AA.cancelR ‹n + 0 ≃ m + 0›
  case mpr =>
    intro (_ : n ≃ m)
    show n——0 ≃ m——0
    show n + 0 ≃ m + 0
    exact AA.substL ‹n ≃ m›

-- Thus we may _identify_ the natural numbers with integers by setting
-- `n ≡ n——0`; this does not affect our definitions of addition or
-- multiplication or equality since they are consistent with each other.
-- [Note: In Lean, the left- and right-hand sides of an equivalence must be the
-- same type, so we can't follow the book exactly here. However, we can define
-- a _coercion_ that converts natural numbers to integers, and use that to
-- demonstrate equivalence.]
example {n : ℕ} : coe n ≃ n——0 := rfl

-- For instance the natural number `3` is now considered to be the same as the
-- integer `3——0`, thus `3 ≃ 3——0`.
example : 3 ≃ 3——0 := rfl

-- In particular `0` is equal to `0——0` and `1` is equal to `1——0`.
example : 0 ≃ 0——0 := rfl
example : 1 ≃ 1——0 := rfl

-- Of course, if we set `n` equal to `n——0`, then it will also be equal to any
-- other integer which is equal to `n——0`, for instance `3` is equal not only
-- to `3——0`, but also to `4——1`, `5——2`, etc.
example : 3 ≃ 4——1 := rfl
example : 3 ≃ 5——2 := rfl

-- We can now define incrementation on the integers by defining
-- `step x := x + 1` for any integer `x`; this is of course consistent with our
-- definition of the increment operation for natural numbers. However, this is
-- no longer an important operation for us, as it has now been superceded by
-- the more general notion of addition.
def step (x : ℤ) := x + 1
example {n : ℕ} : step (coe n) ≃ coe (Natural.step n) := rfl

-- Definition 4.1.4 (Negation of integers).
-- If `(a——b)` is an integer, we define the negation `-(a——b)` to be the
-- integer `(b——a)`.
example {a b : ℕ} : -(a——b) ≃ (b——a) := rfl

-- [definition of integer negation]
example : ℤ → ℤ := Impl.negation.negOp.neg

-- In particular if `n ≃ n——0` is a positive natural number, we can define its
-- negation `-n ≃ 0——n`.
example {n : ℕ} : -(coe n) ≃ 0——n := rfl

-- For instance `-(3——5) ≃ (5——3)`.
example : -(3——5) ≃ 5——3 := rfl

-- Exercise 4.1.2.
-- One can check this definition is well-defined.
example {a b a' b' : ℕ} : a——b ≃ a'——b' → -(a——b) ≃ -(a'——b') :=
  AA.subst₁ (self := Impl.negation.neg_substitutive)

-- Lemma 4.1.5 (Trichotomy of integers).
-- Let `x` be an integer. Then exactly one of the following three statements is
-- true: (a) `x` is zero; (b) `x` is equal to a positive natural number `n`; or
-- (c) `x` is the negation `-n` of a positive natural number `n`.
theorem pos_iff_ex
    {x : ℤ} : Positive x ↔ ∃ (n : ℕ), Positive n ∧ x ≃ coe n
    := by
  -- Explicitly add instance to scope to help resolve `AA.identL` calls below
  have mul_ident := Impl.multiplication.mul_identity (ℕ := ℕ)
  apply Iff.intro
  case mp =>
    intro (_ : Positive x)
    show ∃ (n : ℕ), Positive n ∧ x ≃ coe n
    have (Integer.SignedMagnitude.intro
          (n : ℕ) (_ : Positive n) (_ : x ≃ 1 * coe n)) :=
      Impl.sign.positive_defn.mp ‹Positive x›
    exists n
    apply And.intro ‹Positive n›
    show x ≃ coe n
    exact Rel.trans ‹x ≃ 1 * coe n› AA.identL
  case mpr =>
    intro (Exists.intro (n : ℕ) (And.intro (_ : Positive n) (_ : x ≃ coe n)))
    show Positive x
    apply Impl.sign.positive_defn.mpr
    show Integer.SignedMagnitude x Integer.sqrt1_one
    apply Integer.SignedMagnitude.intro n ‹Positive n›
    show x ≃ 1 * coe n
    exact Rel.trans ‹x ≃ coe n› (Rel.symm AA.identL)

theorem neg_iff_ex
    {x : ℤ} : Negative x ↔ ∃ (n : ℕ), Positive n ∧ x ≃ -(coe n)
    := by
  apply Iff.intro
  case mp =>
    intro (_ : Negative x)
    show ∃ (n : ℕ), Positive n ∧ x ≃ -(coe n)
    have (Integer.SignedMagnitude.intro
          (n : ℕ) (_ : Positive n) (_ : x ≃ -1 * coe n)) :=
      Impl.sign.negative_defn.mp ‹Negative x›
    exists n
    apply And.intro ‹Positive n›
    show x ≃ -(coe n)
    exact Rel.trans ‹x ≃ -1 * coe n› Integer.mul_neg_one
  case mpr =>
    intro
      (Exists.intro (n : ℕ) (And.intro (_ : Positive n) (_ : x ≃ -(coe n))))
    show Negative x
    apply Impl.sign.negative_defn.mpr
    show Integer.SignedMagnitude x Integer.sqrt1_neg_one
    apply Integer.SignedMagnitude.intro n ‹Positive n›
    show x ≃ -1 * coe n
    exact Rel.trans ‹x ≃ -(coe n)› (Rel.symm Integer.mul_neg_one)

example
    : (x : ℤ) →
    AA.ExactlyOneOfThree
      (x ≃ 0)
      (∃ (n : ℕ), Positive n ∧ x ≃ coe n)
      (∃ (n : ℕ), Positive n ∧ x ≃ -(coe n))
    := by
  intro (x : ℤ)
  have tri : AA.ExactlyOneOfThree (x ≃ 0) (Positive x) (Negative x) :=
    Signed.trichotomy x
  apply AA.ExactlyOneOfThree.mk
  case atLeastOne =>
    show AA.OneOfThree
      (x ≃ 0)
      (∃ (n : ℕ), Positive n ∧ x ≃ coe n)
      (∃ (n : ℕ), Positive n ∧ x ≃ -(coe n))
    match tri.atLeastOne with
    | AA.OneOfThree.first (_ : x ≃ 0) =>
      exact AA.OneOfThree.first ‹x ≃ 0›
    | AA.OneOfThree.second (_ : Positive x) =>
      exact AA.OneOfThree.second (pos_iff_ex.mp ‹Positive x›)
    | AA.OneOfThree.third (_ : Negative x) =>
      exact AA.OneOfThree.third (neg_iff_ex.mp ‹Negative x›)
  case atMostOne =>
    intro
      (h : AA.TwoOfThree
        (x ≃ 0)
        (∃ (n : ℕ), Positive n ∧ x ≃ coe n)
        (∃ (n : ℕ), Positive n ∧ x ≃ -(coe n)))
    show False
    apply tri.atMostOne
    show AA.TwoOfThree (x ≃ 0) (Positive x) (Negative x)
    match h with
    | AA.TwoOfThree.oneAndTwo
        (_ : x ≃ 0) (_ : ∃ (n : ℕ), Positive n ∧ x ≃ coe n) =>
      have : Positive x := pos_iff_ex.mpr ‹∃ (n : ℕ), Positive n ∧ x ≃ coe n›
      exact AA.TwoOfThree.oneAndTwo ‹x ≃ 0› ‹Positive x›
    | AA.TwoOfThree.oneAndThree
        (_ : x ≃ 0) (_ : ∃ (n : ℕ), Positive n ∧ x ≃ -(coe n)) =>
      have : Negative x :=
        neg_iff_ex.mpr ‹∃ (n : ℕ), Positive n ∧ x ≃ -(coe n)›
      exact AA.TwoOfThree.oneAndThree ‹x ≃ 0› ‹Negative x›
    | AA.TwoOfThree.twoAndThree
        (_ : ∃ (n : ℕ), Positive n ∧ x ≃ coe n)
        (_ : ∃ (n : ℕ), Positive n ∧ x ≃ -(coe n)) =>
      have : Positive x := pos_iff_ex.mpr ‹∃ (n : ℕ), Positive n ∧ x ≃ coe n›
      have : Negative x :=
        neg_iff_ex.mpr ‹∃ (n : ℕ), Positive n ∧ x ≃ -(coe n)›
      exact AA.TwoOfThree.twoAndThree ‹Positive x› ‹Negative x›

-- Exercise 4.1.4.
-- Proposition 4.1.6 (Laws of algebra for integers).
-- Let `x`, `y`, `z` be integers. Then we have:
section proposition_4_1_6

variable {x y z : ℤ}

example : x + y ≃ y + x := AA.comm (self := Impl.addition.add_commutative)

example : (x + y) + z ≃ x + (y + z) :=
  AA.assoc (self := Impl.addition.add_associative)

example : x + 0 ≃ x := AA.identR (self := Impl.addition.add_identity.identityR)

example : 0 + x ≃ x := AA.identL (self := Impl.addition.add_identity.identityL)

example : x + (-x) ≃ 0 :=
  AA.inverseR (self := Impl.negation.neg_inverse.inverseR)

example : (-x) + x ≃ 0 :=
  AA.inverseL (self := Impl.negation.neg_inverse.inverseL)

example : x * y ≃ y * x :=
  AA.comm (self := Impl.multiplication.mul_commutative)

example : (x * y) * z ≃ x * (y * z) :=
  AA.assoc (self := Impl.multiplication.mul_associative)

example : x * 1 ≃ x :=
  AA.identR (self := Impl.multiplication.mul_identity.identityR)

example : 1 * x ≃ x :=
  AA.identL (self := Impl.multiplication.mul_identity.identityL)

example : x * (y + z) ≃ x * y + x * z :=
  AA.distribL (self := Impl.multiplication.mul_distributive.distributiveL)

example : (y + z) * x ≃ y * x + z * x :=
  AA.distribR (self := Impl.multiplication.mul_distributive.distributiveR)

end proposition_4_1_6

-- We now define the operation of _subtraction_ `x - y` of two integers by the
-- formula `x - y := x + (-y)`.
example {x y : ℤ} : x - y ≃ x + (-y) := Integer.sub_defn

-- [Definition of subtraction.]
example : ℤ → ℤ → ℤ := Impl.integer.toSubtraction.subOp.sub

-- We do not need to verify the substitution axiom for this operation, since we
-- have defined subtraction in terms of two other operations on integers,
-- namely addition and negation, and we have already verified that those
-- operations are well-defined.
-- [Note: What Tao really means here is that the proof of the substitution
-- axiom is too trivial to bother with; his explanation is essentially the
-- proof. We don't have the luxury of hand-waving with Lean, so we have to show
-- it explicitly.]
example {x₁ x₂ y : ℤ} : x₁ ≃ x₂ → x₁ - y ≃ x₂ - y :=
  AA.substL (self := Integer.sub_substitutive.substitutiveL)

example {x₁ x₂ y : ℤ} : x₁ ≃ x₂ → y - x₁ ≃ y - x₂ :=
  AA.substR (self := Integer.sub_substitutive.substitutiveR)

-- One can easily check now that if `a` and `b` are natural numbers, then
example {a b : ℕ} : coe a - coe b ≃ a——b := calc
  coe a - (coe b : ℤ)           ≃ _ := Rel.refl
  coe a + -(coe b : ℤ)          ≃ _ := Rel.refl
  (a——0) + (0——b)               ≃ _ := Rel.refl
  (a + 0)——(0 + b)              ≃ _ := Rel.refl
  Impl.from_prod (a + 0, 0 + b) ≃ _ := AA.subst₁ (AA.substL AA.identR)
  Impl.from_prod (a, 0 + b)     ≃ _ := AA.subst₁ (AA.substR AA.identL)
  Impl.from_prod (a, b)         ≃ _ := Rel.refl
  a——b                          ≃ _ := Rel.refl
-- and so `a——b` is just the same thing as `a - b`. Because of this we can now
-- discard the `(· —— ·)` notation, and use the familiar operation of
-- subtraction instead.

-- We can now generalize Lemma 2.3.3 and Corollary 2.3.7 from the natural
-- numbers to the integers:

-- Exercise 4.1.5.
-- Proposition 4.1.8 (Integers have no zero divisors).
-- Let `a` and `b` be integers such that `a * b ≃ 0`. Then either `a ≃ 0` or
-- `b ≃ 0` (or both).
example {a b : ℤ} : a * b ≃ 0 → a ≃ 0 ∨ b ≃ 0 := Integer.mul_split_zero.mp

-- Exercise 4.1.6.
-- Corollary 4.1.9 (Cancellation law for integers).
-- If `a`, `b`, `c` are integers such that `a * c ≃ b * c` and `c` is non-zero,
-- then `a ≃ b`.
example {a b c : ℤ} : a * c ≃ b * c → c ≄ 0 → a ≃ b := by
  intro (_ : a * c ≃ b * c) (_ : c ≄ 0)
  let inst := Integer.mul_cancellative.cancellativeR
  exact AA.cancelRC (self := inst) ‹c ≄ 0› ‹a * c ≃ b * c›

-- We now extend the notion of order, which was defined on the natural numbers,
-- to the integers by repeating the definition verbatim:

-- Definition 4.1.10 (Ordering of the integers).
-- Let `n` and `m` be integers. We say that `n` is _greater than or equal to_
-- `m`, and write `n ≥ m` or `m ≤ n`, iff we have `n ≃ m + a` for some natural
-- number `a`. We say that `n` is _strictly greater than_ `m`, and write
-- `n > m` or `m < n`, iff `n ≥ m` and `n ≄ m`.
example : ℤ → ℤ → Prop := LE.le (self := Integer.leOp ℕ)
example {n m : ℤ} : n ≥ m ↔ ∃ a : ℕ, n ≃ m + a := Integer.le_iff_add_nat

example : ℤ → ℤ → Prop := LT.lt (self := Integer.ltOp ℕ)
theorem gt_iff_ge_neqv {n m : ℤ} : n > m ↔ n ≥ m ∧ n ≄ m := by
  apply Iff.intro
  case mp =>
    intro (_ : n > m)
    show n ≥ m ∧ n ≄ m
    have (And.intro (_ : n ≥ m) (_ : m ≄ n)) :=
      Integer.lt_iff_le_neqv.mp ‹n > m›
    have : n ≄ m := Rel.symm ‹m ≄ n›
    exact And.intro ‹n ≥ m› ‹n ≄ m›
  case mpr =>
    intro (And.intro (_ : n ≥ m) (_ : n ≄ m))
    show n > m
    apply Integer.lt_iff_le_neqv.mpr
    show n ≥ m ∧ m ≄ n
    have : m ≄ n := Rel.symm ‹n ≄ m›
    exact And.intro ‹n ≥ m› ‹m ≄ n›

-- Thus for instance `5 > -3`, because `5 ≃ -3 + 8` and `5 ≄ -3`.
example : (5 : ℤ) > -3 := by
  show (5 : ℤ) > -3
  apply gt_iff_ge_neqv.mpr
  show (5 : ℤ) ≥ -3 ∧ 5 ≄ -3
  apply And.intro
  case left =>
    show (5 : ℤ) ≥ -3
    apply Integer.le_iff_add_nat.mpr
    show ∃ k : ℕ, 5 ≃ -3 + coe k
    apply Exists.intro 8
    show 5 ≃ -3 + coe 8
    show 5——0 ≃ 0——3 + 8——0
    show 5——0 ≃ 8——3
    show 5 + 3 ≃ 8 + 0
    show 8 ≃ 8
    exact Rel.refl
  case right =>
    show (5 : ℤ) ≄ -3
    intro (_ : (5 : ℤ) ≃ -3)
    show False
    have : 5——0 ≃ 0——3 := ‹(5 : ℤ) ≃ -3›
    have : 5 + 3 ≃ 0 + 0 := this
    have : 8 ≃ 0 := this
    exact absurd ‹8 ≃ 0› Natural.step_neq_zero

-- Lemma 4.1.11 (Properties of order).
-- Let `a`, `b`, `c` be integers.
section lemma_4_1_11

variable {a b c : ℤ}

-- (a) `a > b` if and only if `a - b` is a positive natural number.
example : a > b ↔ Positive (a - b) := Integer.gt_iff_pos_diff

end lemma_4_1_11

end AnalysisI.Ch4.Sec1
