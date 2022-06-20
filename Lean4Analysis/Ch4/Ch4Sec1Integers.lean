import Lean4Axiomatic.Integer
import Lean4Axiomatic.Integer.Impl.Difference
import Lean4Axiomatic.Natural.Impl.Nat

open Lean4Axiomatic

namespace AnalysisI.Ch4.Sec1

abbrev ℕ : Type := Nat

namespace Impl

export Integer.Impl.Difference (
  addition equality from_prod from_prod_substitutive multiplication negation
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
example : ℤ → ℤ → Prop := Impl.equality.eqvOp.tildeDash

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
example {a : ℤ} : a ≃ a := Impl.equality.eqvOp.refl

example {a b : ℤ} : a ≃ b → b ≃ a := Impl.equality.eqvOp.symm

example {a b c : ℤ} : a ≃ b → b ≃ c → a ≃ c := Impl.equality.eqvOp.trans

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
example {n m : ℕ} : (n——0) + (m——0) ≃ (n + m)——0 := rfl

example {n m : ℕ} : (n——0) * (m——0) ≃ (n * m)——0 := by
  show (n * m + 0 * 0)——(n * 0 + 0 * m) ≃ (n * m)——0
  show Impl.from_prod (n * m + 0 * 0, n * 0 + 0 * m) ≃ Impl.from_prod (n * m, 0)
  apply AA.subst₁ (self := Impl.from_prod_substitutive)
  show (n * m + 0 * 0, n * 0 + 0 * m) ≃ (n * m, 0)
  calc
    (n * m + 0 * 0, n * 0 + 0 * m) ≃ _ := AA.substL (AA.substR Natural.zero_mul)
    (n * m + 0, n * 0 + 0 * m)     ≃ _ := AA.substL Natural.add_zero
    (n * m, n * 0 + 0 * m)         ≃ _ := AA.substR (AA.substL Natural.mul_zero)
    (n * m, 0 + 0 * m)             ≃ _ := AA.substR Natural.zero_add
    (n * m, 0 * m)                 ≃ _ := AA.substR Natural.zero_mul
    (n * m, 0)                     ≃ _ := Rel.refl

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
example {n : ℕ} : ↑n ≃ n——0 := rfl

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
example {n : ℕ} : step ↑n ≃ ↑(Natural.step n) := rfl

-- Definition 4.1.4 (Negation of integers).
-- If `(a——b)` is an integer, we define the negation `-(a——b)` to be the
-- integer `(b——a)`.
example {a b : ℕ} : -(a——b) ≃ (b——a) := rfl

-- [definition of integer negation]
example : ℤ → ℤ := Impl.negation.negOp.neg

-- In particular if `n ≃ n——0` is a positive natural number, we can define its
-- negation `-n ≃ 0——n`.
example {n : ℕ} : -↑n ≃ 0——n := rfl

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
example {x : ℤ}
    : AA.ExactlyOneOfThree
      (x ≃ 0)
      (∃ (n : ℕ), Natural.Positive n ∧ x ≃ n)
      (∃ (n : ℕ), Natural.Positive n ∧ x ≃ -n)
    :=
  Impl.negation.trichotomy

end AnalysisI.Ch4.Sec1
