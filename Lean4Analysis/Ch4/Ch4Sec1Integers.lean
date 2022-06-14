import Lean4Axiomatic.Integer
import Lean4Axiomatic.Integer.Impl.Difference
import Lean4Axiomatic.Natural.Impl.Nat

open Lean4Axiomatic

namespace AnalysisI.Ch4.Sec1

abbrev ℕ : Type := Nat

namespace Impl

export Integer.Impl.Difference (
  addition equality from_prod from_prod_substitutive multiplication
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

end AnalysisI.Ch4.Sec1
