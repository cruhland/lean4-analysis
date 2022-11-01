import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Natural
import Lean4Axiomatic.Natural.Impl.Nat
import Lean4Axiomatic.Operators
import Lean4Axiomatic.Relation.Equivalence

open Lean4Axiomatic
open Natural (step)
open Operators (TildeDash)
open Signed (Positive)

namespace AnalysisI.Ch2

namespace Impl

export Natural.Impl.Generic (order sign)
export Natural.Impl.Nat (
  addition axioms constructors core equality exponentiation literals
  multiplication
)

end Impl

/-= Chapter 2: Starting at the beginning: the natural numbers =-/

/- 2.1 The Peano axioms -/

-- We call `ℕ` the _set of natural numbers_.
abbrev ℕ : Type := Nat

-- Axiom 2.1.
-- `0` is a natural number.
example : ℕ := 0

-- Axiom 2.2.
-- If `n` is a natural number, then `step n` is also a natural number.
example {n : ℕ} : ℕ := step n (self := Impl.constructors)

-- Thus for instance, from Axiom 2.1 and two applications of Axiom 2.2, we see
-- that `step (step 0)` is a natural number.
example : ℕ := step (step 0)

-- [values of `ℕ` obey the axioms of equality]
example : Relation.Equivalence.EqvOp? ℕ :=
  Natural.eqvOp? (self := Impl.equality)

-- [`step` obeys substitution]
example {n₁ n₂ : ℕ} : n₁ ≃ n₂ → step n₁ ≃ step n₂ :=
  AA.subst₁
    (self := Natural.step_substitutive (self := Impl.core))

-- Definition 2.1.3.
-- We define `1` to be the number `step 0`,
example : 1 ≃ step 0 := Rel.refl

-- `2` to be the number `step (step 0)`,
example : 2 ≃ step (step 0) := Rel.refl

-- `3` to be the number `step (step (step 0))`,
example : 3 ≃ step (step (step 0)) := Rel.refl

-- etc.
-- [We can convert any natural number literal (`Nat`) into `ℕ`]
example (n : Nat) : ℕ :=
  OfNat.ofNat n (self := Natural.literal (self := Impl.literals))

-- (In other words, `1 := step 0`, `2 := step 1`, `3 := step 2`, etc.)
example : 1 ≃ step 0 := Rel.refl
example : 2 ≃ step 1 := Rel.refl
example : 3 ≃ step 2 := Rel.refl

-- Proposition 2.1.4.
-- `3` is a natural number.
-- [The proof is given above; `3 ≃ step (step (step 0))`]
example : ℕ := 3

-- Axiom 2.3.
-- `0` is not the successor of any natural number; i.e., we have `step n ≄ 0`
-- for every natural number `n`.
example {n : ℕ} : step n ≄ 0 :=
  Natural.step_neqv_zero (self := Impl.axioms)

-- Proposition 2.1.6.
-- `4` is not equal to `0`.
example : 4 ≄ 0 := Natural.step_neqv_zero (ℕ := ℕ)

-- Axiom 2.4.
-- Different natural numbers must have different successors; i.e., if `n`, `m`
-- are natural numbers and `n ≄ m`, then `step n ≄ step m`. Equivalently, if
-- `step n ≃ step m`, then we must have `n ≃ m`.
example {n m : ℕ} : step n ≃ step m → n ≃ m :=
  AA.inject (self := Natural.step_injective (self := Impl.axioms))

-- Proposition 2.1.8.
-- `6` is not equal to `2`.
example : 6 ≄ 2 := by
  intro (_ : 6 ≃ 2)
  show False
  have : step 5 ≃ step 1 := ‹6 ≃ 2›
  have : 5 ≃ 1           := AA.inject this
  have : step 4 ≃ step 0 := this
  have : 4 ≃ 0           := AA.inject this
  have : step 3 ≃ 0      := this
  exact absurd ‹step 3 ≃ 0› Natural.step_neqv_zero

-- Axiom 2.5 (Principle of mathematical induction).
-- Let `P n` be any property pertaining to a natural number `n`. Suppose that
-- `P 0` is true, and suppose that whenever `P n` is true, `P (step n)` is also
-- true. Then `P n` is true for every natural number `n`.
example (P : ℕ → Prop) : P 0 → (∀ n, P n → P (step n)) → ∀ n, P n :=
  Natural.ind (self := Impl.axioms)

-- Proposition 2.1.16 (Recursive definitions).
-- Suppose for each natural number `n`, we have some function `f n : ℕ → ℕ`
-- from the natural numbers to the natural numbers. Let `c` be a natural
-- number. Then we can assign a unique natural number `a n` to each natural
-- number `n`, such that `a 0 ≃ c` and `a (step n) ≃ f n (a n)` for each
-- natural number `n`.
-- [The book only gives an informal proof here, and I'm not completely sure how
-- to formalize it in the right way. An exercise in Chapter 3 asks for the
-- rigorous proof, once functions have been given an exact definition. So I
-- will postpone the formal proof until then. For now, here's my translation of
-- the statement.]
#check {f : ℕ → ℕ → ℕ} → {c : ℕ} →
  ∃ a : ℕ → ℕ, a 0 ≃ c ∧ ∀ n, a (step n) ≃ f n (a n)

/- 2.2 Addition -/

-- Definition 2.2.1 (Addition of natural numbers).
-- Let `m` be a natural number. To add zero to `m`, we define `0 + m := m`. Now
-- suppose inductively that we have defined how to add `n` to `m`. Then we can
-- add `step n` to `m` by defining `step n + m := step (n + m)`.
example : ℕ → ℕ → ℕ := Add.add (self := Natural.addOp (self := Impl.addition))

example {m : ℕ} : 0 + m ≃ m := Natural.zero_add (self := Impl.addition)

example {n m : ℕ} : step n + m ≃ step (n + m) :=
  Natural.step_add (self := Impl.addition)

-- [Addition obeys left and right substitution]
example : AA.Substitutive₂ (α := ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·) :=
  Natural.add_substitutive

-- Thus `0 + m` is `m`,
example {m : ℕ} : 0 + m ≃ m := Natural.zero_add

-- `1 + m ≃ step 0 + m` is `step m`;
theorem one_plus_m {m : ℕ} : 1 + m ≃ step m := by
  calc
    _ ≃ 1 + m        := Rel.refl
    _ ≃ step 0 + m   := AA.substL Rel.refl
    _ ≃ step (0 + m) := Natural.step_add
    _ ≃ step m       := AA.subst₁ Natural.zero_add

-- `2 + m ≃ step 1 + m ≃ step (step m)`;
example {m : ℕ} : 2 + m ≃ step (step m) := by
  calc
    _ ≃ 2 + m         := Rel.refl
    _ ≃ step 1 + m    := AA.substL Rel.refl
    _ ≃ step (1 + m)  := Natural.step_add
    _ ≃ step (step m) := AA.subst₁ one_plus_m

-- and so forth; for instance we have `2 + 3 ≃ step (step 3) ≃ step 4 ≃ 5`.
example : 2 + 3 ≃ 5 := by
  calc
    _ ≃ 2 + 3               := Rel.refl
    _ ≃ step 1 + 3          := AA.substL (α := ℕ) Rel.refl
    _ ≃ step (1 + 3)        := Natural.step_add
    _ ≃ step (step 0 + 3)   := AA.subst₁ (AA.substL Rel.refl)
    _ ≃ step (step (0 + 3)) := AA.subst₁ Natural.step_add
    _ ≃ step (step 3)       := AA.subst₁ (AA.subst₁ Natural.zero_add)
    _ ≃ step 4              := Rel.refl
    _ ≃ 5                   := Rel.refl

-- Note that this definition is asymmetric: `3 + 5` is incrementing `5` three
-- times, while `5 + 3` is incrementing `3` five times. Of course, they both
-- yield the same value of `8`.
example : 3 + 5 ≃ 8 := by
  let zero_add : {m : ℕ} → 0 + m ≃ m := Natural.zero_add
  let step_add : {n m : ℕ} → step n + m ≃ step (n + m) := Natural.step_add
  calc
    _ ≃ 3 + 5                      := Rel.refl
    _ ≃ step (2 + 5)               := step_add
    _ ≃ step (step (1 + 5))        := AA.subst₁ step_add
    _ ≃ step (step (step (0 + 5))) := AA.subst₁ (AA.subst₁ step_add)
    _ ≃ step (step (step 5))       := AA.subst₁ (AA.subst₁ (AA.subst₁ zero_add))
    _ ≃ 8                          := Rel.refl

example : 5 + 3 ≃ 8 := by
  let ss {n₁ n₂ : ℕ} : n₁ ≃ n₂ → step n₁ ≃ step n₂ := AA.subst₁
  let za : {m : ℕ} → 0 + m ≃ m := Natural.zero_add
  let sa : {n m : ℕ} → step n + m ≃ step (n + m) := Natural.step_add
  calc
    _ ≃ 5 + 3                                    := Rel.refl
    _ ≃ step (4 + 3)                             := sa
    _ ≃ step (step (3 + 3))                      := ss sa
    _ ≃ step (step (step (2 + 3)))               := ss (ss sa)
    _ ≃ step (step (step (step (1 + 3))))        := ss (ss (ss sa))
    _ ≃ step (step (step (step (step (0 + 3))))) := ss (ss (ss (ss sa)))
    _ ≃ step (step (step (step (step 3))))       := ss (ss (ss (ss (ss za))))
    _ ≃ 8                                        := Rel.refl

-- Lemma 2.2.2.
-- For any natural number `n`, `n + 0 ≃ n`.
example {n : ℕ} : n + 0 ≃ n := Natural.add_zero

-- Lemma 2.2.3.
-- For any natural numbers `n` and `m`, `n + step m ≃ step (n + m)`.
example {n m : ℕ} : n + step m ≃ step (n + m) := Natural.add_step

-- As a particular corollary of Lemma 2.2.2 and Lemma 2.2.3 we see that
-- `step n ≃ n + 1`.
example {n : ℕ} : step n ≃ n + 1 := Rel.symm Natural.add_one_step

-- Proposition 2.2.4 (Addition is commutative).
-- For any natural numbers `n` and `m`, `n + m ≃ m + n`.
example {n m : ℕ} : n + m ≃ m + n := AA.comm (self := Natural.add_commutative)

-- Exercise 2.2.1.
-- Proposition 2.2.5 (Addition is associative).
-- For any natural numbers `a`, `b`, `c`, we have `(a + b) + c ≃ a + (b + c)`.
example {a b c : ℕ} : (a + b) + c ≃ a + (b + c) :=
  AA.assoc (self := Natural.add_associative)

-- Proposition 2.2.6 (Cancellation law).
-- Let `a`, `b`, `c` be natural numbers such that `a + b ≃ a + c`. Then we have
-- `b ≃ c`.
example {a b c : ℕ} : a + b ≃ a + c → b ≃ c :=
  AA.cancelL (self := Natural.add_cancellative.cancellativeL)

-- Definition 2.2.7 (Positive natural numbers).
-- A natural number `n` is said to be _positive_ iff it is not equal to `0`.
example : ℕ → Prop := Positive (self := Impl.sign.positivity.toOps)
example {n : ℕ} : Positive n ↔ n ≄ 0 :=
  Signed.positive_defn (self := Impl.sign.positivity)

-- Proposition 2.2.8.
-- If `a` is positive and `b` is a natural number, then `a + b` is positive.
example {a b : ℕ} : Positive a → Positive (a + b) := Natural.positive_add

-- Corollary 2.2.9.
-- If `a` and `b` are natural numbers such that `a + b ≃ 0`,
-- then `a ≃ 0` and `b ≃ 0`.
example {a b : ℕ} : a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0 := Natural.zero_sum_split

-- Exercise 2.2.2.
-- Lemma 2.2.10.
-- Let `a` be a positive number. Then there exists exactly one natural number
-- `b` such that `step b ≃ a`.
example {a : ℕ}
    : Positive a → ∃ b : ℕ, step b ≃ a ∧ ∀ b' : ℕ, step b' ≃ a → b ≃ b' := by
  intro (_ : Positive a)
  show ∃ b, step b ≃ a ∧ ∀ b', step b' ≃ a → b ≃ b'
  have ⟨b, (_ : step b ≃ a)⟩ := Natural.positive_step ‹Positive a›
  exists b
  apply And.intro ‹step b ≃ a›
  intro b' (_ : step b' ≃ a)
  show b ≃ b'
  apply AA.inject (β := ℕ) (f := step) (rβ := (· ≃ ·))
  show step b ≃ step b'
  calc
    _ ≃ step b  := Rel.refl
    _ ≃ a       := ‹step b ≃ a›
    _ ≃ step b' := Rel.symm ‹step b' ≃ a›

-- Definition 2.2.11 (Ordering of the natural numbers).
-- Let `n` and `m` be natural numbers. We say that `n` is
-- _greater than or equal to_ `m`, and write `n ≥ m` or `m ≤ n`, iff we have
-- `n ≃ m + a` for some natural number `a`.
example : ℕ → ℕ → Prop :=
  @GE.ge ℕ (Natural.leOp (self := Impl.order))
example {n m : ℕ} : n ≥ m ↔ ∃ a : ℕ, n ≃ m + a := by
  let le_defn := @Natural.le_defn (ℕ := ℕ) (self := Impl.order)
  apply Iff.intro
  · intro (_ : m ≤ n)
    show ∃ a, n ≃ m + a
    have ⟨a, (_ : m + a ≃ n)⟩ := le_defn.mp ‹m ≤ n›
    exact ⟨a, Rel.symm ‹m + a ≃ n›⟩
  · intro ⟨a, (_ : n ≃ m + a)⟩
    show m ≤ n
    exact le_defn.mpr ⟨a, Rel.symm ‹n ≃ m + a›⟩

-- We say that `n` is _strictly greater than_ `m`, and write `n > m` or
-- `m < n`, iff `n ≥ m` and `n ≄ m`.
example : ℕ → ℕ → Prop :=
  @GT.gt ℕ (Natural.ltOp (self := Impl.order))
example {n m : ℕ} : n > m ↔ n ≥ m ∧ n ≄ m := by
  let lt_defn := @Natural.lt_defn (ℕ := ℕ) (self := Impl.order)
  apply Iff.intro
  · intro (_ : n > m)
    show n ≥ m ∧ n ≄ m
    have ⟨(_ : m ≤ n), (_ : m ≄ n)⟩ := lt_defn.mp ‹m < n›
    exact ⟨‹n ≥ m›, Rel.symm ‹m ≄ n›⟩
  · intro ⟨(_ : n ≥ m), (_ : n ≄ m)⟩
    show n > m
    have : m < n := lt_defn.mpr ⟨‹m ≤ n›, Rel.symm ‹n ≄ m›⟩
    exact ‹n > m›

-- Thus for instance `8 > 5`, because `8 ≃ 5 + 3` and `8 ≄ 5`.
example : 8 > 5 := by
  show 5 < 8
  apply Natural.lt_defn.mpr
  apply And.intro
  · show 5 ≤ 8
    apply Natural.le_defn.mpr
    apply Exists.intro (3 : ℕ)
    apply of_decide_eq_true
    rfl
  · show 5 ≄ 8
    apply of_decide_eq_false
    rfl

-- Also note that `step n > n` for any `n`
example {n : ℕ} : step n > n := Natural.lt_step

-- Exercise 2.2.3.
-- Proposition 2.2.12 (Basic properties of order for natural numbers).
-- Let `a`, `b`, `c` be natural numbers. Then
-- (a) (Order is reflexive) `a ≥ a`.
example {a : ℕ} : a ≥ a := Rel.refl (self := Natural.le_reflexive)

-- (b) (Order is transitive) If `a ≥ b` and `b ≥ c`, then `a ≥ c`.
example {a b c : ℕ} : a ≥ b → b ≥ c → a ≥ c :=
  flip (Rel.trans (self := Natural.le_transitive))

-- (c) (Order is anti-symmetric) If `a ≥ b` and `b ≥ a`, then `a ≃ b`.
example {a b : ℕ} : a ≥ b → b ≥ a → a ≃ b := flip Natural.le_antisymm

-- (d) (Addition preserves order) `a ≥ b` if and only if `a + c ≥ b + c`.
example {a b c : ℕ} : a ≥ b ↔ a + c ≥ b + c := by
  apply Iff.intro
  · intro (_ : b ≤ a)
    show b + c ≤ a + c
    exact AA.substL ‹b ≤ a›
  · intro (_ : b + c ≤ a + c)
    show b ≤ a
    exact AA.cancelR ‹b + c ≤ a + c›

-- (e) `a < b` if and only if `step a ≤ b`.
example {a b : ℕ} : a < b ↔ step a ≤ b := Natural.lt_step_le

-- (f) `a < b` if and only if `b ≃ a + d` for some _positive_ number `d`.
example {a b : ℕ} : a < b ↔ ∃ d, Positive d ∧ b ≃ a + d := Natural.lt_defn_add

-- Exercise 2.2.4.
-- Proposition 2.2.13 (Trichotomy of order for natural numbers).
-- Let `a` and `b` be natural numbers. Then exactly one of the following
-- statements is true: `a < b`, `a ≃ b`, or `a > b`.
example {a b : ℕ} : AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b) :=
  Natural.trichotomy a b

-- Exercise 2.2.5.
-- Proposition 2.2.14 (Strong principle of induction).
-- Let `m₀` be a natural number, and let `P m` be a property pertaining to an
-- arbitrary natural number `m`. Suppose that for each `m ≥ m₀`, we have the
-- following implication: if `P m'` is true for all natural numbers
-- `m₀ ≤ m' < m`, then `P m` is also true. (In particular, this means that
-- `P m₀` is true, since in this case the hypothesis is vacuous.) Then we can
-- conclude that `P m` is true for all natural numbers `m ≥ m₀`.
example
    {P : ℕ → Prop} {m₀ : ℕ}
    : (∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' → m' < m → P m') → P m) →
    ∀ m, m ≥ m₀ → P m := by
  intro (h : ∀ m, m₀ ≤ m → (∀ m', m₀ ≤ m' → m' < m → P m') → P m)
  intro m (_ : m₀ ≤ m)
  show P m
  apply h m ‹m₀ ≤ m›
  show ∀ m', m₀ ≤ m' → m' < m → P m'
  let motive := λ m => ∀ m', m₀ ≤ m' → m' < m → P m'
  apply Natural.ind_on (motive := motive) m
  case zero =>
    intro m' (_ : m₀ ≤ m') (_ : m' < 0)
    show P m'
    exact absurd ‹m' < 0› (Natural.lt_zero)
  case step =>
    intro m (ih : ∀ m', m₀ ≤ m' → m' < m → P m')
    intro m' (_ : m₀ ≤ m') (_ : m' < step m)
    show P m'
    match Natural.lt_split ‹m' < step m› with
    | Or.inl (_ : m' < m) =>
      exact ih m' ‹m₀ ≤ m'› ‹m' < m›
    | Or.inr (_ : m' ≃ m) =>
      apply h m' ‹m₀ ≤ m'›
      intro k (_ : m₀ ≤ k) (_ : k < m')
      show P k
      have : k < m := AA.substR (rβ := (· → ·)) ‹m' ≃ m› ‹k < m'›
      exact ih k ‹m₀ ≤ k› ‹k < m›

-- Exercise 2.2.6.
-- Let `n` be a natural number, and let `P m` be a property pertaining to the
-- natural numbers such that whenever `P (step m)` is true, then `P m` is true.
-- Suppose that `P n` is also true. Prove that `P m` is true for all natural
-- numbers `m ≤ n`; this is known as the _principle of backwards induction_.
example {P : ℕ → Prop} [AA.Substitutive₁ P (· ≃ ·) (· → ·)] {n : ℕ}
    : (∀ m, P (step m) → P m) → P n → ∀ m, m ≤ n → P m := by
  intro (_ : ∀ m, P (step m) → P m)
  apply Natural.ind_on (motive := λ n => P n → ∀ m, m ≤ n → P m) n
  case zero =>
    intro (_ : P 0) m (_ : m ≤ 0)
    show P m
    match Natural.le_split ‹m ≤ 0› with
    | Or.inl (_ : m < 0) =>
      exact absurd ‹m < 0› Natural.lt_zero
    | Or.inr (_ : m ≃ 0) =>
      exact AA.subst₁ (rβ := (· → ·)) (Rel.symm ‹m ≃ 0›) ‹P 0›
  case step =>
    intro n (ih : P n → ∀ m, m ≤ n → P m) (_ : P (step n)) m (_ : m ≤ step n)
    show P m
    match Natural.le_split ‹m ≤ step n› with
    | Or.inl (_ : m < step n) =>
      have : step m ≤ step n := Natural.lt_step_le.mp ‹m < step n›
      have : m ≤ n := AA.inject ‹step m ≤ step n›
      have : P n := ‹∀ m, P (step m) → P m› n ‹P (step n)›
      exact ih ‹P n› m ‹m ≤ n›
    | Or.inr (_ : m ≃ step n) =>
      exact AA.subst₁ (rβ := (· → ·)) (Rel.symm ‹m ≃ step n›) ‹P (step n)›

/- 2.3 Multiplication -/

-- Definition 2.3.1 (Multiplication of natural numbers).
-- Let `m` be a natural number. To multiply zero to `m`, we define
-- `0 * m := 0`. Now suppose inductively that we have defined how to multiply
-- `n` to `m`. Then we can multiply `step n` to `m` by defining
-- `step n * m := (n * m) + m`.
example : ℕ → ℕ → ℕ :=
  Mul.mul (self := Natural.mulOp (self := Impl.multiplication))

example {m : ℕ} : 0 * m ≃ 0 := Natural.zero_mul (self := Impl.multiplication)

example {n m : ℕ} : step n * m ≃ (n * m) + m :=
  Natural.step_mul (self := Impl.multiplication)

-- [Multiplication obeys left and right substitution]
example : AA.Substitutive₂ (α := ℕ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·) :=
  Natural.mul_substitutive_eq

-- Thus for instance `0 * m ≃ 0`,
def ex_zero_mul {m : ℕ} : 0 * m ≃ 0 := Natural.zero_mul

-- `1 * m ≃ 0 + m`,
def ex_one_mul {m : ℕ} : 1 * m ≃ 0 + m := calc
  1 * m      ≃ _ := AA.substL (Natural.literal_step (self := Impl.literals))
  step 0 * m ≃ _ := Natural.step_mul
  0 * m + m  ≃ _ := AA.substL ex_zero_mul
  0 + m      ≃ _ := Rel.refl

-- `2 * m ≃ 0 + m + m`, etc.
def ex_two_mul {m : ℕ} : 2 * m ≃ 0 + m + m := calc
  2 * m      ≃ _ := AA.substL Natural.literal_step
  step 1 * m ≃ _ := Natural.step_mul
  1 * m + m  ≃ _ := AA.substL ex_one_mul
  0 + m + m  ≃ _ := Rel.refl

def two_mul_sum {m : ℕ} : 2 * m ≃ m + m := calc
  2 * m     ≃ _ := ex_two_mul
  0 + m + m ≃ _ := AA.substL Natural.zero_add
  m + m     ≃ _ := Rel.refl

-- Exercise 2.3.1.
-- Lemma 2.3.2 (Multiplication is commutative).
-- Let `n`, `m` be natural numbers. Then `n * m ≃ m * n`.
example {n m : ℕ} : n * m ≃ m * n := by
  exact AA.comm (self := Natural.mul_commutative)

-- Exercise 2.3.2.
-- Lemma 2.3.3 (Positive natural numbers have no zero divisors).
-- Let `n`, `m` be natural numbers. Then `n * m ≃ 0` if and only if at least
-- one of `n`, `m` is equal to zero.
example {n m : ℕ} : n * m ≃ 0 ↔ n ≃ 0 ∨ m ≃ 0 := Natural.mul_split_zero

-- In particular, if `n` and `m` are both positive, then `n * m` is also
-- positive.
example {n m : ℕ} : Positive n → Positive m → Positive (n * m) :=
  Natural.mul_positive

-- Proposition 2.3.4 (Distributive law).
-- For any natural numbers `a`, `b`, `c`, we have `a * (b + c) ≃ a * b + a * c`
-- and `(b + c) * a ≃ b * a + c * a`.
example {a b c : ℕ} : a * (b + c) ≃ a * b + a * c :=
  AA.distrib (self := Natural.mul_distributive.distributiveL)

example {a b c : ℕ} : (b + c) * a ≃ b * a + c * a := AA.distribR

-- Exercise 2.3.3.
-- Proposition 2.3.5 (Multiplication is associative).
-- For any natural numbers `a`, `b`, `c`, we have `(a * b) * c ≃ a * (b * c)`.
example {a b c : ℕ} : (a * b) * c ≃ a * (b * c) :=
  AA.assoc (self := Natural.mul_associative)

-- Proposition 2.3.6 (Multiplication preserves order).
-- If `a`, `b` are natural numbers such that `a < b`, and `c` is positive, then
-- `a * c < b * c`.
example {a b c : ℕ} : a < b → Positive c → a * c < b * c := by
  intro (_ : a < b) (_ : Positive c)
  show a * c < b * c
  let mul_substL_lt := (Natural.mul_substitutive_lt (ℕ := ℕ)).substitutiveL
  exact AA.substLC (self := mul_substL_lt) ‹Positive c› ‹a < b›

-- Corollary 2.3.7 (Cancellation law).
-- Let `a`, `b`, `c` be natural numbers such that `a * c ≃ b * c` and `c` is
-- non-zero. Then `a ≃ b`.
example {a b c : ℕ} : a * c ≃ b * c → c ≄ 0 → a ≃ b := by
  intro (_ : a * c ≃ b * c) (_ : c ≄ 0)
  show a ≃ b
  let mul_cancelR := (Natural.mul_cancellative (ℕ := ℕ)).cancellativeR
  exact AA.cancelRC (C := (· ≄ 0)) ‹c ≄ 0› ‹a * c ≃ b * c›

-- Exercise 2.3.5
-- Proposition 2.3.9 (Euclidean algorithm).
-- Let `n` be a natural number, and let `q` be a positive number. Then there
-- exist natural numbers `m`, `r` such that `0 ≤ r < q` and `n ≃ m * q + r`.
inductive Euclid (n q : ℕ) : Prop where
| intro (m r : ℕ) (r_bounded : r < q) (n_divided : n ≃ m * q + r) : Euclid n q

theorem euclidean_algorithm {n q : ℕ} : Positive q → Euclid n q := by
  intro (_ : Positive q)
  show Euclid n q
  have : 0 < q := Natural.lt_zero_pos.mp ‹Positive q›
  apply Natural.ind_on (motive := λ n => Euclid n q) n
  case zero =>
    show Euclid 0 q
    let m := 0
    let r := 0
    have r_bounded : r < q := ‹0 < q›
    have n_divided : 0 ≃ m * q + r := calc
      0         ≃ _ := Rel.symm Natural.zero_mul
      0 * q     ≃ _ := Rel.symm Natural.add_zero
      0 * q + 0 ≃ _ := Rel.refl
      m * q + r ≃ _ := Rel.refl
    exact Euclid.intro m r r_bounded n_divided
  case step =>
    intro n (ih : Euclid n q)
    show Euclid (step n) q
    have ⟨m', r', (_ : r' < q), (_ : n ≃ m' * q + r')⟩ := ih
    have : step r' ≤ q := Natural.lt_step_le.mp ‹r' < q›
    have : step r' < q ∨ step r' ≃ q := Natural.le_split ‹step r' ≤ q›
    apply Or.elim ‹step r' < q ∨ step r' ≃ q›
    · intro (_ : step r' < q)
      show Euclid (step n) q
      let m := m'
      let r := step r'
      have : r < q := ‹step r' < q›
      have : step n ≃ m * q + r := calc
        step n             ≃ _ := AA.subst₁ ‹n ≃ m' * q + r'›
        step (m' * q + r') ≃ _ := Rel.symm Natural.add_step
        m' * q + step r'   ≃ _ := Rel.refl
        m * q + r          ≃ _ := Rel.refl
      exact ⟨m, r, ‹r < q›, ‹step n ≃ m * q + r›⟩
    · intro (_ : step r' ≃ q)
      show Euclid (step n) q
      let m := step m'
      let r := 0
      have : r < q := ‹0 < q›
      have : step n ≃ m * q + r := calc
        step n             ≃ _ := AA.subst₁ ‹n ≃ m' * q + r'›
        step (m' * q + r') ≃ _ := Rel.symm Natural.add_step
        m' * q + step r'   ≃ _ := AA.substR ‹step r' ≃ q›
        m' * q + q         ≃ _ := Rel.symm Natural.step_mul
        step m' * q        ≃ _ := Rel.symm Natural.add_zero
        step m' * q + 0    ≃ _ := Rel.refl
        m * q + r          ≃ _ := Rel.refl
      exact ⟨m, r, ‹r < q›, ‹step n ≃ m * q + r›⟩

-- Definition 2.3.11 (Exponentiation for natural numbers).
example : ℕ → ℕ → ℕ :=
  Pow.pow (self := Natural.powOp (self := Impl.exponentiation))

-- Let `m` be a natural number. To raise `m` to the power `0`, we define
-- `m ^ 0 := 1`;
example {m : ℕ} : m ^ 0 ≃ 1 := Natural.pow_zero (self := Impl.exponentiation)

-- in particular, we define `0 ^ 0 := 1`.
example : 0 ^ (0 : ℕ) ≃ 1 := Natural.pow_zero

-- Now suppose recursively that `m ^ n` has been defined for some natural
-- number `n`, then we define `m ^ step n := m ^ n * m`.
example {m n : ℕ} : m ^ step n ≃ m ^ n * m :=
  Natural.pow_step (self := Impl.exponentiation)

-- Examples 2.3.12.
-- Thus for instance `x ^ 1 ≃ x ^ 0 * x ≃ 1 * x ≃ x`;
def pow_one {x : ℕ} : x ^ 1 ≃ x := calc
  x ^ 1           ≃ _ := Natural.pow_step
  x ^ (0 : ℕ) * x ≃ _ := AA.substL Natural.pow_zero
  1 * x           ≃ _ := ex_one_mul
  0 + x           ≃ _ := Natural.zero_add
  x               ≃ _ := Rel.refl

-- `x ^ 2 ≃ x ^ 1 * x ≃ x * x`;
def pow_two {x : ℕ} : x ^ 2 ≃ x * x := calc
  x ^ 2     ≃ _ := Natural.pow_step
  x ^ 1 * x ≃ _ := AA.substL pow_one
  x * x     ≃ _ := Rel.refl

-- `x ^ 3 ≃ x ^ 2 * x ≃ x * x * x`; and so forth.
example {x : ℕ} : x ^ 3 ≃ x * x * x := calc
  x ^ 3 ≃ _ := Natural.pow_step
  x ^ 2 * x ≃ _ := AA.substL pow_two
  x * x * x ≃ _ := Rel.refl

-- Exercise 2.3.4.
-- Prove the identity `(a + b) ^ 2 ≃ a ^ 2 + 2 * a * b + b ^ 2` for all natural
-- numbers `a, b`.
example {a b : ℕ} : (a + b) ^ 2 ≃ a ^ 2 + 2 * a * b + b ^ 2 := calc
  (a + b) ^ 2
    ≃ _ := pow_two
  (a + b) * (a + b)
    ≃ _ := AA.distribR
  a * (a + b) + b * (a + b)
    ≃ _ := AA.substL AA.distribL
  (a * a + a * b) + b * (a + b)
    ≃ _ := AA.substR AA.distribL
  (a * a + a * b) + (b * a + b * b)
    ≃ _ := AA.substR (AA.substL AA.comm)
  (a * a + a * b) + (a * b + b * b)
    ≃ _ := Rel.symm AA.assoc
  ((a * a + a * b) + a * b) + b * b
    ≃ _ := AA.substL AA.assoc
  a * a + (a * b + a * b) + b * b
    ≃ _ := Rel.symm (AA.substL (AA.substR two_mul_sum))
  a * a + 2 * (a * b) + b * b
    ≃ _ := Rel.symm (AA.substL (AA.substR AA.assoc))
  a * a + 2 * a * b + b * b
    ≃ _ := Rel.symm (AA.substL (AA.substL pow_two))
  a ^ 2 + 2 * a * b + b * b
    ≃ _ := Rel.symm (AA.substR pow_two)
  a ^ 2 + 2 * a * b + b ^ 2
    ≃ _ := Rel.refl

end AnalysisI.Ch2
