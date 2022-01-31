import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Eqv
import Lean4Axiomatic.Natural
import Lean4Axiomatic.Operators

open Natural
  (Addition AdditionBase AdditionProperties Axioms Equality Positive step)
open Operators (TildeDash)

/-= Chapter 2: Starting at the beginning: the natural numbers =-/

/- 2.1 The Peano axioms -/

-- We call `ℕ` the _set of natural numbers_.
abbrev ℕ : Type := Nat

-- Axiom 2.1.
-- `0` is a natural number.
example : ℕ := 0

-- Axiom 2.2.
-- If `n` is a natural number, then `step n` is also a natural number.
example {n : ℕ} : ℕ := step n

-- Thus for instance, from Axiom 2.1 and two applications of Axiom 2.2, we see
-- that `step (step 0)` is a natural number.
example : ℕ := step (step 0)

-- Definition 2.1.3.
-- We define `1` to be the number `step 0`,
example : 1 ≃ step 0 := Eqv.refl

-- `2` to be the number `step (step 0)`,
example : 2 ≃ step (step 0) := Eqv.refl

-- `3` to be the number `step (step (step 0))`,
example : 3 ≃ step (step (step 0)) := Eqv.refl

-- etc.
-- [We can convert any natural number literal (`Nat`) into `ℕ`]
example (n : Nat) : ℕ := OfNat.ofNat n (self := Natural.instOfNat)

-- (In other words, `1 := step 0`, `2 := step 1`, `3 := step 2`, etc.)
example : 1 ≃ step 0 := Eqv.refl
example : 2 ≃ step 1 := Eqv.refl
example : 3 ≃ step 2 := Eqv.refl

-- Proposition 2.1.4.
-- `3` is a natural number.
-- [The proof is given above; `3 ≃ step (step (step 0))`]
example : ℕ := 3

-- Axiom 2.3.
-- `0` is not the successor of any natural number; i.e., we have `step n ≄ 0`
-- for every natural number `n`.
example {n : ℕ} : step n ≄ 0 := Axioms.step_neq_zero

-- Proposition 2.1.6.
-- `4` is not equal to `0`.
example : 4 ≄ 0 := Axioms.step_neq_zero (ℕ := ℕ)

-- Axiom 2.4.
-- Different natural numbers must have different successors; i.e., if `n`, `m`
-- are natural numbers and `n ≄ m`, then `step n ≄ step m`. Equivalently, if
-- `step n ≃ step m`, then we must have `n ≃ m`.
example {n m : ℕ} : step n ≃ step m → n ≃ m := Axioms.step_injective

-- Proposition 2.1.8.
-- `6` is not equal to `2`.
example : 6 ≄ 2 := by
  intro (_ : 6 ≃ 2)
  show False
  have : step 5 ≃ step 1 := ‹6 ≃ 2›
  have : 5 ≃ 1           := Axioms.step_injective this
  have : step 4 ≃ step 0 := this
  have : 4 ≃ 0           := Axioms.step_injective this
  have : step 3 ≃ 0      := this
  have : False           := Axioms.step_neq_zero this
  exact this

-- Axiom 2.5 (Principle of mathematical induction).
-- Let `P n` be any property pertaining to a natural number `n`. Suppose that
-- `P 0` is true, and suppose that whenever `P n` is true, `P (step n)` is also
-- true. Then `P n` is true for every natural number `n`.
example (P : ℕ → Prop) : P 0 → (∀ n, P n → P (step n)) → ∀ n, P n := Axioms.ind

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
#check {f : ∀ n : ℕ, ℕ → ℕ} → {c : ℕ} →
  ∃ a : ℕ → ℕ, a 0 ≃ c ∧ ∀ n, a (step n) ≃ f n (a n)

/- 2.2 Addition -/

-- Definition 2.2.1 (Addition of natural numbers).
-- Let `m` be a natural number. To add zero to `m`, we define `0 + m := m`. Now
-- suppose inductively that we have defined how to add `n` to `m`. Then we can
-- add `step n` to `m` by defining `step n + m := step (n + m)`.
example : ℕ → ℕ → ℕ := Add.add (self := AdditionBase.addOp)
example {m : ℕ} : 0 + m ≃ m := AdditionBase.zero_add
example {n m : ℕ} : step n + m ≃ step (n + m) := AdditionBase.step_add

-- Thus `0 + m` is `m`,
example {m : ℕ} : 0 + m ≃ m := AdditionBase.zero_add

-- `1 + m ≃ step 0 + m` is `step m`;
theorem one_plus_m {m : ℕ} : 1 + m ≃ step m := by
  calc
    _ ≃ 1 + m        := Eqv.refl
    _ ≃ step 0 + m   := AA.substL Eqv.refl
    _ ≃ step (0 + m) := AdditionBase.step_add
    _ ≃ step m       := AA.subst AdditionBase.zero_add

-- `2 + m ≃ step 1 + m ≃ step (step m)`;
example {m : ℕ} : 2 + m ≃ step (step m) := by
  calc
    _ ≃ 2 + m         := Eqv.refl
    _ ≃ step 1 + m    := AA.substL Eqv.refl
    _ ≃ step (1 + m)  := AdditionBase.step_add
    _ ≃ step (step m) := AA.subst one_plus_m

-- and so forth; for instance we have `2 + 3 ≃ step (step 3) ≃ step 4 ≃ 5`.
example : 2 + 3 ≃ 5 := by
  calc
    _ ≃ 2 + 3               := Eqv.refl
    _ ≃ step 1 + 3          := AA.substL (α := ℕ) Eqv.refl
    _ ≃ step (1 + 3)        := AdditionBase.step_add
    _ ≃ step (step 0 + 3)   := AA.subst (AA.substL Eqv.refl)
    _ ≃ step (step (0 + 3)) := AA.subst AdditionBase.step_add
    _ ≃ step (step 3)       := AA.subst (AA.subst AdditionBase.zero_add)
    _ ≃ step 4              := Eqv.refl
    _ ≃ 5                   := Eqv.refl

-- Note that this definition is asymmetric: `3 + 5` is incrementing `5` three
-- times, while `5 + 3` is incrementing `3` five times. Of course, they both
-- yield the same value of `8`.
example : 3 + 5 ≃ 8 := by
  let zero_add : {m : ℕ} → 0 + m ≃ m := AdditionBase.zero_add
  let step_add : {n m : ℕ} → step n + m ≃ step (n + m) := AdditionBase.step_add
  calc
    _ ≃ 3 + 5                      := Eqv.refl
    _ ≃ step (2 + 5)               := step_add
    _ ≃ step (step (1 + 5))        := AA.subst step_add
    _ ≃ step (step (step (0 + 5))) := AA.subst (AA.subst step_add)
    _ ≃ step (step (step 5))       := AA.subst (AA.subst (AA.subst zero_add))
    _ ≃ 8                          := Eqv.refl

example : 5 + 3 ≃ 8 := by
  let ss {n₁ n₂ : ℕ} : n₁ ≃ n₂ → step n₁ ≃ step n₂ := AA.subst
  let za : {m : ℕ} → 0 + m ≃ m := AdditionBase.zero_add
  let sa : {n m : ℕ} → step n + m ≃ step (n + m) := AdditionBase.step_add
  calc
    _ ≃ 5 + 3                                    := Eqv.refl
    _ ≃ step (4 + 3)                             := sa
    _ ≃ step (step (3 + 3))                      := ss sa
    _ ≃ step (step (step (2 + 3)))               := ss (ss sa)
    _ ≃ step (step (step (step (1 + 3))))        := ss (ss (ss sa))
    _ ≃ step (step (step (step (step (0 + 3))))) := ss (ss (ss (ss sa)))
    _ ≃ step (step (step (step (step 3))))       := ss (ss (ss (ss (ss za))))
    _ ≃ 8                                        := Eqv.refl

-- Lemma 2.2.2.
-- For any natural number `n`, `n + 0 ≃ n`.
example {n : ℕ} : n + 0 ≃ n := Natural.Derived.add_zero

-- Lemma 2.2.3.
-- For any natural numbers `n` and `m`, `n + step m ≃ step (n + m)`.
example {n m : ℕ} : n + step m ≃ step (n + m) := Natural.Derived.add_step

-- As a particular corollary of Lemma 2.2.2 and Lemma 2.2.3 we see that
-- `step n ≃ n + 1`.
example {n : ℕ} : step n ≃ n + 1 :=
  Eqv.symm (Natural.Derived.add_one_step (ℕ := ℕ))

-- Proposition 2.2.4 (Addition is commutative).
-- For any natural numbers `n` and `m`, `n + m ≃ m + n`.
example {n m : ℕ} : n + m ≃ m + n := Natural.Derived.add_comm

-- Exercise 2.2.1.
-- Proposition 2.2.5 (Addition is associative).
-- For any natural numbers `a`, `b`, `c`, we have `(a + b) + c ≃ a + (b + c)`.
example {a b c : ℕ} : (a + b) + c ≃ a + (b + c) := Natural.Derived.add_assoc

-- Proposition 2.2.6 (Cancellation law).
-- Let `a`, `b`, `c` be natural numbers such that `a + b ≃ a + c`. Then we have
-- `b ≃ c`.
example {a b c : ℕ} : a + b ≃ a + c → b ≃ c := Natural.Derived.cancel_add

-- Definition 2.2.7 (Positive natural numbers).
-- A natural number `n` is said to be _positive_ iff it is not equal to `0`.
example : ℕ → Prop := Positive
example {n : ℕ} : Positive n ↔ n ≄ 0 := Natural.SignBase.positive_defn

-- Proposition 2.2.8.
-- If `a` is positive and `b` is a natural number, then `a + b` is positive.
example {a b : ℕ} : Positive a → Positive (a + b) :=
  Natural.Derived.positive_add

-- Corollary 2.2.9.
-- If `a` and `b` are natural numbers such that `a + b ≃ 0`,
-- then `a ≃ 0` and `b ≃ 0`.
example {a b : ℕ} : a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0 := Natural.Derived.zero_sum_split

-- Exercise 2.2.2.
-- Lemma 2.2.10.
-- Let `a` be a positive number. Then there exists exactly one natural number
-- `b` such that `step b ≃ a`.
example {a : ℕ}
    : Positive a → ∃ b : ℕ, step b ≃ a ∧ ∀ b' : ℕ, step b' ≃ a → b ≃ b' := by
  apply Natural.Derived.casesOn
    (motive := λ a =>
      Positive a → ∃ b : ℕ, step b ≃ a ∧ ∀ b' : ℕ, step b' ≃ a → b ≃ b')
    a
  case zero =>
    intro (_ : Positive 0)
    apply False.elim
    show False
    have : 0 ≄ 0 := Natural.SignBase.positive_defn.mp ‹Positive 0›
    exact this Eqv.refl
  case step =>
    intro a (_ : Positive (step a))
    show ∃ b : ℕ, step b ≃ step a ∧ ∀ b' : ℕ, step b' ≃ step a → b ≃ b'
    exists a
    apply And.intro
    · show step a ≃ step a
      exact Eqv.refl
    · intro b' (_ : step b' ≃ step a)
      show a ≃ b'
      apply Axioms.step_injective
      show step a ≃ step b'
      exact Eqv.symm ‹step b' ≃ step a›

-- Definition 2.2.11 (Ordering of the natural numbers).
-- Let `n` and `m` be natural numbers. We say that `n` is
-- _greater than or equal to_ `m`, and write `n ≥ m` or `m ≤ n`, iff we have
-- `n ≃ m + a` for some natural number `a`.
example : ℕ → ℕ → Prop := @GE.ge ℕ Natural.OrderBase.leOp
example {n m : ℕ} : n ≥ m ↔ ∃ a : ℕ, n ≃ m + a := by
  apply Iff.intro
  · intro (_ : m ≤ n)
    show ∃ a, n ≃ m + a
    have ⟨a, (_ : m + a ≃ n)⟩ := Natural.OrderBase.le_defn.mp ‹m ≤ n›
    exact ⟨a, Eqv.symm ‹m + a ≃ n›⟩
  · intro ⟨a, (_ : n ≃ m + a)⟩
    show m ≤ n
    exact Natural.OrderBase.le_defn.mpr ⟨a, Eqv.symm ‹n ≃ m + a›⟩

-- We say that `n` is _strictly greater than_ `m`, and write `n > m` or
-- `m < n`, iff `n ≥ m` and `n ≄ m`.
example : ℕ → ℕ → Prop := @GT.gt ℕ Natural.OrderBase.ltOp
example {n m : ℕ} : n > m ↔ n ≥ m ∧ n ≄ m := by
  apply Iff.intro
  · intro (_ : n > m)
    show n ≥ m ∧ n ≄ m
    have ⟨(_ : m ≤ n), (_ : m ≄ n)⟩ := Natural.OrderBase.lt_defn.mp ‹m < n›
    exact ⟨‹n ≥ m›, Eqv.symm ‹m ≄ n›⟩
  · intro ⟨(_ : n ≥ m), (_ : n ≄ m)⟩
    show n > m
    have : m < n := Natural.OrderBase.lt_defn.mpr ⟨‹m ≤ n›, Eqv.symm ‹n ≄ m›⟩
    exact ‹n > m›

-- Thus for instance `8 > 5`, because `8 ≃ 5 + 3` and `8 ≄ 5`.
example : 8 > 5 := by
  show 5 < 8
  apply Natural.OrderBase.lt_defn.mpr
  apply And.intro
  · show 5 ≤ 8
    apply Natural.OrderBase.le_defn.mpr
    exists (3 : ℕ)
    apply of_decide_eq_true (s := 5 + 3 ≃? 8)
    rfl
  · show 5 ≄ 8
    apply of_decide_eq_false (s := 5 ≃? 8)
    rfl

-- Also note that `step n > n` for any `n`
example {n : ℕ} : step n > n := Natural.Derived.lt_step

-- Exercise 2.2.3.
-- Proposition 2.2.12 (Basic properties of order for natural numbers).
-- Let `a`, `b`, `c` be natural numbers. Then
-- (a) (Order is reflexive) `a ≥ a`.
example {a : ℕ} : a ≥ a := Natural.Derived.le_refl

-- (b) (Order is transitive) If `a ≥ b` and `b ≥ c`, then `a ≥ c`.
example {a b c : ℕ} : a ≥ b → b ≥ c → a ≥ c := flip Natural.Derived.le_trans

-- (c) (Order is anti-symmetric) If `a ≥ b` and `b ≥ a`, then `a ≃ b`.
example {a b : ℕ} : a ≥ b → b ≥ a → a ≃ b := flip Natural.Derived.le_antisymm
