import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Eqv
import Lean4Axiomatic.Natural
import Lean4Axiomatic.Natural.Impl.Nat
import Lean4Axiomatic.Operators

open ℕ (Positive step)
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
example (n : Nat) : ℕ := OfNat.ofNat n (self := ℕ.instOfNat)

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
example {n : ℕ} : step n ≄ 0 := ℕ.step_neq_zero

-- Proposition 2.1.6.
-- `4` is not equal to `0`.
example : 4 ≄ 0 := ℕ.step_neq_zero (ℕ := ℕ)

-- Axiom 2.4.
-- Different natural numbers must have different successors; i.e., if `n`, `m`
-- are natural numbers and `n ≄ m`, then `step n ≄ step m`. Equivalently, if
-- `step n ≃ step m`, then we must have `n ≃ m`.
example {n m : ℕ} : step n ≃ step m → n ≃ m :=
  AA.inject (self := ℕ.step_injective)

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
  have : False           := ℕ.step_neq_zero this
  exact this

-- Axiom 2.5 (Principle of mathematical induction).
-- Let `P n` be any property pertaining to a natural number `n`. Suppose that
-- `P 0` is true, and suppose that whenever `P n` is true, `P (step n)` is also
-- true. Then `P n` is true for every natural number `n`.
example (P : ℕ → Prop) : P 0 → (∀ n, P n → P (step n)) → ∀ n, P n := ℕ.ind

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
example : ℕ → ℕ → ℕ := Add.add (self := ℕ.addOp)
example {m : ℕ} : 0 + m ≃ m := ℕ.zero_add
example {n m : ℕ} : step n + m ≃ step (n + m) := ℕ.step_add

-- Thus `0 + m` is `m`,
example {m : ℕ} : 0 + m ≃ m := ℕ.zero_add

-- `1 + m ≃ step 0 + m` is `step m`;
theorem one_plus_m {m : ℕ} : 1 + m ≃ step m := by
  calc
    _ ≃ 1 + m        := Eqv.refl
    _ ≃ step 0 + m   := AA.substL Eqv.refl
    _ ≃ step (0 + m) := ℕ.step_add
    _ ≃ step m       := AA.subst ℕ.zero_add

-- `2 + m ≃ step 1 + m ≃ step (step m)`;
example {m : ℕ} : 2 + m ≃ step (step m) := by
  calc
    _ ≃ 2 + m         := Eqv.refl
    _ ≃ step 1 + m    := AA.substL Eqv.refl
    _ ≃ step (1 + m)  := ℕ.step_add
    _ ≃ step (step m) := AA.subst one_plus_m

-- and so forth; for instance we have `2 + 3 ≃ step (step 3) ≃ step 4 ≃ 5`.
example : 2 + 3 ≃ 5 := by
  calc
    _ ≃ 2 + 3               := Eqv.refl
    _ ≃ step 1 + 3          := AA.substL (α := ℕ) Eqv.refl
    _ ≃ step (1 + 3)        := ℕ.step_add
    _ ≃ step (step 0 + 3)   := AA.subst (AA.substL Eqv.refl)
    _ ≃ step (step (0 + 3)) := AA.subst ℕ.step_add
    _ ≃ step (step 3)       := AA.subst (AA.subst ℕ.zero_add)
    _ ≃ step 4              := Eqv.refl
    _ ≃ 5                   := Eqv.refl

-- Note that this definition is asymmetric: `3 + 5` is incrementing `5` three
-- times, while `5 + 3` is incrementing `3` five times. Of course, they both
-- yield the same value of `8`.
example : 3 + 5 ≃ 8 := by
  let zero_add : {m : ℕ} → 0 + m ≃ m := ℕ.zero_add
  let step_add : {n m : ℕ} → step n + m ≃ step (n + m) := ℕ.step_add
  calc
    _ ≃ 3 + 5                      := Eqv.refl
    _ ≃ step (2 + 5)               := step_add
    _ ≃ step (step (1 + 5))        := AA.subst step_add
    _ ≃ step (step (step (0 + 5))) := AA.subst (AA.subst step_add)
    _ ≃ step (step (step 5))       := AA.subst (AA.subst (AA.subst zero_add))
    _ ≃ 8                          := Eqv.refl

example : 5 + 3 ≃ 8 := by
  let ss {n₁ n₂ : ℕ} : n₁ ≃ n₂ → step n₁ ≃ step n₂ := AA.subst
  let za : {m : ℕ} → 0 + m ≃ m := ℕ.zero_add
  let sa : {n m : ℕ} → step n + m ≃ step (n + m) := ℕ.step_add
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
example {n : ℕ} : n + 0 ≃ n := ℕ.add_zero

-- Lemma 2.2.3.
-- For any natural numbers `n` and `m`, `n + step m ≃ step (n + m)`.
example {n m : ℕ} : n + step m ≃ step (n + m) := ℕ.add_step

-- As a particular corollary of Lemma 2.2.2 and Lemma 2.2.3 we see that
-- `step n ≃ n + 1`.
example {n : ℕ} : step n ≃ n + 1 :=
  Eqv.symm (ℕ.add_one_step (ℕ := ℕ))

-- Proposition 2.2.4 (Addition is commutative).
-- For any natural numbers `n` and `m`, `n + m ≃ m + n`.
example {n m : ℕ} : n + m ≃ m + n := ℕ.add_comm

-- Exercise 2.2.1.
-- Proposition 2.2.5 (Addition is associative).
-- For any natural numbers `a`, `b`, `c`, we have `(a + b) + c ≃ a + (b + c)`.
example {a b c : ℕ} : (a + b) + c ≃ a + (b + c) := ℕ.add_assoc

-- Proposition 2.2.6 (Cancellation law).
-- Let `a`, `b`, `c` be natural numbers such that `a + b ≃ a + c`. Then we have
-- `b ≃ c`.
example {a b c : ℕ} : a + b ≃ a + c → b ≃ c := ℕ.cancel_add

-- Definition 2.2.7 (Positive natural numbers).
-- A natural number `n` is said to be _positive_ iff it is not equal to `0`.
example : ℕ → Prop := Positive
example {n : ℕ} : Positive n ↔ n ≄ 0 := ℕ.Sign.Base.positive_defn

-- Proposition 2.2.8.
-- If `a` is positive and `b` is a natural number, then `a + b` is positive.
example {a b : ℕ} : Positive a → Positive (a + b) :=
  ℕ.positive_add

-- Corollary 2.2.9.
-- If `a` and `b` are natural numbers such that `a + b ≃ 0`,
-- then `a ≃ 0` and `b ≃ 0`.
example {a b : ℕ} : a + b ≃ 0 → a ≃ 0 ∧ b ≃ 0 := ℕ.zero_sum_split

-- Exercise 2.2.2.
-- Lemma 2.2.10.
-- Let `a` be a positive number. Then there exists exactly one natural number
-- `b` such that `step b ≃ a`.
example {a : ℕ}
    : Positive a → ∃ b : ℕ, step b ≃ a ∧ ∀ b' : ℕ, step b' ≃ a → b ≃ b' := by
  intro (_ : Positive a)
  show ∃ b, step b ≃ a ∧ ∀ b', step b' ≃ a → b ≃ b'
  have ⟨b, (_ : step b ≃ a)⟩ := ℕ.positive_step ‹Positive a›
  exists b
  apply And.intro ‹step b ≃ a›
  intro b' (_ : step b' ≃ a)
  show b ≃ b'
  apply AA.inject (β := ℕ) (f := step) (rβ := (· ≃ ·))
  show step b ≃ step b'
  calc
    _ ≃ step b  := Eqv.refl
    _ ≃ a       := ‹step b ≃ a›
    _ ≃ step b' := Eqv.symm ‹step b' ≃ a›

-- Definition 2.2.11 (Ordering of the natural numbers).
-- Let `n` and `m` be natural numbers. We say that `n` is
-- _greater than or equal to_ `m`, and write `n ≥ m` or `m ≤ n`, iff we have
-- `n ≃ m + a` for some natural number `a`.
example : ℕ → ℕ → Prop := @GE.ge ℕ ℕ.Order.Base.leOp
example {n m : ℕ} : n ≥ m ↔ ∃ a : ℕ, n ≃ m + a := by
  apply Iff.intro
  · intro (_ : m ≤ n)
    show ∃ a, n ≃ m + a
    have ⟨a, (_ : m + a ≃ n)⟩ := ℕ.Order.Base.le_defn.mp ‹m ≤ n›
    exact ⟨a, Eqv.symm ‹m + a ≃ n›⟩
  · intro ⟨a, (_ : n ≃ m + a)⟩
    show m ≤ n
    exact ℕ.Order.Base.le_defn.mpr ⟨a, Eqv.symm ‹n ≃ m + a›⟩

-- We say that `n` is _strictly greater than_ `m`, and write `n > m` or
-- `m < n`, iff `n ≥ m` and `n ≄ m`.
example : ℕ → ℕ → Prop := @GT.gt ℕ ℕ.Order.Base.ltOp
example {n m : ℕ} : n > m ↔ n ≥ m ∧ n ≄ m := by
  apply Iff.intro
  · intro (_ : n > m)
    show n ≥ m ∧ n ≄ m
    have ⟨(_ : m ≤ n), (_ : m ≄ n)⟩ := ℕ.Order.Base.lt_defn.mp ‹m < n›
    exact ⟨‹n ≥ m›, Eqv.symm ‹m ≄ n›⟩
  · intro ⟨(_ : n ≥ m), (_ : n ≄ m)⟩
    show n > m
    have : m < n := ℕ.Order.Base.lt_defn.mpr ⟨‹m ≤ n›, Eqv.symm ‹n ≄ m›⟩
    exact ‹n > m›

-- Thus for instance `8 > 5`, because `8 ≃ 5 + 3` and `8 ≄ 5`.
example : 8 > 5 := by
  show 5 < 8
  apply ℕ.Order.Base.lt_defn.mpr
  apply And.intro
  · show 5 ≤ 8
    apply ℕ.Order.Base.le_defn.mpr
    exists (3 : ℕ)
    apply of_decide_eq_true (s := 5 + 3 ≃? 8)
    rfl
  · show 5 ≄ 8
    apply of_decide_eq_false (s := 5 ≃? 8)
    rfl

-- Also note that `step n > n` for any `n`
example {n : ℕ} : step n > n := ℕ.lt_step

-- Exercise 2.2.3.
-- Proposition 2.2.12 (Basic properties of order for natural numbers).
-- Let `a`, `b`, `c` be natural numbers. Then
-- (a) (Order is reflexive) `a ≥ a`.
example {a : ℕ} : a ≥ a := ℕ.le_refl

-- (b) (Order is transitive) If `a ≥ b` and `b ≥ c`, then `a ≥ c`.
example {a b c : ℕ} : a ≥ b → b ≥ c → a ≥ c := flip ℕ.le_trans

-- (c) (Order is anti-symmetric) If `a ≥ b` and `b ≥ a`, then `a ≃ b`.
example {a b : ℕ} : a ≥ b → b ≥ a → a ≃ b := flip ℕ.le_antisymm

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
example {a b : ℕ} : a < b ↔ step a ≤ b := ℕ.lt_step_le

-- (f) `a < b` if and only if `b ≃ a + d` for some _positive_ number `d`.
example {a b : ℕ} : a < b ↔ ∃ d, Positive d ∧ b ≃ a + d := by
  apply Iff.intro
  · intro (_ : a < b)
    show ∃ d, Positive d ∧ b ≃ a + d
    have : step a ≤ b := ℕ.lt_step_le.mp ‹a < b›
    have ⟨d, (_ : step a + d ≃ b)⟩ := ℕ.Order.Base.le_defn.mp ‹step a ≤ b›
    exists step d
    apply And.intro
    · show Positive (step d)
      apply ℕ.Sign.Base.positive_defn.mpr
      show step d ≄ 0
      exact ℕ.step_neq_zero
    · show b ≃ a + step d
      calc
        _ ≃ b            := Eqv.refl
        _ ≃ step a + d   := Eqv.symm ‹step a + d ≃ b›
        _ ≃ step (a + d) := ℕ.step_add
        _ ≃ a + step d   := Eqv.symm ℕ.add_step
  · intro ⟨d, (_ : Positive d), (_ : b ≃ a + d)⟩
    show a < b
    apply ℕ.lt_step_le.mpr
    show step a ≤ b
    apply ℕ.Order.Base.le_defn.mpr
    show ∃ k, step a + k ≃ b
    have ⟨d', (_ : step d' ≃ d)⟩ := ℕ.positive_step ‹Positive d›
    exists d'
    show step a + d' ≃ b
    calc
      _ ≃ step a + d'   := Eqv.refl
      _ ≃ step (a + d') := ℕ.step_add
      _ ≃ a + step d'   := Eqv.symm ℕ.add_step
      _ ≃ a + d         := AA.substR ‹step d' ≃ d›
      _ ≃ b             := Eqv.symm ‹b ≃ a + d›

-- Exercise 2.2.4.
-- Proposition 2.2.13 (Trichotomy of order for natural numbers).
-- Let `a` and `b` be natural numbers. Then exactly one of the following
-- statements is true: `a < b`, `a ≃ b`, or `a > b`.
example {a b : ℕ} : AA.ExactlyOneOfThree (a < b) (a ≃ b) (a > b) :=
  ℕ.trichotomy

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
  apply ℕ.ind_on (motive := motive) m
  case zero =>
    intro m' (_ : m₀ ≤ m') (_ : m' < 0)
    show P m'
    exact absurd ‹m' < 0› ℕ.lt_zero
  case step =>
    intro m (ih : ∀ m', m₀ ≤ m' → m' < m → P m')
    intro m' (_ : m₀ ≤ m') (_ : m' < step m)
    show P m'
    match ℕ.lt_split ‹m' < step m› with
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
example {P : ℕ → Prop} [AA.Substitutive P (· ≃ ·) (· → ·)] {n : ℕ}
    : (∀ m, P (step m) → P m) → P n → ∀ m, m ≤ n → P m := by
  intro (_ : ∀ m, P (step m) → P m)
  apply ℕ.ind_on (motive := λ n => P n → ∀ m, m ≤ n → P m) n
  case zero =>
    intro (_ : P 0) m (_ : m ≤ 0)
    show P m
    match ℕ.le_split ‹m ≤ 0› with
    | Or.inl (_ : m < 0) =>
      exact absurd ‹m < 0› ℕ.lt_zero
    | Or.inr (_ : m ≃ 0) =>
      exact AA.subst (rβ := (· → ·)) (Eqv.symm ‹m ≃ 0›) ‹P 0›
  case step =>
    intro n (ih : P n → ∀ m, m ≤ n → P m) (_ : P (step n)) m (_ : m ≤ step n)
    show P m
    match ℕ.le_split ‹m ≤ step n› with
    | Or.inl (_ : m < step n) =>
      have : step m ≤ step n := ℕ.lt_step_le.mp ‹m < step n›
      have : m ≤ n := AA.inject ‹step m ≤ step n›
      have : P n := ‹∀ m, P (step m) → P m› n ‹P (step n)›
      exact ih ‹P n› m ‹m ≤ n›
    | Or.inr (_ : m ≃ step n) =>
      exact AA.subst (rβ := (· → ·)) (Eqv.symm ‹m ≃ step n›) ‹P (step n)›
