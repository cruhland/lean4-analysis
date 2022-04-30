import Lean4Axiomatic.Integer
import Lean4Axiomatic.Integer.Impl.NatPair
import Lean4Axiomatic.Natural.Impl.Nat

open Lean4Axiomatic

namespace AnalysisI.Ch4.Sec1

abbrev ℕ : Type := Nat

namespace Impl

export Integer.Impl.NatPair (equality)

end Impl

/- 4.1 The integers -/

-- Definition 4.1.1 (Integers).
-- An _integer_ is an expression of the form `⟨a, b⟩`, where `a` and `b` are
-- natural numbers. Two integers are considered to be equal, `⟨a, b⟩ ≃ ⟨c, d⟩`,
-- if and only if `a + d ≃ c + b`. We let `ℤ` denote the set of all integers.
abbrev ℤ : Type := Integer.Impl.NatPair.PosNegPair ℕ

example {a b : ℕ} : ℤ := ⟨a, b⟩

-- [definition of the equality relation on ℤ]
example : ℤ → ℤ → Prop :=
  let inst := Integer.Equality.tildeDash (self := Impl.equality)
  Operators.tildeDash (self := inst)

example {a b c d : ℕ} : (⟨a, b⟩ : ℤ) ≃ ⟨c, d⟩ ↔ a + d ≃ c + b :=
  Iff.intro id id

end AnalysisI.Ch4.Sec1
