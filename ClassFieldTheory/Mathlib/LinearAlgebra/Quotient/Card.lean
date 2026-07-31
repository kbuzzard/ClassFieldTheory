module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Quotient.Card
public import ClassFieldTheory.Mathlib.SetTheory.Cardinal.Finite

public section

open scoped QuotientAddGroup
open LinearMap QuotientAddGroup

variable {𝕜 R M : Type*} [Semifield 𝕜] [CharZero 𝕜]

namespace Submodule
section Semiring
variable [Semiring R] [AddCommGroup M] [Module R M] {p q : Submodule R M}

@[simp]
lemma natCard_submoduleOf (h : p ≤ q) : Nat.card (p.submoduleOf q) = Nat.card p :=
  Nat.card_congr (submoduleOfEquivOfLe h)

end Semiring

section Ring
variable [Ring R] [AddCommGroup M] [Module R M] {p q : Submodule R M}

@[simp] lemma natCard_quotient [Finite M] : (Nat.card (M ⧸ p) : 𝕜) = Nat.card M / Nat.card p := by
  simp [p.card_eq_card_quotient_mul_card]

end Ring
end Submodule
