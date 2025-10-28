import Mathlib.LinearAlgebra.Isomorphisms

variable {R M M₂ : Type*} [Ring R] [AddCommGroup M] [AddCommGroup M₂] [Module R M] [Module R M₂]

@[simp] lemma LinearMap.natCard_range_mul_natCard_ker (f : M →ₗ[R] M₂) :
    Nat.card (LinearMap.range f) * Nat.card (LinearMap.ker f) = Nat.card M := by
  rw [← Nat.card_congr f.quotKerEquivRange.toEquiv, mul_comm,
    ← Submodule.card_eq_card_quotient_mul_card]
