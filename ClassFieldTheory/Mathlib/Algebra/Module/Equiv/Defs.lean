import Mathlib.Algebra.Module.Equiv.Defs

namespace LinearEquiv
variable {R S M₁ M₂ : Type*} [Semiring R] [Semiring S] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable {σ : R →+* S} {σ' : S →+* R}
variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

-- TODO: Replace `toEquiv` in mathlib
/-- The equivalence of types underlying a linear equivalence. -/
def toEquiv' {_ : Module R M₁} {_ : Module S M₂} : (M₁ ≃ₛₗ[σ] M₂) → M₁ ≃ M₂ :=
  fun f ↦ f.toAddEquiv.toEquiv

end LinearEquiv
