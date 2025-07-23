import Mathlib.Algebra.Module.LinearMap.Defs

namespace LinearMap
variable {R S M₁ M₂ : Type*} [Semiring R] [Semiring S] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable {σ : R →+* S}

-- TODO: Replace `toAddMonoidHom` in mathlib
/-- convert a linear map to an additive map -/
def toAddMonoidHom'' {_ : Module R M₁} {_ : Module S M₂} (f : M₁ →ₛₗ[σ] M₂) : M₁ →+ M₂ :=
  f.toAddMonoidHom

end LinearMap
