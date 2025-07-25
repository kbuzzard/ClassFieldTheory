import Mathlib.Algebra.Algebra.Equiv

namespace AlgEquiv
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp] lemma coe_inv (e : A ≃ₐ[R] A) : ⇑e⁻¹ = e.symm := rfl

end AlgEquiv
