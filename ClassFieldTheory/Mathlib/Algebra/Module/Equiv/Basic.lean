import Mathlib.Algebra.Module.Equiv.Basic

namespace AddEquiv
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

def toIntLinearEquiv' {modG : Module ℤ G} {modH : Module ℤ H} (e : G ≃+ H) : G ≃ₗ[ℤ] H := by
  have := @AddCommGroup.uniqueIntModule.{u_1}
  have := @AddCommGroup.uniqueIntModule.{u_2}
  convert e.toIntLinearEquiv <;> exact Subsingleton.elim ..

end AddEquiv
