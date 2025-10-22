import Mathlib.CategoryTheory.Limits.Shapes.Kernels

namespace CategoryTheory.Limits
variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- The kernel of an arrow is natural. -/
@[simps]
noncomputable def kernelFunctor [HasKernels C] : Arrow C ⥤ C where
  obj f := kernel f.hom
  map {f g} u := kernel.lift _ (kernel.ι _ ≫ u.left) (by simp)

/-- The cokernel of an arrow is natural. -/
@[simps]
noncomputable def cokernelFunctor [HasCokernels C] : Arrow C ⥤ C where
  obj f := cokernel f.hom
  map {f g} u := cokernel.desc _ (u.right ≫ cokernel.π _) (by simp [← Arrow.w_assoc u])

end CategoryTheory.Limits
