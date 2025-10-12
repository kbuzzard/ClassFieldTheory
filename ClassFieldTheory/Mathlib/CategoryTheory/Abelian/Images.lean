import Mathlib.CategoryTheory.Abelian.Images

noncomputable section

namespace CategoryTheory.Abelian
open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasKernels C] [HasCokernels C]

/-- `Abelian.image` as a functor from the arrow category. -/
@[simps]
def imageFunctor : Arrow C ⥤ C where
  obj f := Abelian.image f.hom
  map {f g} u := kernel.lift _ (Abelian.image.ι f.hom ≫ u.right) sorry

/-- `Abelian.coimage` as a functor from the arrow category. -/
@[simps]
def coimageFunctor : Arrow C ⥤ C where
  obj f := Abelian.coimage f.hom
  map {f g} u := cokernel.desc _ (u.left ≫ Abelian.coimage.π g.hom) sorry

end CategoryTheory.Abelian
