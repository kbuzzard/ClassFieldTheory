import Mathlib.CategoryTheory.Abelian.Basic

noncomputable section

namespace CategoryTheory.Abelian
open Limits

variable {C : Type*} [Category C] [Abelian C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

@[simp] lemma image.ι_comp_eq_zero : image.ι f ≫ g = 0 ↔ f ≫ g = 0 := by
  simp [← cancel_epi (Abelian.factorThruImage _)]

@[simp] lemma coimage.comp_π_eq_zero : f ≫ coimage.π g = 0 ↔ f ≫ g = 0 := by
  simp [← cancel_mono (Abelian.factorThruCoimage _)]

/-- `Abelian.image` as a functor from the arrow category. -/
@[simps]
def imageFunctor : Arrow C ⥤ C where
  obj f := Abelian.image f.hom
  map {f g} u := kernel.lift _ (Abelian.image.ι f.hom ≫ u.right) <| by simp [← Arrow.w_assoc u]

/-- `Abelian.coimage` as a functor from the arrow category. -/
@[simps]
def coimageFunctor : Arrow C ⥤ C where
  obj f := Abelian.coimage f.hom
  map {f g} u := cokernel.desc _ (u.left ≫ Abelian.coimage.π g.hom) <| by
    simp [← Category.assoc, coimage.comp_π_eq_zero]; simp

/-- The image and coimage of an arrow are naturally isomorphic. -/
@[simps!]
def coimageFunctorIsoImageFunctor : coimageFunctor (C := C) ≅ imageFunctor :=
  NatIso.ofComponents fun _ ↦ Abelian.coimageIsoImage _

end CategoryTheory.Abelian
