import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Abelian.Basic

noncomputable section

namespace CategoryTheory.Abelian
open Limits

variable {C : Type*} [Category C]

theorem ι_comp_eq_zero_of_comp_eq_zero [CategoryTheory.Abelian C] {a b c : C} {f : a ⟶ b}
    [HasCokernel f] [HasKernel (cokernel.π f)]
    {g : b ⟶ c} (H : f ≫ g = 0) :
    Abelian.image.ι f ≫ g = 0 :=
  Epi.left_cancellation (f := Abelian.factorThruImage f) _ _ (by simp [←Category.assoc, H])

variable [CategoryTheory.Abelian C]

/-- `Abelian.image` as a functor from the arrow category. -/
@[simps]
def imageFunctor : Arrow C ⥤ C where
  obj f := Abelian.image f.hom
  map {f g} u := by
    apply kernel.lift _ (Abelian.image.ι f.hom ≫ u.right)
    rw [Category.assoc]
    apply ι_comp_eq_zero_of_comp_eq_zero
    calc
      f.hom ≫ u.right ≫ cokernel.π g.hom = (u.left ≫ g.hom) ≫ cokernel.π g.hom := by
        simp [←Category.assoc]
      _ = u.left ≫ (g.hom ≫ cokernel.π g.hom) := by rw [←Category.assoc]
      _ = 0 := by simp

/-- `Abelian.coimage` as a functor from the arrow category. -/
@[simps]
def coimageFunctor : Arrow C ⥤ C where
  obj f := Abelian.coimage f.hom
  map {f g} u := by
    apply cokernel.desc _ (u.left ≫ Abelian.coimage.π g.hom)
    rw [←Category.assoc]
    sorry -- should be similar to the above.


end CategoryTheory.Abelian
