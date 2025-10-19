import Mathlib.CategoryTheory.Abelian.Images

noncomputable section

namespace CategoryTheory.Abelian
open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C]

instance epi_factorThruImage {a b : C} (f : a ⟶ b) [HasCokernel f] [HasKernel (cokernel.π f)] :
    Epi (Abelian.factorThruImage f) := by
  sorry

theorem ι_comp_eq_zero_of_comp_eq_zero {a b c : C} {f : a ⟶ b} [HasCokernel f] [HasKernel (cokernel.π f)]
    {g : b ⟶ c} (H : f ≫ g = 0) :
    Abelian.image.ι f ≫ g = 0 :=
  Epi.left_cancellation (f := Abelian.factorThruImage f) _ _ (by simp [←Category.assoc, H])

variable [HasKernels C] [HasCokernels C] [HasImages C]

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
    rw [Category.assoc]
    apply ι_comp_eq_zero_of_comp_eq_zero
    calc
      f.hom ≫ u.right ≫ cokernel.π g.hom = (u.left ≫ g.hom) ≫ cokernel.π g.hom := by
        simp [←Category.assoc]
      _ = u.left ≫ (g.hom ≫ cokernel.π g.hom) := by rw [←Category.assoc]
      _ = 0 := by simp

end CategoryTheory.Abelian
