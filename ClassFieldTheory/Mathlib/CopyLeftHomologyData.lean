import Mathlib.Algebra.Homology.ShortComplex.LeftHomology

universe v u

namespace CategoryTheory.ShortComplex.LeftHomologyData

open Limits Category

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {S : ShortComplex C} (h : S.LeftHomologyData)

@[simps] def copy (K' H' : C) (eK : K' ≅ h.K) (eH : H' ≅ h.H) : S.LeftHomologyData where
  K := K'
  H := H'
  i := eK.hom ≫ h.i
  π := eK.hom ≫ h.π ≫ eH.inv
  wi := by rw [assoc, h.wi, comp_zero]
  hi := IsKernel.isoKernel _ _ h.hi eK (by simp)
  wπ := by simp [IsKernel.isoKernel]
  hπ := IsColimit.equivOfNatIsoOfIso
    (parallelPair.ext (Iso.refl S.X₁) eK.symm (by simp [IsKernel.isoKernel]) (by simp)) _ _
    (Cocones.ext (by exact eH.symm) (by rintro (_ | _) <;> simp [IsKernel.isoKernel])) h.hπ

end CategoryTheory.ShortComplex.LeftHomologyData
