import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

noncomputable section

namespace groupHomology

open CategoryTheory CategoryTheory.Limits Representation Rep Finsupp CategoryTheory.ShortComplex

universe v u

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

lemma cyclesMk₀_eq (x : A) :
    cyclesMk 0 (by simp) ((chainsIso₀ A).inv x) (by simp) = (cyclesIso₀ A).inv x :=
  (ModuleCat.mono_iff_injective <| iCycles A 0).1 inferInstance <| by rw [iCycles_mk]; simp

lemma cyclesMk₁_eq (x : cycles₁ A) :
    cyclesMk 0 (by simp) ((chainsIso₁ A).inv x) (by simp) = (isoCycles₁ A).inv x :=
  (ModuleCat.mono_iff_injective <| iCycles A 1).1 inferInstance <| by
    rw [iCycles_mk]
    simp only [ChainComplex.of_x, isoCycles₁_inv_comp_iCycles_apply]
    rfl

lemma cyclesMk₂_eq (x : cycles₂ A) :
    cyclesMk 1 (by simp) ((chainsIso₂ A).inv x) (by simp) = (isoCycles₂ A).inv x :=
  (ModuleCat.mono_iff_injective <| iCycles A 2).1 inferInstance <| by
    rw [iCycles_mk]
    simp only [ChainComplex.of_x, isoCycles₂_inv_comp_iCycles_apply]
    rfl

end groupHomology

end
