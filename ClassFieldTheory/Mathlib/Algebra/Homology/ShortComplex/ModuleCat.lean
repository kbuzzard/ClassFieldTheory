import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.GroupTheory.QuotientGroup.Finite

universe v u

namespace CategoryTheory.ShortComplex
variable {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v} R))

lemma moduleCat_range_le_ker : LinearMap.range S.f.hom ≤ LinearMap.ker S.g.hom :=
  fun _ ⟨_, ht⟩ ↦ LinearMap.mem_ker.mpr (ht ▸ moduleCat_zero_apply _ _)

lemma Exact.moduleCat_of_ker_le_range (h : LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom) :
    S.Exact := .moduleCat_of_range_eq_ker _ _ (S.moduleCat_range_le_ker.antisymm h)

/-- In an exact complex, a module sandwiched between two finite modules is finite. -/
lemma Exact.moduleCat_finite {S : ShortComplex (ModuleCat.{u} R)} (hS : S.Exact) [Finite S.X₁]
    [Finite S.X₃] :
    Finite S.X₂ := by
  have : Finite S.f.hom.toAddMonoidHom.range := Set.finite_range _
  have : Finite (S.X₂ ⧸ S.f.hom.toAddMonoidHom.range) := by
    rw [show S.f.hom.toAddMonoidHom.range = S.g.hom.toAddMonoidHom.ker from
      congr($(hS.moduleCat_range_eq_ker).toAddSubgroup)]
    exact .of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).toEquiv.symm
  exact .of_addSubgroup_quotient S.f.hom.toAddMonoidHom.range

end CategoryTheory.ShortComplex
