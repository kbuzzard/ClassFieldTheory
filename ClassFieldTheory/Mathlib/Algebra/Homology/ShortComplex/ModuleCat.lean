import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.GroupTheory.QuotientGroup.Finite

universe v u

namespace CategoryTheory.ShortComplex
variable {R : Type u} [CommRing R]

/-- In an exact complex, a module sandwiched between two finite modules is finite. -/
lemma Exact.finite_moduleCat {S : ShortComplex (ModuleCat.{u} R)} (hS : S.Exact) [Finite S.X₁]
    [Finite S.X₃] :
    Finite S.X₂ := by
  have : Finite S.f.hom.toAddMonoidHom.range := Set.finite_range _
  have : Finite (S.X₂ ⧸ S.f.hom.toAddMonoidHom.range) := by
    rw [show S.f.hom.toAddMonoidHom.range = S.g.hom.toAddMonoidHom.ker from
      congr($(hS.moduleCat_range_eq_ker).toAddSubgroup)]
    exact .of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).toEquiv.symm
  -- TODO: Make `H` explicit in `Finite.of_finite_quot_finite_addSubgroup`
  exact .of_finite_quot_finite_addSubgroup (H := S.f.hom.toAddMonoidHom.range)

end CategoryTheory.ShortComplex
