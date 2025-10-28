import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# TODO

Move `ab_exact_iff_function_exact` out of the `ShortComplex` namespace
-/

universe u

namespace CategoryTheory.ShortComplex

alias ⟨Exact.ab_range_eq_ker, _⟩ := ab_exact_iff_range_eq_ker

/-- In an exact complex, an abelian group sandwiched between two finite abelian groups is finite. -/
lemma Exact.finite_ab {S : ShortComplex Ab.{u}} (hS : S.Exact) [Finite S.X₁] [Finite S.X₃] :
    Finite S.X₂ := by
  have : Finite S.f.hom.range := Set.finite_range _
  have : Finite (S.X₂ ⧸ S.f.hom.range) := by
    rw [hS.ab_range_eq_ker]
    exact .of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).toEquiv.symm
  -- TODO: Make `H` explicit in `Finite.of_finite_quot_finite_addSubgroup`
  exact .of_finite_quot_finite_addSubgroup (H := S.f.hom.range)

end CategoryTheory.ShortComplex
