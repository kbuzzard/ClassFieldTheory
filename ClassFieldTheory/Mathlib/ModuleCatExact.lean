import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
-- should be put in ^ this file

universe u

namespace CategoryTheory.ShortComplex

theorem moduleCat_range_le_ker
    {R : Type u} [Ring R] (S : ShortComplex (ModuleCat R)) :
    LinearMap.range S.f.hom ≤ LinearMap.ker S.g.hom :=
  fun _ ⟨_, ht⟩ ↦ LinearMap.mem_ker.mpr (ht ▸ moduleCat_zero_apply _ _)

theorem Exact.moduleCat_of_ker_le_range
    {R : Type u} [Ring R] (S : ShortComplex (ModuleCat R))
    (h : LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom) :
    S.Exact :=
  ShortComplex.Exact.moduleCat_of_range_eq_ker _ _
    (le_antisymm S.moduleCat_range_le_ker h)

