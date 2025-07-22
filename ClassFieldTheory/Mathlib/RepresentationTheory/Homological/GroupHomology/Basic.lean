import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

noncomputable section

namespace groupHomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Representation Finsupp Rep
  Finsupp groupHomology.inhomogeneousChains HomologicalComplex

universe u

variable (k G : Type u) [CommRing k] [Group G] {k G : Type u} [CommRing k] [Group G]
  (A : Rep k G) (n : ℕ)

variable {A} in
/-- Make an `n + 1`-cycle out of an element of the kernel of the `n`th differential. -/
abbrev cyclesMk {m : ℕ} (n : ℕ) (h : (ComplexShape.down ℕ).next m = n) (f : (Fin m → G) →₀ A)
    (hf : (inhomogeneousChains A).d m n f = 0) : cycles A m :=
  (inhomogeneousChains A).cyclesMk f n h hf

variable {A} in
theorem iCycles_mk {m n : ℕ} (h : (ComplexShape.down ℕ).next m = n) (f : (Fin m → G) →₀ A)
    (hf : (inhomogeneousChains A).d m n f = 0) :
    iCycles A m (cyclesMk n h f hf) = f := by
  exact (inhomogeneousChains A).i_cyclesMk f n h hf

end groupHomology

end
