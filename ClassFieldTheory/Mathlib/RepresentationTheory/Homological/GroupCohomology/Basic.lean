import ClassFieldTheory.Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

open groupCohomology CategoryTheory
lemma cocyclesMk_surjective.{u} {k G : Type u} [CommRing k] [Group G] {A : Rep k G}
    {n : ℕ} (x : cocycles A n) : ∃ (f : (Fin n → G) → A.V)
    (h : (ConcreteCategory.hom (inhomogeneousCochains.d A n)) f = 0), cocyclesMk f h = x := by
  have := (inhomogeneousCochains A).cyclesMk_surjective (n+1) (by simp) x
  convert this <;> simp
