module

public import ClassFieldTheory.Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

public section

open groupCohomology CategoryTheory
lemma cocyclesMk_surjective.{u} {k G : Type u} [CommRing k] [Group G] {A : Rep k G}
    {n : ℕ} (x : cocycles A n) : ∃ (f : (Fin n → G) → A.V)
    (h : (ConcreteCategory.hom (inhomogeneousCochains.d A n)) f = 0), cocyclesMk f h = x := by
  obtain ⟨f, h, hf⟩ := (inhomogeneousCochains A).cyclesMk_surjective (n + 1) (by simp) x
  simp only [CochainComplex.of_x, ModuleCat.forget₂_obj, CochainComplex.of_d, ModuleCat.forget₂_map,
    AddCommGrpCat.hom_ofHom] at h
  exact ⟨f, h, hf⟩
