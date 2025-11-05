/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.Cohomology.IsFilterComplete
import ClassFieldTheory.Cohomology.Subrep.ShortExact
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-! # An approximation lemma

Let `M` be a filtered `G`-module, i.e. given `G`-submodules `M_i ≤ M` indexed by `i : ℕ`, such that
`M = lim[<-] M/M_i`. Now fix `q : ℕ` and suppose that `∀ i : ℕ, H^(q+1)(G, M_i/M_{i+1}) = 0`. Then
`H^(q+1)(G, M) = 0`.

-/

universe u

namespace Rep
variable {k G : Type u} [CommRing k] [Monoid G] (A : Rep k G)

noncomputable def piLeft (α : Type u) : Rep k G where
  V := .of _ <| α → A
  ρ :=
  { toFun g := ModuleCat.ofHom <| .pi fun i ↦ A.ρ g ∘ₗ .proj i
    map_one' := by simp only [map_one, CategoryTheory.End.one_def]; rfl
    map_mul' _ _ := by simp only [map_mul, CategoryTheory.End.mul_def]; rfl }

end Rep

-- We don't need this because C^n(M) is not meant to be viewed as a G-module?
-- noncomputable def Subrep.piLeft (w : Subrep A) (α : Type u) : Subrep (A.piLeft α) where
--   toSubmodule := .pi .univ fun _ ↦ w.toSubmodule
--   le_comap g _ hx i _ := w.le_comap g <| hx i trivial

namespace IsFilterComplete

instance subrepToSubmodule {k G : Type u} [CommRing k] [Monoid G] (M : Rep k G)
    {ι : Type*} [LE ι] (M_ : ι → Subrep M) [IsFilterComplete M_] :
    IsFilterComplete fun i ↦ (M_ i).toSubmodule :=
  sorry

instance piLeft {k M : Type u} [CommRing k] [AddCommGroup M] [Module k M]
    {ι : Type*} [LE ι] (M_ : ι → Submodule k M) [IsFilterComplete M_] (α : Type u) :
    IsFilterComplete fun i ↦ Submodule.pi .univ fun _ : α ↦ M_ i :=
  sorry

end IsFilterComplete

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] {M : Rep k G} (M_ : ℕ → Subrep M)
  (hm : Antitone M_) (hm0 : M_ 0 = ⊤) [IsFilterComplete M_]

open CategoryTheory ShortComplex HomologicalComplex Limits

theorem map_inclusion_surjective_of_subsingleton_groupCohomology_subquotient (q : ℕ)
    {w₁ w₂ : Subrep M} (h : w₁ ≤ w₂)
    [h₀ : Subsingleton (groupCohomology (w₂.subquotient w₁) q)] :
    Function.Surjective ((functor k G q).map (w₁.inclusion h)) := by
  rw [← ModuleCat.isZero_iff_subsingleton] at h₀
  rw [← ModuleCat.epi_iff_surjective]
  exact (mapShortComplex₂_exact (Subrep.shortExact_of_le h) q).epi_f <| IsZero.eq_of_tgt h₀ ..

include hm hm0 in
/-
Needed facts:
1. H^{q+1}(M_{i+1}) → H^{q+1}(M_i) is surjective
2. C^q(M_i) ⊆ C^q(M) is precomplete
3. Z^{q+1}(M_i) ⊆ Z^q(M) is Hausdorff
-/
theorem subsingleton_of_subquotient (q : ℕ)
    [h : ∀ i, Subsingleton (groupCohomology ((M_ i).subquotient (M_ (i + 1))) (q + 1))] :
    Subsingleton (groupCohomology M (q + 1)) := by
  simp_rw [← ModuleCat.isZero_iff_subsingleton, groupCohomology, ← exactAt_iff_isZero_homology,
    exactAt_iff, moduleCat_exact_iff]
  sorry

end groupCohomology
