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

instance piLeft {k M ι : Type*} [Ring k] [AddCommGroup M] [Module k M]
    [LE ι] (M_ : ι → Submodule k M) [IsFilterComplete M_] (α : Type*) :
    IsFilterComplete fun i ↦ Submodule.pi .univ fun _ : α ↦ M_ i :=
  sorry

theorem ker {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [LE ι] (F : ι → Submodule R M) (G : ι → Submodule R N)
    [IsFilterComplete F] [IsFilterComplete G]
    (φ : M →ₗ[R] N) (hφ : ∀ i x, x ∈ F i → φ x ∈ G i) :
    IsFilterComplete fun i ↦ (F i).submoduleOf (LinearMap.ker φ) :=
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

noncomputable def subrepToSubmodule (w : Subrep M) (q : ℕ) :
    Submodule k ((inhomogeneousCochains M).X q) :=
  Submodule.pi .univ fun _ ↦ w.toSubmodule

theorem subrepToSubmodule_le_comap_d (w : Subrep M) (q : ℕ) :
    subrepToSubmodule w q ≤
    (subrepToSubmodule w (q + 1)).comap ((inhomogeneousCochains M).d q (q + 1)).hom := by
  intro x hx f _
  simp only [CochainComplex.of_x, inhomogeneousCochains.d_def, inhomogeneousCochains.d_hom_apply,
    SetLike.mem_coe]
  exact add_mem (w.2 (f 0) (hx _ trivial)) <| sum_mem fun _ _ ↦
    SMulMemClass.smul_mem _ <| hx _ trivial

instance (q : ℕ) : IsFilterComplete fun i ↦ subrepToSubmodule (M_ i) q :=
  inferInstanceAs <| IsFilterComplete fun _ ↦ Submodule.pi _ _

/-- `C(M_i)` is a submodule of `C(M)`. -/
@[simps!] def subrepToSubmoduleIso (w : Subrep M) (q : ℕ) :
    subrepToSubmodule w q ≃ₗ[k] (inhomogeneousCochains w.toRep).X q where
  toFun x := fun f ↦ ⟨_, x.2 f trivial⟩
  invFun x := ⟨_, fun f _ ↦ (x f).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `d : C(M_i) ⟶ C(M_i)` commutes with `d : C(M) ⟶ C(M)`. -/
theorem d_commutes {w : Subrep M} {q : ℕ} {x : subrepToSubmodule w q} (f) :
    (inhomogeneousCochains.d w.toRep q (subrepToSubmoduleIso w q x) f).val =
    inhomogeneousCochains.d M q x.val f := by
  simp [inhomogeneousCochains.d_hom_apply, subrepToSubmoduleIso, Subrep.toRep]

-- move
@[ext] theorem _root_.Subrep.toRep_ext {k G : Type u} [CommRing k] [Monoid G] {A : Rep k G}
    {w : Subrep A} {x y : w.toRep.V} (h : x.val = y.val) : x = y :=
  Subtype.ext h

-- move
@[simp] theorem _root_.groupCohomology.inhomogeneousCochains.d_d
    {k G : Type u} [CommRing k] {n : ℕ} [Group G] {A : Rep k G}
    (x : (inhomogeneousCochains A).X n) :
    inhomogeneousCochains.d A (n + 1) (inhomogeneousCochains.d A n x) = 0 :=
  congr($(inhomogeneousCochains.d_comp_d n A) x)

@[simp] theorem _root_.groupCohomology.inhomogeneousCochains.d_d_apply
    {k G : Type u} [CommRing k] {n : ℕ} [Group G] {A : Rep k G}
    (x : (inhomogeneousCochains A).X n) (f) :
    inhomogeneousCochains.d A (n + 1) (inhomogeneousCochains.d A n x) f = 0 :=
  congr($(inhomogeneousCochains.d_d x) f)

-- /-- `Z(M_i)` is a submodule of `Z(M)`. -/

include hm hm0 in
/-
Needed facts:
1. (✓) H^{q+1}(M_{i+1}) → H^{q+1}(M_i) is surjective
2. C^q(M_i) ⊆ C^q(M) is precomplete
3. Z^{q+1}(M_i) ⊆ Z^{q+1}(M) is Hausdorff
-/
theorem subsingleton_of_subquotient (q : ℕ)
    [h₀ : ∀ i, Subsingleton (groupCohomology ((M_ i).subquotient (M_ (i + 1))) (q + 1))] :
    Subsingleton (groupCohomology M (q + 1)) := by
  rw [← ModuleCat.isZero_iff_subsingleton, groupCohomology, ← exactAt_iff_isZero_homology,
    exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp), moduleCat_exact_iff]
  have h₁ (i) := map_inclusion_surjective_of_subsingleton_groupCohomology_subquotient
    (q + 1) (hm (Nat.le_succ i))
  have h₂ : IsFilterComplete fun i ↦ subrepToSubmodule (M_ i) q := inferInstance
  have h₃ := IsFilterComplete.ker
    (fun i ↦ subrepToSubmodule (M_ i) (q + 1))
    (fun i ↦ subrepToSubmodule (M_ i) (q + 2))
    ((inhomogeneousCochains M).d (q + 1) (q + 2)).hom
    fun _ ↦ subrepToSubmodule_le_comap_d _ _
  intro (x : (inhomogeneousCochains M).X (q + 1)) hx
  simp only [shortComplexFunctor'_obj_X₃, CochainComplex.of_x, shortComplexFunctor'_obj_X₂,
    shortComplexFunctor'_obj_g, inhomogeneousCochains.d_def] at hx
  -- hx : inhomogeneousCochains.d M (q + 1) x = 0
  -- having chosen the first `n` elements, we can choose the `n+1`-st
  have h₄ (n : ℕ) (ih : Fin n → (inhomogeneousCochains M).X q)
      (h : x - ∑ i, (inhomogeneousCochains M).d q (q + 1) (ih i) ∈
        subrepToSubmodule (M_ n) (q + 1)) :
      ∃ next : (inhomogeneousCochains M).X q,
        x - (inhomogeneousCochains M).d q (q + 1) next -
          ∑ i, (inhomogeneousCochains M).d q (q + 1) (ih i) ∈
            subrepToSubmodule (M_ (n + 1)) (q + 1) := by
    obtain ⟨y, hy⟩ := h₁ n <| π _ _ <| cocyclesMk (subrepToSubmoduleIso _ _ ⟨_, h⟩) <| by
      ext f
      rw [d_commutes]
      simp only [CochainComplex.of_x, CochainComplex.of_d, map_sub, hx, map_sum, Pi.sub_apply,
        Finset.sum_apply]
      conv => enter [1,2,2]; exact funext fun c ↦ inhomogeneousCochains.d_d_apply _ _
      simp; rfl
    induction y using groupCohomology_induction_on with | h y =>
    sorry
  sorry

end groupCohomology
