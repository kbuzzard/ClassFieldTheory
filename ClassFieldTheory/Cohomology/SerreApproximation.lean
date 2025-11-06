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

/-- `d : C(M_i) ⟶ C(M_i)` commutes with `d : C(M) ⟶ C(M)`. -/
theorem d_commutes_symm {w : Subrep M} {q : ℕ} {x : (inhomogeneousCochains w.toRep).X q} (f) :
    inhomogeneousCochains.d M q ((subrepToSubmoduleIso w q).symm x).val f =
    (inhomogeneousCochains.d w.toRep q x f).val := by
  rw [← d_commutes, LinearEquiv.apply_symm_apply]

-- move
@[ext] theorem _root_.Subrep.toRep_ext {k G : Type u} [CommRing k] [Monoid G] {A : Rep k G}
    {w : Subrep A} {x y : w.toRep.V} (h : x.val = y.val) : x = y :=
  Subtype.ext h

-- move
-- if π x₁ = π x₂ then there is y : C(M) with x₁ + dy = x₂
theorem exists_of_π_eq_π {q : ℕ} {x₁ x₂ : cocycles M (q + 1)}
    (h : π M (q + 1) x₁ = π M (q + 1) x₂) :
    ∃ y : (inhomogeneousCochains M).X q,
    x₁ + toCocycles M q (q + 1) y = x₂ := by
  have hc₁ := (inhomogeneousCochains M).homologyIsCokernel q (q + 1) (by simp)
  have hc₂ := ModuleCat.cokernelIsColimit ((inhomogeneousCochains M).toCycles q (q + 1))
  have h₂ := congr((hc₁.coconePointUniqueUpToIso hc₂).hom $h)
  conv at h₂ => enter [1]; exact (ConcreteCategory.comp_apply ..).symm
  conv at h₂ => enter [1,1,1]; exact IsColimit.comp_coconePointUniqueUpToIso_hom hc₁ hc₂ .one
  conv at h₂ => enter [2]; exact (ConcreteCategory.comp_apply ..).symm
  conv at h₂ => enter [2,1,1]; exact IsColimit.comp_coconePointUniqueUpToIso_hom hc₁ hc₂ .one
  obtain ⟨y, hy⟩ := (Submodule.Quotient.eq' _).mp h₂
  exact ⟨y, eq_neg_add_iff_add_eq.mp hy⟩

-- move
@[reassoc, elementwise]
theorem cocyclesMap_comp_iCocycles {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (f : G →* H) {φ : (Action.res (ModuleCat k) f).obj A ⟶ B} {n : ℕ} :
    cocyclesMap f φ n ≫ iCocycles B n = iCocycles A n ≫ (cochainsMap f φ).f n :=
  HomologicalComplex.cyclesMap_i ..

-- move
@[reassoc, elementwise]
theorem iCocycles_d {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {n : ℕ} :
    iCocycles A n ≫ inhomogeneousCochains.d A n = 0 := by
  rw [← inhomogeneousCochains.d_def, HomologicalComplex.iCycles_d]

-- /-- `Z(M_i)` is a submodule of `Z(M)`. -/

/-- Given map `f: M ⟶ N` and `q : ℕ`, if `H^{q+1}(M) ⟶ H^{q+1}(N)` is surjective, then any
`z : Z^{q+1}(N)` can be written as `f(z') + d(y)` for some `z' : Z^{q+1}(M)` and `y : C^q(M)`.

Note that `d` is spelled as `toCocycles`. -/
theorem exists_of_surjective {k G : Type u} [CommRing k] [Group G] {M N : Rep k G}
    {f : M ⟶ N} {q : ℕ} (h : Function.Surjective (map (MonoidHom.id G) f (q + 1)))
    (z : cocycles N (q + 1)) :
    ∃ z' : cocycles M (q + 1), ∃ y : (inhomogeneousCochains N).X q,
    cocyclesMap (.id G) f (q + 1) z' + toCocycles N q (q + 1) y = z := by
  have hc₁ := (inhomogeneousCochains N).homologyIsCokernel q (q + 1) (by simp)
  have hc₂ := ModuleCat.cokernelIsColimit ((inhomogeneousCochains N).toCycles q (q + 1))
  obtain ⟨z', hz'⟩ := h (π N (q + 1) z)
  induction z' using groupCohomology_induction_on with | h z' =>
  rw [π_map_apply] at hz'
  obtain ⟨y, hy⟩ := exists_of_π_eq_π hz'
  exact ⟨z', y, hy⟩

noncomputable def cocyclesMapIso {k G : Type u} [CommRing k] [Group G] {M N : Rep k G} (e : M ≅ N)
    (q : ℕ) : cocycles M q ≅ cocycles N q where
  hom := cocyclesMap (.id G) e.hom q
  inv := cocyclesMap (.id G) e.inv q
  hom_inv_id := by rw [← cocyclesMap_id_comp, e.hom_inv_id, cocyclesMap_id]
  inv_hom_id := by rw [← cocyclesMap_id_comp, e.inv_hom_id, cocyclesMap_id]

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
  -- `H^{q+1}(M_{i+1}) ⟶ H^{q+1}(M_i)` is surjective
  have h₁ (i) := map_inclusion_surjective_of_subsingleton_groupCohomology_subquotient
    (q + 1) (hm (Nat.le_succ i))
  -- `C^q(M_•)` is a complete filtration of `C^q(M)`
  have h₂ : IsFilterComplete fun i ↦ subrepToSubmodule (M_ i) q := inferInstance
  -- `Z^{q+1}(M_•)` is a complete filtration of `Z^{q+1}(M)`
  -- Kenny: I might want to state this differently later.
  have h₃ := IsFilterComplete.ker
    (fun i ↦ subrepToSubmodule (M_ i) (q + 1))
    (fun i ↦ subrepToSubmodule (M_ i) (q + 2))
    ((inhomogeneousCochains M).d (q + 1) (q + 2)).hom
    fun _ ↦ subrepToSubmodule_le_comap_d _ _
  -- repackage h₁ to h₄ : any z : Z^{q+1}(M_i) can be written as
  -- a sum of something in `Z^{q+1}(M_{i+1})` and something in `C^q(M_i)` (after mapping)
  have h₄ (i) := exists_of_surjective (h₁ i)
  choose fuel summand h₄ using h₄
  rw [subsingleton_iff_forall_eq 0]
  intro x
  induction x using groupCohomology_induction_on with | h x =>
  -- x : Z^{q+1}(M)
  obtain ⟨x, rfl⟩ := (cocyclesMapIso ((M_ 0).isoOfEqTop hm0) (q + 1)).toLinearEquiv.surjective x
  -- x : Z^{q+1}(M₀)
  let desc (i : ℕ) : cocycles (M_ i).toRep (q + 1) := i.rec x fuel
  let component (i : ℕ) : (inhomogeneousCochains (M_ i).toRep).X q := summand i (desc i)
  -- this is the decomposition of x as ∑ i, d (component i)
  -- have := IsFilterPrecomplete.sum fun i ↦ (subrepToSubmoduleIso (M_ i) q).symm (component i)
  -- now we need theory of precomplete
  sorry

end groupCohomology
