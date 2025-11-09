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

-- theorem ker {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
--     [AddCommGroup N] [Module R N] [LE ι] (F : ι → Submodule R M) (G : ι → Submodule R N)
--     [IsFilterComplete F] [IsFilterComplete G]
--     (φ : M →ₗ[R] N) (hφ : ∀ i x, x ∈ F i → φ x ∈ G i) :
--     IsFilterComplete fun i ↦ (F i).submoduleOf (LinearMap.ker φ) :=
--   sorry

end IsFilterComplete

namespace groupCohomology
variable {k G : Type u} [CommRing k] [Group G] {M : Rep k G}

section
variable (M_ : ℕ → Subrep M) [IsFilterComplete M_]

open CategoryTheory ShortComplex HomologicalComplex Limits

/-- Given a subrep `w : M`, this is `C^q(w)` as a submodule of `C^q(M)`. -/
noncomputable def _root_.Subrep.toCochains (w : Subrep M) (q : ℕ) :
    Submodule k ((inhomogeneousCochains M).X q) :=
  Submodule.pi .univ fun _ ↦ w.toSubmodule

noncomputable def _root_.Subrep.toCochainsOrderHom (q : ℕ) :
    Subrep M →o Submodule k ((inhomogeneousCochains M).X q) :=
  ⟨(·.toCochains q), fun _ _ h₁ _ h₂ _ _ ↦ h₁ <| h₂ _ trivial⟩

/-- Given a subrep `w : M`, this is `Z^q(w)` as a submodule of `Z^q(M)`. -/
noncomputable def _root_.Subrep.toCocycles (w : Subrep M) (q : ℕ) :
    Submodule k (cocycles M q) :=
  (w.toCochains q).comap (iCocycles M q).hom

noncomputable def _root_.Subrep.toCocyclesOrderHom (q : ℕ) :
    Subrep M →o Submodule k (cocycles M q) :=
  ⟨(·.toCocycles q), fun _ _ h₁ _ h₂ _ _ ↦ h₁ <| h₂ _ trivial⟩

instance (q : ℕ) : IsFilterComplete fun i ↦ (M_ i).toCochains q :=
  inferInstanceAs <| IsFilterComplete fun _ ↦ Submodule.pi _ _

instance [IsFilterComplete M_] (q : ℕ) : IsFilterComplete fun i ↦ (M_ i).toCocycles q :=
  sorry

/-- `C(w)` is isomorphic to the submodule of `C(M)` called `w.toCochains q`. -/
@[simps!] noncomputable def _root_.Subrep.toCochainsIso (w : Subrep M) (q : ℕ) :
    w.toCochains q ≃ₗ[k] (inhomogeneousCochains w.toRep).X q where
  toFun x := fun f ↦ ⟨_, x.2 f trivial⟩
  invFun x := ⟨(cochainsMap (.id G) w.subtype).f q x, fun f _ ↦ by
    simp [Subrep.subtype, Submodule.subtype]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `d : C(M_i) ⟶ C(M_i)` commutes with `d : C(M) ⟶ C(M)`. -/
theorem d_toCochainsIso_symm {w : Subrep M} {q : ℕ} {x : (inhomogeneousCochains w.toRep).X q} :
    (inhomogeneousCochains M).d q (q + 1) ((w.toCochainsIso q).symm x) =
    (w.toCochainsIso (q + 1)).symm ((inhomogeneousCochains w.toRep).d q (q + 1) x) := by
  ext; simp [inhomogeneousCochains.d_hom_apply, Subrep.toCochainsIso, Subrep.toRep]

-- move
@[reassoc]
theorem iCocycles_d {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {n : ℕ} :
    iCocycles A n ≫ (inhomogeneousCochains A).d n (n + 1) = 0 :=
  HomologicalComplex.iCycles_d ..

-- move
theorem iCocycles_d_apply {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {n : ℕ} (x) :
    (inhomogeneousCochains A).d n (n + 1) (iCocycles A n x) = 0 :=
  congr($iCocycles_d x)

-- move
@[reassoc, elementwise]
theorem iCocycles_d' {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {n : ℕ} :
    iCocycles A n ≫ inhomogeneousCochains.d A n = 0 := by
  rw [← inhomogeneousCochains.d_def, iCocycles_d]

-- move
@[reassoc, elementwise]
theorem cocyclesMap_comp_iCocycles {k G H : Type u} [CommRing k] [Group G] [Group H]
    {A : Rep k H} {B : Rep k G} (f : G →* H) {φ : (Action.res (ModuleCat k) f).obj A ⟶ B} {n : ℕ} :
    cocyclesMap f φ n ≫ iCocycles B n = iCocycles A n ≫ (cochainsMap f φ).f n :=
  HomologicalComplex.cyclesMap_i ..

-- move
@[reassoc]
theorem toCocycles_iCocycles {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {n : ℕ} :
    toCocycles A n (n + 1) ≫ iCocycles A (n + 1) = (inhomogeneousCochains A).d n (n + 1) :=
  HomologicalComplex.toCycles_i ..

-- move
-- `@[elementwise]` causes `(inhomogeneousCochains _).X` to leak into the pi-type
theorem toCocycles_iCocycles_apply {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {n : ℕ}
    {x : (inhomogeneousCochains A).X n} :
    iCocycles A (n + 1) (toCocycles A n (n + 1) x) = (inhomogeneousCochains A).d n (n + 1) x :=
  congr($toCocycles_iCocycles x)

/-- `Z(w)` is isomorphic to the submodule of `Z(M)` called `w.toCocycles q`. -/
noncomputable def _root_.Subrep.toCocyclesIso (w : Subrep M) (q : ℕ) :
    w.toCocycles q ≃ₗ[k] cocycles w.toRep q where
  toFun x := cocyclesMk (w.toCochainsIso q ⟨iCocycles M q x.val, x.2⟩) <|
    (map_eq_zero_iff _ (w.toCochainsIso (q + 1)).symm.injective).mp <| by
    ext
    rw [← inhomogeneousCochains.d_def]
    erw [← d_toCochainsIso_symm]
    rw [LinearEquiv.symm_apply_apply, Subtype.coe_mk, iCocycles_d_apply]
    rfl
  invFun x := ⟨cocyclesMap (.id G) w.subtype q x, by
    simp only [Subrep.toCocycles, CochainComplex.of_x, Submodule.mem_comap,
      cocyclesMap_comp_iCocycles_apply, cochainsMap_id_f_hom_eq_compLeft]
    exact ((w.toCochainsIso q).symm (iCocycles w.toRep q x)).2⟩
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

-- Kenny: this feels duplicated somehow
theorem _root_.Subrep.toCocycles_mem_toCocycles {w : Subrep M} {q : ℕ}
    {x : (inhomogeneousCochains M).X q} (h : x ∈ w.toCochains q) :
    toCocycles M q (q + 1) x ∈ w.toCocycles (q + 1) := by
  -- have :=  (toCocycles w.toRep q (q + 1) ((w.toCochainsIso q) ⟨x, h⟩))
  unfold Subrep.toCocycles
  rw [Submodule.mem_comap, ModuleCat.Hom.hom, toCocycles_iCocycles_apply]
  -- dx ∈ C^(q+1)_w
  intro f _
  rw [inhomogeneousCochains.d_def]
  refine add_mem (w.le_comap _ <| h _ trivial) <| sum_mem fun _ _ ↦ SMulMemClass.smul_mem _ <|
    h _ trivial


-- theorem _root_.HomologicalComplex.toCycles_nat {C : Type*} [Category C]
--     [HasZeroMorphisms C] {K : HomologicalComplex C (ComplexShape.up ℕ)}
--     {j : ℕ} [K.HasHomology (j + 1)] [(K.sc' j (j + 1) (j + 2)).HasLeftHomology] :
--     K.toCycles j (j + 1) = (K.sc' j (j + 1) (j + 2)).toCycles :=
--   _

theorem toCycles_naturality {w : Subrep M} {q : ℕ} :
    toCocycles w.toRep q (q + 1) ≫ cocyclesMap (.id G) w.subtype (q + 1) =
    (cochainsMap (.id G) w.subtype).f q ≫ toCocycles M q (q + 1) := by
  sorry -- ????
  -- rw [← groupCohomology.functor_map]
  -- unfold toCocycles /- HomologicalComplex.toCycles HomologicalComplex.liftCycles
    -- ShortComplex.liftCycles cocyclesMap HomologicalComplex.cyclesMap -/
  -- convert CategoryTheory.ShortComplex.toCycles_naturality _ using 1
  -- CategoryTheory.ShortComplex.toCycles_naturality
  --   ((HomologicalComplex.shortComplexFunctor _ _ _).map
  --     (groupCohomology.cochainsMap (.id G) w.subtype))

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

theorem map_inclusion_surjective_of_subsingleton_groupCohomology_subquotient (q : ℕ)
    {w₁ w₂ : Subrep M} (h : w₁ ≤ w₂)
    [h₀ : Subsingleton (groupCohomology (w₂.subquotient w₁) q)] :
    Function.Surjective ((functor k G q).map (w₁.inclusion h)) := by
  rw [← ModuleCat.isZero_iff_subsingleton] at h₀
  rw [← ModuleCat.epi_iff_surjective]
  exact (mapShortComplex₂_exact (Subrep.shortExact_of_le h) q).epi_f <| IsZero.eq_of_tgt h₀ ..

@[reassoc, elementwise]
theorem toCocycles_comp_π {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (q : ℕ) :
    toCocycles M q (q + 1) ≫ π M (q + 1) = 0 :=
  toCycles_comp_homologyπ ..

end

section
-- Kenny: I don't know if we should make a separate definition for `a - b ∈ s`.
-- can't tag with `@[gcongr]`

theorem _root_.sub_mem_trans {M σ : Type*} [AddGroup M] [SetLike σ M] [AddSubgroupClass σ M]
    {s : σ} {a b c : M} (hab : a - b ∈ s) (hbc : b - c ∈ s) : a - c ∈ s :=
  sub_add_sub_cancel a b c ▸ add_mem hab hbc

theorem _root_.sub_mem_symm {M σ : Type*} [AddGroup M] [SetLike σ M] [AddSubgroupClass σ M]
    {s : σ} {a b : M} (h : a - b ∈ s) : b - a ∈ s :=
  neg_sub a b ▸ neg_mem h

open CategoryTheory

-- MOVE
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem _root_.Subrep.inclusion_comp_subtype {w₁ w₂ : Subrep M} {h : w₁ ≤ w₂} :
    w₁.inclusion h ≫ w₂.subtype = w₁.subtype :=
  rfl



end

section
variable (M_ : ℕ → Subrep M) [IsFilterComplete M_] (hm : Antitone M_) (hm0 : M_ 0 = ⊤)

open OrderDual CategoryTheory

/-
Needed facts:
1. (✓) H^{q+1}(M_{i+1}) → H^{q+1}(M_i) is surjective
2. C^q(M_i) ⊆ C^q(M) is precomplete
3. Z^{q+1}(M_i) ⊆ Z^{q+1}(M) is Hausdorff
-/
include hm hm0 in
theorem subsingleton_of_subquotient (q : ℕ)
    [h₀ : ∀ i, Subsingleton (groupCohomology ((M_ i).subquotient (M_ (i + 1))) (q + 1))] :
    Subsingleton (groupCohomology M (q + 1)) := by
  -- `H^{q+1}(M_{i+1}) ⟶ H^{q+1}(M_i)` is surjective
  have h₁ (i) := map_inclusion_surjective_of_subsingleton_groupCohomology_subquotient
    (q + 1) (hm (Nat.le_succ i))
  -- `C^q(M_•)` is a complete filtration of `C^q(M)`
  have : IsFilterComplete fun i ↦ (M_ i).toCochains q := inferInstance
  -- `Z^{q+1}(M_•)` is a complete filtration of `Z^{q+1}(M)`
  have : IsFilterComplete fun i ↦ (M_ i).toCocycles (q + 1) := inferInstance
  -- build the bundled versions of each filtration
  let M_' : ℕᵒᵈ →o Subrep M := ⟨(M_ <| ofDual ·), fun _ _ h ↦ hm h⟩
  have : IsFilterComplete (M_' ∘ toDual) := ‹_›
  let C_ : ℕᵒᵈ →o Submodule k ((inhomogeneousCochains M).X q) :=
    (Subrep.toCochainsOrderHom q).comp M_'
  have : IsFilterComplete (C_ ∘ toDual) := ‹_›
  let Z_ : ℕᵒᵈ →o Submodule k (cocycles M (q + 1)) :=
    (Subrep.toCocyclesOrderHom (q + 1)).comp M_'
  -- repackage h₁ to h₂ : any z : Z^{q+1}(M_i) can be written as
  -- a sum of something in `Z^{q+1}(M_{i+1})` and something in `C^q(M_i)` (after mapping)
  have h₂ (i) := exists_of_surjective (h₁ i)
  choose fuel summand h₂ using h₂
  rw [subsingleton_iff_forall_eq 0]
  intro x
  induction x using groupCohomology_induction_on with | h x =>
  -- x : Z^{q+1}(M)
  obtain ⟨x, rfl⟩ := (cocyclesMapIso ((M_ 0).isoOfEqTop hm0) (q + 1)).toLinearEquiv.surjective x
  -- x : Z^{q+1}(M₀)
  let desc (i : ℕ) : cocycles (M_ i).toRep (q + 1) := i.rec x fuel
  let component (i : ℕ) := ((M_ i).toCochainsIso q).symm (summand i (desc i))
  -- this is the decomposition of x as ∑ i, d (component i)
  suffices toCocycles M q (q + 1) (IsFilterComplete.sum C_ component) =
      (cocyclesMapIso (Subrep.isoOfEqTop hm0) (q + 1)).toLinearEquiv x by
    rw [← this]
    exact toCocycles_comp_π_apply ..
  have : IsFilterComplete (Z_ ∘ toDual) := ‹_›
  rw [IsFilterComplete.map_sum (G := Z_) fun i _ ↦ (M_ i).toCocycles_mem_toCocycles]
  refine Filtration.ext (Z_ ∘ toDual) fun i ↦ ?_
  refine sub_mem_trans (IsFilterComplete.sum_sub_mem Z_) <| sub_mem_symm ?_
  -- x - ∑ j < i, d (component j) = desc i
  suffices cocyclesMap (.id G) (Subrep.subtype _) (q + 1) x -
      ∑ j ∈ Finset.range i, toCocycles M q (q + 1) (component j) =
      cocyclesMap (.id G) (Subrep.subtype _) (q + 1) (desc i) from
    this ▸ (((M_ (toDual i)).toCocyclesIso _).symm (desc i)).2
  induction i with
  | zero => rw [Finset.sum_range_zero, sub_zero]; rfl
  | succ i ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    simp only [desc]
    conv_lhs => rw [← h₂ i (Nat.rec x fuel i)]
    rw [map_add]
    simp_rw [← ConcreteCategory.comp_apply, ← cocyclesMap_id_comp, Subrep.inclusion_comp_subtype,
      toCycles_naturality, ConcreteCategory.comp_apply]
    exact add_sub_cancel_right _ _

end

end groupCohomology
