/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Aaron Liu
-/
import ClassFieldTheory.Cohomology.Functors.UpDown
import ClassFieldTheory.Mathlib.GroupTheory.GroupAction.Quotient
import ClassFieldTheory.Mathlib.CategoryTheory.Category.Cat
import ClassFieldTheory.Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Corestriction

If `S` is a finite index subgroup of `G` and `M` is a `G`-module
then there's a corestriction map `H^n(S,M) → H^n(G,M)`, defined
by averaging on `H^0` and then by dimension shifting for
general `H^n`.

## Remarks

Cassels-Froehlich define cores on *homology* for an arbitrary
morphism `S → G` and then if `G` is finite they
extend it to Tate cohomology by dimension shifting.
It agrees with our definition on H^0-hat so presumably
agrees with our definition in general for G finite.

Arguably this filename has too large a number.

## TODO

cores o res = multiplication by index
-/

noncomputable section

open
  Rep
  dimensionShift
  groupCohomology
  CategoryTheory
  Limits

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] {S : Subgroup G}

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace groupCohomology

lemma cores_aux₁ {V : Type} [AddCommMonoid V] [Module R V] (ρ : Representation R G V)
    (v : V) (hv : ∀ s ∈ S, (ρ s) v = v) (g₁ g₂ : G)
    (h : (QuotientGroup.mk g₁ : G ⧸ S) = QuotientGroup.mk g₂) : ρ g₁ v = ρ g₂ v := by
  rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by simp, map_mul, Module.End.mul_apply,
  hv _ (QuotientGroup.eq.1 h)]

lemma cores_aux₂ {X : Type} {V : Type} [Fintype X] [AddCommGroup V] [Module R V] {s₁ : X → G}
    {s₂ : X → G} (ρ : Representation R G V) (v : V) (hv : ∀ s ∈ S, (ρ s) v = v)
    (hs₁ : Function.Bijective (fun x ↦ QuotientGroup.mk (s₁ x) : X → G ⧸ S))
    (hs₂ : Function.Bijective (fun x ↦ QuotientGroup.mk (s₂ x) : X → G ⧸ S)) :
    ∑ x : X, ρ (s₁ x) v = ∑ x : X, ρ (s₂ x) v := by
  let e1 : X ≃ G ⧸ S := Equiv.ofBijective (QuotientGroup.mk ∘ s₁) hs₁
  let e2 : X ≃ G ⧸ S := Equiv.ofBijective (QuotientGroup.mk ∘ s₂) hs₂
  exact Finset.sum_equiv (e1.trans e2.symm) (by simp) fun i _ ↦ cores_aux₁ ρ v hv _ _ <| by
    rw [Equiv.trans_apply]
    exact (e2.apply_symm_apply _).symm

variable [S.FiniteIndex]

/-- The H^0 corestriction map for S ⊆ G a finite index subgroup, as an `R`-linear
map on invariants. -/
def _root_.Representation.cores₀_obj {V : Type} [AddCommGroup V] [Module R V] (ρ : Representation R G V) :
    Representation.invariants (MonoidHom.comp ρ S.subtype) →ₗ[R] ρ.invariants where
  toFun x := ⟨∑ i : G ⧸ S, i.lift (ρ · x.1) (fun a b h ↦ cores_aux₁ ρ x.1
    (by simpa using Representation.mem_invariants (MonoidHom.comp ρ S.subtype) x.1|>.1 <| by simp)
    a b (Quotient.sound h)), fun g ↦ by
    simp only [map_sum]
    letI : Fintype (G ⧸ S) := Subgroup.fintypeQuotientOfFiniteIndex
    exact Finset.sum_bijective (ι := G ⧸ S) (g • ·) (MulAction.bijective g) (by aesop) <| by
      refine Quotient.ind <| by simp⟩
  map_add' x y := by
    ext
    simpa [← Finset.sum_add_distrib] using Finset.sum_congr rfl fun i _ ↦
      Quotient.inductionOn i (by simp)
  map_smul' := by
    simp only [SetLike.val_smul, map_smul, RingHom.id_apply, Subtype.forall,
      Representation.mem_invariants, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
      SetLike.mk_smul_mk, Finset.smul_sum, Subtype.mk.injEq]
    intros
    congr! with i
    exact Quotient.inductionOn i (by simp)

/-- The corestriction functor on H^0 for S ⊆ G a finite index subgroup, as a
functor `H^0(S,-) → H^0(G,-)`. -/
def cores₀ : Rep.res S.subtype ⋙ functor R S 0 ⟶ functor R G 0 where
  app M :=
    (H0Iso (M ↓ S.subtype)).hom ≫ (ModuleCat.ofHom (Representation.cores₀_obj M.ρ)) ≫ (H0Iso M).inv
  naturality := by
    intro X Y f
    simp_rw [← Category.assoc]
    rw [(H0Iso Y).comp_inv_eq]
    simp_rw [Category.assoc]
    rw [functor_map, map_id_comp_H0Iso_hom, (H0Iso X).inv_hom_id_assoc, Functor.comp_map,
      functor_map, map_id_comp_H0Iso_hom_assoc, (H0Iso (X ↓ S.subtype)).cancel_iso_hom_left]
    ext x
    simp only [Action.res_obj_V, res_obj_ρ, Representation.cores₀_obj, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, invariantsFunctor_map_hom, Action.res_map_hom, LinearMap.coe_comp,
      LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, LinearMap.codRestrict_apply, coe_hom,
      Submodule.coe_subtype, LinearMap.comp_codRestrict, map_sum]
    congr! with i
    exact Quotient.inductionOn i (fun g ↦ by simpa using congr($(f.comm g) x.val).symm)
    -- simp_rw [ConcreteCategory.comp_apply]


/-- The morphism `H¹(S, M↓S) ⟶ H¹(G, M)`. -/
def cores₁_obj [DecidableEq G] (M : Rep R G) :
    -- defining H¹(S, M↓S) ⟶ H¹(G, M) by a diagram chase
    (functor R S 1).obj (M ↓ S.subtype) ⟶ (functor R G 1).obj M := by
  -- Recall we have 0 ⟶ M ⟶ coind₁'^G M ⟶ up_G M ⟶ 0 a short exact sequence
  -- of `G`-modules which restricts to a short exact sequence of `S`-modules.
  -- First I claim δ : H⁰(S,(up_G M)↓S) ⟶ H¹(S,M↓S) is surjective
  have : Epi (mapShortComplex₃ (up_shortExact_res M S.subtype) (rfl : 0 + 1 = 1)).g :=
    -- because `coind₁'^G M` has trivial cohomology
    epi_δ_up_zero_res (R := R) (φ := S.subtype) M S.subtype_injective
  -- so it suffices to give a map H⁰(S,(up_G M)↓S) ⟶ H¹(G,M) such that the
  -- image of H⁰(S,(coind₁'^G M)↓S) is in the kernel of that map
  refine (mapShortComplex₃_exact (up_shortExact_res M S.subtype) (rfl : 0 + 1 = 1)).desc ?_ ?_
  · -- The map H⁰(S,up_G M)↓S) ⟶ H¹(G,M) is just the composite of
    -- cores₀ : H⁰(S,up_G M↓S) ⟶ H⁰(G,up_G M) and δ : H⁰(G,up_G M) ⟶ H¹(G,M)
    exact (cores₀.app _) ≫ (δ (up_shortExact M) 0 1 rfl)
  · -- We now need to prove that the induced map
    -- H⁰(S,(coind₁'^G M)↓S) ⟶ H¹(G,M) is 0
    -- This is a diagram chase. The map is H⁰(S,(coind₁'^G M)↓S) ⟶ H⁰(S,(up_G M)↓S)
    -- (functoriality of H⁰) followed by cores₀ : H⁰(S,(up_G M)↓S) ⟶ H⁰(G, up_G M)
    -- followed by δ : H⁰(G, up_G M) ⟶ H¹(G, M). First put the brackets around
    -- the first two terms.
    rw [← Category.assoc]
    -- now apply naturality of cores₀, because I want to change
    -- H⁰(S,(coind₁'^G M)↓S) ⟶ H⁰(S,(up_G M)↓S) ⟶ H⁰(G, up_G M) to
    -- H⁰(S,(coind₁'^G M)↓S) ⟶ H⁰(G,(coind₁'^G M)) ⟶ H⁰(G, up_G M)
    let bar := cokernel.π (coind₁'_ι.app M)
    -- cores₀ : res S.subtype ⋙ functor R (↥S) 0 ⟶ functor R G 0
    have baz := cores₀.naturality (F := (res S.subtype ⋙ functor R (↥S) 0)) bar
    change ((res S.subtype ⋙ functor R (↥S) 0).map bar ≫ (cores₀.app (up.obj M))) ≫ _ = 0
    change _ ≫ (cores₀.app (up.obj M)) = _ ≫ _ at baz
    rw [baz, Category.assoc]
    convert comp_zero -- cancel first functor
    exact (mapShortComplex₃ (up_shortExact M) (rfl : 0 + 1 = 1)).zero

@[reassoc]
lemma commSq_cores₁ [DecidableEq G] (M : Rep R G) :
  δ (up_shortExact_res M S.subtype) 0 1 rfl ≫ cores₁_obj (S := S) M =
    (cores₀ (S := S)).app _ ≫ δ (up_shortExact M) 0 1 rfl :=
  have : Epi (mapShortComplex₃ (up_shortExact_res M S.subtype) (rfl : 0 + 1 = 1)).g :=
    epi_δ_up_zero_res (R := R) (φ := S.subtype) M S.subtype_injective
  (mapShortComplex₃_exact (up_shortExact_res M S.subtype) (rfl : 0 + 1 = 1)).g_desc _ _

theorem cores₁_naturality  (X Y : Rep R G) (f : X ⟶ Y) [DecidableEq G] :
    (res S.subtype ⋙ functor R (↥S) 1).map f ≫ cores₁_obj Y =
    cores₁_obj X ≫ (functor R G 1).map f := by
  haveI : Epi (δ (up_shortExact_res X S.subtype) 0 1 rfl) :=
    epi_δ_up_zero_res (R := R) (φ := S.subtype) X S.subtype_injective
  symm
  refine CategoryTheory.cubeLemma
    (H0 (up.obj X ↓ S.subtype)) (H1 (X ↓ S.subtype)) (H0 (up.obj X)) (H1 X)
    (H0 (up.obj Y ↓ S.subtype)) (H1 (Y ↓ S.subtype)) (H0 (up.obj Y)) (H1 Y)
    -- four ?_ are the maps in the conclusion of the lemma
    (δ (up_shortExact_res X S.subtype) 0 1 rfl) (δ (up_shortExact X) 0 1 rfl)
    (δ (up_shortExact_res Y S.subtype) 0 1 rfl) (δ (up_shortExact Y) 0 1 rfl)
    (cores₀.app (up.obj X)) _ (cores₀.app (up.obj Y)) _
    (map (.id S) ((res S.subtype).map (up.map f)) 0) _
    (map (.id G) (up.map f) 0) _
    ?_ ?_ ?_ ?_ (by exact (cores₀ (S := S)|>.naturality (X := up.obj X) (up.map f)).symm) this
  all_goals symm
  · exact commSq_cores₁ X
  · exact commSq_cores₁ Y
  · exact δ_naturality (up_shortExact_res X S.subtype) (up_shortExact_res Y S.subtype)
      { τ₁ := (res S.subtype).map f
        τ₂ := (res S.subtype).map <| coind₁'.map f
        τ₃ := (res S.subtype).map <| up.map f
        comm₂₃ := by
          have := (upShortComplex.map f).comm₂₃
          simp only [upShortComplex_map_τ₂, upShortComplex_map_τ₃, ShortComplex.map_g] at this ⊢
          rw [← (res S.subtype).map_comp, this, (res S.subtype).map_comp]} 0 1 rfl
  · exact δ_naturality (up_shortExact X) (up_shortExact Y)
      ⟨f, coind₁'.map f, up.map f, rfl, by aesop_cat⟩ 0 1 rfl

/-- Corestriction on objects in group cohomology. -/
def cores_obj [DecidableEq G] : (M : Rep R G) → (n : ℕ) →
    (functor R S n).obj (M ↓ S.subtype) ⟶ (functor R G n).obj M
| M, 0 => cores₀.app M
| M, 1 => cores₁_obj M
| M, (d + 2) =>
  -- δ : H^{d+1}(G,up -) ≅ H^{d+2}(G,-)
  let up_δ_bottom_Iso := Rep.dimensionShift.δUpNatIso (R := R) (G := G) d
  -- `M ⟶ coind₁'^G M ⟶ up_G M` as a complex of S-modules
  let upsc_top := (upShortComplex.obj M).map (res S.subtype)
  -- the above complex of S-modules is exact
  have htopexact : upsc_top.ShortExact := up_shortExact_res M S.subtype
  -- so δ : H^{d+1}(S,up_G M) ≅ H^{d+2}(S,M)...
  let up_δ_top_isIso : IsIso (δ (htopexact) (d + 1) (d + 2) rfl) := by
    -- ...because `coind₁'^G M` has trivial cohomology as S-module
    -- have := M.coind₁'_trivialCohomology
    have : upsc_top.X₂.TrivialCohomology := Rep.TrivialCohomology.res_subtype (coind₁'.obj M)
    refine isIso_δ_of_isZero (htopexact) (d + 1) ?_ ?_
    all_goals simpa only [upShortComplex_obj_X₂] using isZero_of_trivialCohomology
  let ih := cores_obj (up.obj M) (d + 1)
  (asIso (δ (htopexact) (d + 1) (d + 2) rfl)).inv ≫ ih ≫ (up_δ_bottom_Iso).hom.app M

theorem cores_succ_naturality (n : ℕ) (X Y : Rep R G) (f : X ⟶ Y) [DecidableEq G] :
    (res S.subtype ⋙ functor R (↥S) (n + 1)).map f ≫ cores_obj Y (n + 1) =
    cores_obj X (n + 1) ≫ (functor R G (n + 1)).map f := by
  revert X Y f
  induction n with
  | zero => exact fun _ _ _ ↦ cores₁_naturality ..
  | succ n ih =>
    intro X Y f
    simp only [Functor.comp_obj, functor_obj, Functor.comp_map, functor_map, cores_obj,
      ShortComplex.map_X₃, upShortComplex_obj_X₃, up_obj, Functor.id_obj, coind₁'_obj,
      ShortComplex.map_X₁, upShortComplex_obj_X₁, asIso_inv, Category.assoc, IsIso.eq_inv_comp,
      δUpNatIso, Functor.comp_obj, up_obj, Functor.id_obj, coind₁'_obj, functor_obj,
      δUpIso, id_eq, NatIso.ofComponents_hom_app, asIso_hom]
    rw [← Category.assoc]
    have := δ_naturality (up_shortExact_res X S.subtype) (up_shortExact_res Y S.subtype)
      { τ₁ := (res S.subtype).map f
        τ₂ := (res S.subtype).map <| coind₁'.map f
        τ₃ := (res S.subtype).map <| up.map f
        comm₂₃ := by
          have := (upShortComplex.map f).comm₂₃
          simp only [upShortComplex_map_τ₂, upShortComplex_map_τ₃, ShortComplex.map_g] at this ⊢
          rw [← (res S.subtype).map_comp, this, (res S.subtype).map_comp]} (n + 1) (n + 2) rfl
    rw [this, Category.assoc, ← Category.assoc (δ _ _ _ _), IsIso.hom_inv_id, Category.id_comp,
      δ_naturality (up_shortExact X) (up_shortExact Y) ⟨f, coind₁'.map f, up.map f, rfl,
      by aesop_cat⟩ (n + 1) (n + 2) rfl, ← Category.assoc, ← Category.assoc]
    exact congr((· ≫ δ (up_shortExact _) _ _ _) $(ih (up.obj X) (up.obj Y) (up.map f)))

variable (R) (S) in
/-- Corestriction as a natural transformation. -/
def coresNatTrans (n : ℕ) [DecidableEq G] : Rep.res S.subtype ⋙ functor R S n ⟶ functor R G n where
  app M := (groupCohomology.cores_obj M n)
  naturality X Y f := match n with
    | 0 => cores₀.naturality f
    | n + 1 => cores_succ_naturality n X Y f

lemma cores_res₀ : resNatTrans R (S.subtype) 0 ≫ cores₀ = S.index • (.id _) := by
  ext N : 2
  simp only [functor_obj, cores₀, Functor.comp_obj, Action.res_obj_V, res_obj_ρ, NatTrans.comp_app,
    resNatTrans_app, NatTrans.app_nsmul, NatTrans.id_app']
  ext x
  simp only [Representation.cores₀_obj, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, ModuleCat.hom_smul, ModuleCat.hom_id,
    nsmul_eq_mul, Module.End.mul_apply, LinearMap.id_coe, id_eq, Module.End.natCast_apply]
  apply (H0Iso N).toLinearEquiv.injective
  simp only [Iso.toLinearEquiv, LinearEquiv.ofLinear_apply, Iso.inv_hom_id_apply,
    LinearMap.map_smul_of_tower]
  ext
  simp only [Subgroup.index, Nat.card_eq_fintype_card, SetLike.val_smul_of_tower]
  rw [← Finset.card_univ, ← Finset.sum_const]
  congr! with i
  induction i using QuotientGroup.induction_on
  simp only [Quotient.lift_mk]
  conv_lhs => enter [2]; tactic => convert groupCohomology.map_H0Iso_hom_f_apply S.subtype (𝟙 _) x -- BAD
  change (N.ρ _) ((@CategoryStruct.comp (ModuleCat R) (ModuleCat.moduleCategory R).toCategoryStruct
    (H0 N) (ModuleCat.of R ↥N.ρ.invariants)
    ((Action.res (ModuleCat R) S.subtype).obj N).V (H0Iso N).hom
    ((shortComplexH0 N).f ≫ (𝟙 ((Action.res (ModuleCat R) S.subtype).obj N):).hom)).hom x) = _ -- EVEN WORSE because of the smile face
  simp only [Action.res_obj_V, Action.id_hom, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply]
  erw [ModuleCat.hom_id] --BAD
  simp [shortComplexH0, N.ρ.mem_invariants ((ModuleCat.Hom.hom (H0Iso N).hom) x).1 |>.1 (by simp)]

lemma cores_res (M : Rep R G) (n : ℕ) [DecidableEq G] :
    ((groupCohomology.resNatTrans.{0} R (S.subtype) n) ≫
      (groupCohomology.coresNatTrans R S n) : functor R G n ⟶ functor R G n) =
      S.index • (.id _) :=
  match n with
  | 0 => cores_res₀
  | 1 => sorry
  | n + 2 => sorry

/-- Any element of H^n-hat (n ∈ ℤ) is `|G|`-torsion. -/
lemma tateCohomology_torsion {n : ℤ} [Fintype G] (M : Rep R G) (x : (tateCohomology n).obj M) :
    Nat.card G • x = 0 := sorry

-- Should the above really be a statement about a functor?
-- Something like this?

-- instance (n : ℤ) [Finite G] : Functor.Additive (tateCohomology (R := R) (G := G) n) := sorry

-- this doesn't work
-- lemma tateCohomology_torsion' {n : ℤ} [Finite G] :
--     (Nat.card G) • (CategoryTheory.NatTrans.id (tateCohomology (R := R) (G := G) n)) = 0 := sorry

-- p^infty-torsion injects into H^(Sylow) (for group cohomology)
lemma groupCohomology_Sylow {n : ℕ} (hn : 0 < n) [Finite G] (M : Rep R G)
    (x : groupCohomology M n) (p : ℕ) (P : Sylow p G) (hx : ∃ d, (p ^ d) • x = 0)
    (hx' : x ≠ 0) : (groupCohomology.rest (P.toSubgroup.subtype) n).app M x ≠ 0 := sorry

-- Want an analogous statement for Tate cohomology but I can't find restriction
-- in Tate cohomology
