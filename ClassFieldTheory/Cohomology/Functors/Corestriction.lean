/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Aaron Liu, Yunzhou Xie
-/
module

public import ClassFieldTheory.Cohomology.Functors.UpDown
public import ClassFieldTheory.Mathlib.Algebra.Module.Torsion.Basic
public import ClassFieldTheory.Mathlib.CategoryTheory.Category.Basic
public import ClassFieldTheory.Mathlib.CategoryTheory.Category.Cat
public import ClassFieldTheory.Mathlib.GroupTheory.GroupAction.Quotient

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

@[expose] public noncomputable section

open
  Rep
  dimensionShift
  groupCohomology
  CategoryTheory
  Limits

variable {R : Type} [CommRing R] -- R a comm ring
variable {G : Type} [Group G] {S : Subgroup G} -- G a group, S a subgroup

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace Rep.dimensionShift

@[simp]
lemma δUpNatIso_hom_app (n : ℕ) (M : Rep R G) :
    (δUpNatIso n).hom.app M = δ (shortExact_upSES M) (n + 1) (n + 2) rfl :=
  rfl

/-- If `S ⊆ G` then `δ : Hⁿ⁺¹(S, (up M) ↓ S) ⟶ Hⁿ⁺²(S, M ↓ S)` is an isomorphism. -/
instance isIso_δ_upSES_res (M : Rep R G) (n : ℕ) :
    IsIso (δ (shortExact_upSES_res M S.subtype) (n + 1) (n + 2) rfl) :=
  isIso_δ_up_res M S.subtype_injective (n + 1)

variable (S) in
/-- The connecting homomorphism `δ : Hⁿ⁺¹(S, (up M) ↓ S) ⟶ Hⁿ⁺²(S, M ↓ S)` for a subgroup
`S ⊆ G`, as a natural isomorphism in `M`. -/
def δUpResNatIso (n : ℕ) :
    up ⋙ resFunctor S.subtype ⋙ functor R S (n + 1) ≅
      resFunctor S.subtype ⋙ functor R S (n + 2) :=
  NatIso.ofComponents
    (fun M ↦ asIso (δ (shortExact_upSES_res M S.subtype) (n + 1) (n + 2) rfl)) fun {M N} f ↦
      .symm <| δ_naturality (shortExact_upSES_res M S.subtype) (shortExact_upSES_res N S.subtype)
        ((resFunctor S.subtype).mapShortComplex.map (upShortComplex.map f)) (n + 1) (n + 2) rfl

@[simp]
lemma δUpResNatIso_hom_app (n : ℕ) (M : Rep R G) :
    (δUpResNatIso S n).hom.app M = δ (shortExact_upSES_res M S.subtype) (n + 1) (n + 2) rfl :=
  rfl

@[simp]
lemma δUpResNatIso_inv_app (n : ℕ) (M : Rep R G) :
    (δUpResNatIso S n).inv.app M =
      inv (δ (shortExact_upSES_res M S.subtype) (n + 1) (n + 2) rfl) :=
  rfl

end Rep.dimensionShift

namespace groupCohomology

-- let V be an R[G]-module
lemma cores_aux₁ {V : Type} [AddCommMonoid V] [Module R V] (ρ : Representation R G V)
    -- if v ∈ V is S-invariant
    (v : V) (hv : ∀ s ∈ S, (ρ s) v = v) (g₁ g₂ : G)
    -- then for g₁ and g₂ in G such that g₁S=g₂S, then g₁•v=g₂•v
    (h : (QuotientGroup.mk g₁ : G ⧸ S) = QuotientGroup.mk g₂) : ρ g₁ v = ρ g₂ v := by
  rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by simp, map_mul, mul_apply_eq_comp,
  hv _ (QuotientGroup.eq.1 h)]

-- Cor: if X is any finite set and s₁, s₂ : X → G are such that X -> G -> G/S is a bijection
-- for both of them, then ∑_g s₁(g)v = ∑_g s₂(g)v for v in M^S
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
@[simps]
def _root_.Rep.cores₀_obj (V : Rep R G) :
    -- Defining an R-linear map from V^S to V^G
    (V ↓ S.subtype).ρ.invariants →ₗ[R] V.ρ.invariants where
  toFun x := ⟨∑ i : G ⧸ S, V.ρ i.out x.1, fun g ↦ by
    simp only [map_sum, ← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul]
    let : Fintype (G ⧸ S) := Subgroup.fintypeQuotientOfFiniteIndex
    refine (cores_aux₂ V.ρ x.1 (by simpa [-SetLike.coe_mem] using x.2) (by simp) ?_).symm
    simp_rw [QuotientGroup.mk_mul', QuotientGroup.out_eq', MulAction.bijective]⟩
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' := by simp [Finset.smul_sum]

/-- `Rep.cores₀_obj` is natural in `V`. -/
@[reassoc]
lemma _root_.Rep.cores₀_obj_naturality {X Y : Rep R G} (f : X ⟶ Y) :
    (invariantsFunctor R S).map ((Rep.resFunctor S.subtype).map f) ≫
      ModuleCat.ofHom (Rep.cores₀_obj Y) =
    ModuleCat.ofHom (Rep.cores₀_obj X) ≫ (invariantsFunctor R G).map f := by
  ext; simp [LinearMap.codRestrict, Rep.cores₀_obj_apply_coe _, hom_comm_apply]

/-- The corestriction functor on H^0 for S ⊆ G a finite index subgroup, as a
functor `H^0(S,-) → H^0(G,-)`. -/
@[simps]
def cores₀ : Rep.resFunctor S.subtype ⋙ functor R S 0 ⟶ functor R G 0 where
  app M := (H0Iso (M ↓ S.subtype)).hom ≫ ModuleCat.ofHom (Rep.cores₀_obj M) ≫ (H0Iso M).inv
  naturality X Y f := by
    simp [-functor_map, ← H0NatIso_hom_app, ← H0NatIso_inv_app, cores₀_obj_naturality_assoc]

/-- Naturality of `cores₀`, stated in simp-normal form. -/
@[reassoc (attr := simp)]
lemma cores₀_naturality {X Y : Rep R G} (f : X ⟶ Y) :
    (functor R S 0).map (resMap S.subtype f) ≫ cores₀.app Y =
      cores₀.app X ≫ (functor R G 0).map f :=
  cores₀.naturality f

/-- The morphism `H¹(S, M↓S) ⟶ H¹(G, M)`. -/
def cores₁_obj (M : Rep R G) :
    -- defining H¹(S, M↓S) ⟶ H¹(G, M) by a diagram chase
    (functor R S 1).obj (M ↓ S.subtype) ⟶ (functor R G 1).obj M := by
  -- Recall we have 0 ⟶ M ⟶ coind₁'^G M ⟶ up_G M ⟶ 0 a short exact sequence
  -- of `G`-modules which restricts to a short exact sequence of `S`-modules.
  -- Since `coind₁'^G M` has trivial cohomology, δ : H⁰(S,(up_G M)↓S) ⟶ H¹(S,M↓S) is
  -- surjective (the instance `epi_δUpRes_app`) with kernel the image of H⁰(S,(coind₁'^G M)↓S).
  -- So it suffices to give a map H⁰(S,(up_G M)↓S) ⟶ H¹(G,M) killing H⁰(S,(coind₁'^G M)↓S),
  -- namely cores₀ : H⁰(S,up_G M↓S) ⟶ H⁰(G,up_G M) followed by δ : H⁰(G,up_G M) ⟶ H¹(G,M).
  refine (exact_δUpRes M S.subtype).desc (cores₀.app _ ≫ δUp.app M) ?_
  -- By naturality of `cores₀`, the composite
  -- H⁰(S,(coind₁'^G M)↓S) ⟶ H⁰(S,(up_G M)↓S) ⟶ H⁰(G, up_G M) ⟶ H¹(G, M) equals
  -- H⁰(S,(coind₁'^G M)↓S) ⟶ H⁰(G,(coind₁'^G M)) ⟶ H⁰(G, up_G M) ⟶ H¹(G, M),
  -- and the last two maps compose to zero.
  simp [-functor_map, -δUp_app, -cores₀_app, cores₀_naturality_assoc, map_up_π_comp_δUp, comp_zero]

@[reassoc]
lemma commSq_cores₁ (M : Rep R G) :
    δ (shortExact_upSES_res M S.subtype) 0 1 rfl ≫ cores₁_obj (S := S) M =
      (cores₀ (S := S)).app _ ≫ δ (shortExact_upSES M) 0 1 rfl :=
  (exact_δUpRes M S.subtype).g_desc _ _

theorem cores₁_naturality (X Y : Rep R G) (f : X ⟶ Y) :
    (resFunctor S.subtype ⋙ functor R (↥S) 1).map f ≫ cores₁_obj Y =
    cores₁_obj X ≫ (functor R G 1).map f := by
  have : Epi (δ (shortExact_upSES_res X S.subtype) 0 1 rfl) :=
    epi_δ_up_zero_res (R := R) (φ := S.subtype) X S.subtype_injective
  symm
  refine CategoryTheory.cubeLemma
    (H0 (up.obj X ↓ S.subtype)) (H1 (X ↓ S.subtype)) (H0 (up.obj X)) (H1 X)
    (H0 (up.obj Y ↓ S.subtype)) (H1 (Y ↓ S.subtype)) (H0 (up.obj Y)) (H1 Y)
    -- four ?_ are the maps in the conclusion of the lemma
    (δ (shortExact_upSES_res X S.subtype) 0 1 rfl) (δ (shortExact_upSES X) 0 1 rfl)
    (δ (shortExact_upSES_res Y S.subtype) 0 1 rfl) (δ (shortExact_upSES Y) 0 1 rfl)
    (cores₀.app (up.obj X)) _ (cores₀.app (up.obj Y)) _
    (map (.id S) ((resFunctor S.subtype).map (up.map f)) 0) _
    (map (.id G) (up.map f) 0) _
    ?_ ?_ ?_ ?_ (by exact (cores₀ (S := S)|>.naturality (X := up.obj X) (up.map f)).symm) this
  all_goals symm
  · exact commSq_cores₁ X
  · exact commSq_cores₁ Y
  · exact δ_naturality (shortExact_upSES_res X S.subtype) (shortExact_upSES_res Y S.subtype)
      ((upShortComplex ⋙ (resFunctor S.subtype).mapShortComplex).map f) 0 1 rfl
  · exact δ_naturality (shortExact_upSES X) (shortExact_upSES Y)
      ⟨f, coind₁'.map f, up.map f, rfl, by aesop_cat⟩ 0 1 rfl

/-- Corestriction on objects in group cohomology. -/
def cores_obj : (M : Rep R G) → (n : ℕ) →
    (functor R S n).obj (M ↓ S.subtype) ⟶ (functor R G n).obj M
| M, 0 => cores₀.app M
| M, 1 => cores₁_obj M
| M, (d + 2) =>
  -- δ : H^{d+1}(G,up -) ≅ H^{d+2}(G,-)
  let up_δ_bottom_Iso := Rep.dimensionShift.δUpNatIso (R := R) (G := G) d
  -- `M ⟶ coind₁'^G M ⟶ up_G M` as a complex of S-modules
  let upsc_top := (upShortComplex.obj M).map (resFunctor S.subtype)
  -- the above complex of S-modules is exact
  have htopexact : upsc_top.ShortExact := shortExact_upSES_res M S.subtype
  -- so δ : H^{d+1}(S,up_G M) ≅ H^{d+2}(S,M)...
  let up_δ_top_isIso : IsIso (δ htopexact (d + 1) (d + 2) rfl) := by
    -- ...because `coind₁'^G M` has trivial cohomology as S-module
    -- have := M.coind₁'_trivialCohomology
    have : upsc_top.X₂.TrivialCohomology := Rep.TrivialCohomology.res_subtype (coind₁'.obj M)
    refine isIso_δ_of_isZero (htopexact) (d + 1) ?_ ?_
    all_goals simpa only [upSES_X₂] using isZero_of_trivialCohomology
  let ih := cores_obj (up.obj M) (d + 1)
  (asIso (δ htopexact (d + 1) (d + 2) rfl)).inv ≫ ih ≫ (up_δ_bottom_Iso).hom.app M

/-- `cores_obj M (n + 2)` is `δ⁻¹ ≫ cores_obj (up.obj M) (n + 1) ≫ δ`, with the connecting
homomorphisms written as components of `δUpResNatIso` and `δUpNatIso`. -/
lemma cores_obj_succ_succ (M : Rep R G) (n : ℕ) :
    cores_obj M (n + 2) =
      (δUpResNatIso S n).inv.app M ≫ cores_obj (up.obj M) (n + 1) ≫ (δUpNatIso n).hom.app M :=
  rfl

theorem cores_succ_naturality (n : ℕ) (X Y : Rep R G) (f : X ⟶ Y) :
    (resFunctor S.subtype ⋙ functor R (↥S) (n + 1)).map f ≫ cores_obj Y (n + 1) =
    cores_obj X (n + 1) ≫ (functor R G (n + 1)).map f := by
  revert X Y f
  induction n with
  | zero => exact fun _ _ _ ↦ cores₁_naturality ..
  | succ n ih =>
    intro X Y f
    -- `cores_obj _ (n + 2)` is a component of the composite natural transformation
    -- `δ⁻¹ ≫ (cores_obj _ (n + 1), whiskered by `up`) ≫ δ`, so it is natural.
    have := ((δUpResNatIso S n).inv ≫
      Functor.whiskerLeft up ⟨fun M ↦ cores_obj M (n + 1), ih⟩ ≫ (δUpNatIso n).hom).naturality f
    simpa [cores_obj_succ_succ] using this

variable (R) (S) in
/-- Corestriction as a natural transformation. -/
def coresNatTrans (n : ℕ) : resFunctor S.subtype ⋙ functor R S n ⟶ functor R G n where
  app M := (groupCohomology.cores_obj M n)
  naturality X Y f := match n with
    | 0 => cores₀.naturality f
    | n + 1 => cores_succ_naturality n X Y f

@[simp]
lemma coresNatTrans_app (n : ℕ) (M : Rep R G) : (coresNatTrans R S n).app M = cores_obj M n :=
  rfl

lemma map_H0Iso_hom_f_apply'.{u} {k G H : Type u} [CommRing k] [Group G] [Group H] {A : Rep k H}
    {B : Rep k G} (f : G →* H) (φ : A ↓ f ⟶ B) (x : groupCohomology A 0) :
    (H0Iso B).hom.hom ((map f φ 0).hom x) =
    φ.hom ((H0Iso A).hom.hom x : A) :=
  map_H0Iso_hom_f_apply ..

-- `simp` does a lot of work here, and it was quite some effort getting
-- it to do so, so I hope this proof never breaks...
lemma cores_res₀ : rest (R := R) (S.subtype) 0 ≫ cores₀ = S.index • (.id _) := by
  ext M v
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback (H0Iso M).hom)
  ext
  simp [rest, Subgroup.index, cores₀_obj, groupCohomology.map_H0Iso_hom_f_apply' _,
    (M.ρ.mem_invariants ((H0Iso M).hom.hom v)).1 (Subtype.prop _), -nsmul_eq_mul]

/-!
            rest                       cores
Hⁿ(G, up M) ---> Hⁿ(S, upM ↓ S.subtype) ---> Hⁿ(G, up M)
    |                                         |
    | δ                                       | δ
    v       rest                       cores  v
Hⁿ⁺¹(G, M)  ---> Hⁿ⁺¹(S, M ↓ S.subtype) ---> Hⁿ⁺¹(G, M)

-/
lemma commSqₙ (n : ℕ) (M : Rep R G) :
    (rest S.subtype n ≫ coresNatTrans R S n).app (up.obj M) ≫ δ (shortExact_upSES M) n (n + 1) rfl =
      δ (shortExact_upSES M) n (n + 1) rfl ≫ (rest S.subtype (n + 1) ≫
        coresNatTrans R S (n + 1)).app M := by
  rw [NatTrans.comp_app, NatTrans.comp_app]
  match n with
  | 0 =>
    exact comp_commSq _ _ _ _ _ _ _ (δ (shortExact_upSES_res M S.subtype) 0 1 rfl)
      (rest_δ_naturality (shortExact_upSES M) S.subtype 0 1 rfl |>.symm) (commSq_cores₁ ..|>.symm)
  | n + 1 =>
    refine comp_commSq _ _ _ _ _ _ _ (δ (shortExact_upSES_res M S.subtype) (n + 1) (n + 2) rfl)
      (rest_δ_naturality (shortExact_upSES M) S.subtype (n + 1) (n + 2) rfl).symm ?_
    simp [cores_obj_succ_succ]

lemma cores_res (n : ℕ) :
    (rest (R := R) (S.subtype) n ≫ coresNatTrans R S n : functor R G n ⟶ functor R G n) =
      S.index • (.id _) := by
  induction n with
  | zero => exact cores_res₀
  | succ n ih =>
    ext M : 2
    have : Epi (δ (shortExact_upSES M) n (n + 1) rfl) :=
      match n with
      | 0 => δ_up_zero_epi ..
      | m + 1 => δ_up_isIso M m|>.epi_of_iso _
    rw [← cancel_epi (δ (shortExact_upSES M) n (n + 1) rfl), ← commSqₙ n M, ih]
    simp

/-- Any element of H^n-hat (n ∈ ℤ) is `|G|`-torsion. -/
lemma torsion_of_finite_of_neZero {n : ℕ} [NeZero n] (M : Rep R G)
    (x : groupCohomology M n) : Nat.card G • x = 0 := by
  if hG : Infinite G then simp else
  simp only [not_infinite_iff_finite] at hG
  have := by simpa [-nsmul_eq_mul] using (LinearMap.ext_iff.1 <| ModuleCat.hom_ext_iff.1
    congr(NatTrans.app $(cores_res (R := R) n (G := G) (S := ⊥)) M)) x
  simp [← this, rest, IsZero.eq_zero_of_tgt isZero_of_trivialCohomology <|
    map _ (𝟙 (M ↓ (⊥ : Subgroup G).subtype)) n]

-- /-- Any element of H^n-hat (n ∈ ℤ) is `|G|`-torsion. -/
-- lemma tateCohomology_torsion {n : ℤ} [Fintype G] (M : Rep R G) (x : (tateCohomology n).obj M) :
--     Nat.card G • x = 0 := sorry

-- Should the above really be a statement about a functor?
-- Something like this?

-- instance (n : ℤ) [Finite G] : Functor.Additive (tateCohomology (R := R) (G := G) n) := sorry

-- this doesn't work
-- lemma tateCohomology_torsion' {n : ℤ} [Finite G] :
--     (Nat.card G) • (CategoryTheory.NatTrans.id (tateCohomology (R := R) (G := G) n)) = 0 := sorry

-- p^infty-torsion injects into H^(Sylow) (for group cohomology)

lemma pTorsion_eq_sylowTorsion {n : ℕ} [NeZero n] [Finite G] (M : Rep R G)
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (x : groupCohomology M n) :
    (∃ d, (p ^ d) • x = 0) ↔ x ∈ Submodule.torsionBy R _ (Nat.card P) where
  mp := by
    rintro ⟨d, hd⟩
    obtain ⟨k, hk1, hk2⟩ := Nat.dvd_prime_pow Fact.out|>.1 <| Nat.gcd_dvd_right (Nat.card G) (p ^ d)
    obtain ⟨m, hm⟩ := P.pow_dvd_card_of_pow_dvd_card (hk2 ▸ Nat.gcd_dvd_left (Nat.card G) (p ^ d))
    simp [hm, mul_comm _ m, mul_smul, - Nat.cast_pow, Nat.cast_smul_eq_nsmul, ← hk2, smul_comm m]
    simp [smul_comm _ m, hd, torsion_of_finite_of_neZero]
  mpr h := ⟨(Nat.card G).factorization p, P.card_eq_multiplicity ▸ by
    simpa [Nat.cast_smul_eq_nsmul] using h⟩

lemma injects_to_sylowCoh {n : ℕ} [NeZero n] [Finite G] (M : Rep R G)
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) : Function.Injective
    ((map P.toSubgroup.subtype (𝟙 (_ ↓ _)) n).hom ∘ₗ (Module.IsTorsionBy.coprime_decompose
    (M := groupCohomology M n) (Subgroup.card_mul_index P.toSubgroup).symm
    (Sylow.card_coprime_index P) (fun x ↦ Nat.cast_smul_eq_nsmul R (Nat.card G) x ▸
    torsion_of_finite_of_neZero M x)).symm.toLinearMap ∘ₗ LinearMap.inl _ _ _) :=
  Function.Injective.of_comp (f := (cores_obj M n).hom) <| by
  have eq := by simpa [rest_app, coresNatTrans] using
    ModuleCat.hom_ext_iff.1 congr(NatTrans.app $(cores_res (R := R) (G := G) (S := P) n) M)
  simp only [functor_obj, LinearMap.coe_comp, LinearMap.coe_inl, ← Function.comp_assoc]
  simp only [← LinearMap.coe_comp, eq, Module.End.mul_eq_comp, LinearMap.comp_id,
    LinearEquiv.coe_coe]
  intro ⟨x1, hx1⟩ ⟨x2, hx2⟩
  simp only [Function.comp_apply, Module.IsTorsionBy.coprime_decompose_symm_apply,
    ZeroMemClass.coe_zero, smul_zero, add_zero, map_smul, natCast_apply_eq_smul,
    Subtype.mk.injEq]
  intro h
  replace h := by simpa using congr((· + ((Nat.card P).gcdA P.toSubgroup.index : R) • 0) $h)
  nth_rw 1 [← Submodule.mem_torsionBy_iff _ _|>.1 hx1,
    ← Submodule.mem_torsionBy_iff _ _|>.1 hx2] at h
  rw [← Nat.cast_smul_eq_nsmul R P.toSubgroup.index, ← Nat.cast_smul_eq_nsmul R P.toSubgroup.index,
    ← smul_assoc, ← smul_assoc, ← smul_assoc, ← smul_assoc] at h
  simp only [← add_smul, smul_eq_mul] at h
  rw [← Ring.intCast_ofNat, ← Int.cast_mul, ← Ring.intCast_ofNat (Nat.card P), ← Int.cast_mul,
    ← Int.cast_add, add_comm, mul_comm, mul_comm _ (P.toSubgroup.index : ℤ),
    ← Nat.gcd_eq_gcd_ab, Nat.coprime_iff_gcd_eq_one.1 (Sylow.card_coprime_index P)] at h
  simpa using h

lemma groupCohomology_Sylow {n : ℕ} (hn : 0 < n) [Finite G] (M : Rep R G)
    (x : groupCohomology M n) (p : ℕ) [Fact p.Prime] (P : Sylow p G) (hx : ∃ d, (p ^ d) • x = 0)
    (hx' : x ≠ 0) : ((rest (P.toSubgroup.subtype) n).app M).hom x ≠ 0 := by
  classical
  have : NeZero n := ⟨ne_of_gt hn⟩
  simpa [Functor.comp_obj, functor_obj, rest_app, ne_eq] using by_contra fun hx2 ↦ hx' <|
    @Subtype.ext_iff _ (p := fun x ↦ x ∈ Submodule.torsionBy R (groupCohomology M n) (Nat.card P))
    ⟨x, pTorsion_eq_sylowTorsion M p P x|>.1 hx⟩ 0|>.1 <| groupCohomology.injects_to_sylowCoh M p P
    (by simp [not_not.1 hx2])

end groupCohomology
