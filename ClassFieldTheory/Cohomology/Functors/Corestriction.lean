/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Aaron Liu, Yunzhou Xie
-/
import ClassFieldTheory.Cohomology.Functors.UpDown
import ClassFieldTheory.Mathlib.Algebra.Module.Torsion.Basic
import ClassFieldTheory.Mathlib.CategoryTheory.Category.Basic
import ClassFieldTheory.Mathlib.CategoryTheory.Category.Cat
import ClassFieldTheory.Mathlib.GroupTheory.GroupAction.Quotient
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

variable {R : Type} [CommRing R] -- R a comm ring
variable {G : Type} [Group G] {S : Subgroup G} -- G a group, S a subgroup

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace groupCohomology

-- let V be an R[G]-module
lemma cores_aux₁ {V : Type} [AddCommMonoid V] [Module R V] (ρ : Representation R G V)
    -- if v ∈ V is S-invariant
    (v : V) (hv : ∀ s ∈ S, (ρ s) v = v) (g₁ g₂ : G)
    -- then for g₁ and g₂ in G such that g₁S=g₂S, then g₁•v=g₂•v
    (h : (QuotientGroup.mk g₁ : G ⧸ S) = QuotientGroup.mk g₂) : ρ g₁ v = ρ g₂ v := by
  rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by simp, map_mul, Module.End.mul_apply,
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
    letI : Fintype (G ⧸ S) := Subgroup.fintypeQuotientOfFiniteIndex
    refine (cores_aux₂ V.ρ x.1 (by simpa [-SetLike.coe_mem] using x.2) (by simp) ?_).symm
    simp_rw [QuotientGroup.mk_mul', QuotientGroup.out_eq', MulAction.bijective]⟩
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' := by simp [Finset.smul_sum]

/-- The corestriction functor on H^0 for S ⊆ G a finite index subgroup, as a
functor `H^0(S,-) → H^0(G,-)`. -/
@[simps]
def cores₀ : Rep.res S.subtype ⋙ functor R S 0 ⟶ functor R G 0 where
  app M :=
    (H0Iso (M ↓ S.subtype)).hom ≫ (ModuleCat.ofHom (Rep.cores₀_obj M)) ≫ (H0Iso M).inv
  naturality := by
    intro X Y f
    simp_rw [← Category.assoc]
    rw [(H0Iso Y).comp_inv_eq]
    simp_rw [Category.assoc]
    rw [functor_map, map_id_comp_H0Iso_hom, (H0Iso X).inv_hom_id_assoc, Functor.comp_map,
      functor_map, map_id_comp_H0Iso_hom_assoc, (H0Iso (X ↓ S.subtype)).cancel_iso_hom_left]
    ext x
    have comm := congr(∑ i : G ⧸ S, ModuleCat.Hom.hom $(f.comm i.out) x.val)
    simpa [Rep.cores₀_obj] using comm.symm

/-- The morphism `H¹(S, M↓S) ⟶ H¹(G, M)`. -/
def cores₁_obj (M : Rep R G) :
    -- defining H¹(S, M↓S) ⟶ H¹(G, M) by a diagram chase
    (functor R S 1).obj (M ↓ S.subtype) ⟶ (functor R G 1).obj M := by
  -- Recall we have 0 ⟶ M ⟶ coind₁'^G M ⟶ up_G M ⟶ 0 a short exact sequence
  -- of `G`-modules which restricts to a short exact sequence of `S`-modules.
  -- First I claim δ : H⁰(S,(up_G M)↓S) ⟶ H¹(S,M↓S) is surjective
  have : Epi (mapShortComplex₃ (shortExact_upSES_res M S.subtype) (rfl : 0 + 1 = 1)).g :=
    -- because `coind₁'^G M` has trivial cohomology
    epi_δ_up_zero_res (R := R) (φ := S.subtype) M S.subtype_injective
  -- so it suffices to give a map H⁰(S,(up_G M)↓S) ⟶ H¹(G,M) such that the
  -- image of H⁰(S,(coind₁'^G M)↓S) is in the kernel of that map
  refine (mapShortComplex₃_exact (shortExact_upSES_res M S.subtype) (rfl : 0 + 1 = 1)).desc ?_ ?_
  · -- The map H⁰(S,up_G M)↓S) ⟶ H¹(G,M) is just the composite of
    -- cores₀ : H⁰(S,up_G M↓S) ⟶ H⁰(G,up_G M) and δ : H⁰(G,up_G M) ⟶ H¹(G,M)
    exact (cores₀.app _) ≫ (δ (shortExact_upSES M) 0 1 rfl)
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
    exact (mapShortComplex₃ (shortExact_upSES M) (rfl : 0 + 1 = 1)).zero

@[reassoc]
lemma commSq_cores₁ (M : Rep R G) :
  δ (shortExact_upSES_res M S.subtype) 0 1 rfl ≫ cores₁_obj (S := S) M =
    (cores₀ (S := S)).app _ ≫ δ (shortExact_upSES M) 0 1 rfl :=
  have : Epi (mapShortComplex₃ (shortExact_upSES_res M S.subtype) (rfl : 0 + 1 = 1)).g :=
    epi_δ_up_zero_res (R := R) (φ := S.subtype) M S.subtype_injective
  (mapShortComplex₃_exact (shortExact_upSES_res M S.subtype) (rfl : 0 + 1 = 1)).g_desc _ _

theorem cores₁_naturality  (X Y : Rep R G) (f : X ⟶ Y) :
    (res S.subtype ⋙ functor R (↥S) 1).map f ≫ cores₁_obj Y =
    cores₁_obj X ≫ (functor R G 1).map f := by
  haveI : Epi (δ (shortExact_upSES_res X S.subtype) 0 1 rfl) :=
    epi_δ_up_zero_res (R := R) (φ := S.subtype) X S.subtype_injective
  symm
  refine CategoryTheory.cubeLemma
    (H0 (up.obj X ↓ S.subtype)) (H1 (X ↓ S.subtype)) (H0 (up.obj X)) (H1 X)
    (H0 (up.obj Y ↓ S.subtype)) (H1 (Y ↓ S.subtype)) (H0 (up.obj Y)) (H1 Y)
    -- four ?_ are the maps in the conclusion of the lemma
    (δ (shortExact_upSES_res X S.subtype) 0 1 rfl) (δ (shortExact_upSES X) 0 1 rfl)
    (δ (shortExact_upSES_res Y S.subtype) 0 1 rfl) (δ (shortExact_upSES Y) 0 1 rfl)
    (cores₀.app (up.obj X)) _ (cores₀.app (up.obj Y)) _
    (map (.id S) ((res S.subtype).map (up.map f)) 0) _
    (map (.id G) (up.map f) 0) _
    ?_ ?_ ?_ ?_ (by exact (cores₀ (S := S)|>.naturality (X := up.obj X) (up.map f)).symm) this
  all_goals symm
  · exact commSq_cores₁ X
  · exact commSq_cores₁ Y
  · exact δ_naturality (shortExact_upSES_res X S.subtype) (shortExact_upSES_res Y S.subtype)
      ((upShortComplex ⋙ (res (R := R) S.subtype).mapShortComplex).map f) 0 1 rfl
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
  let upsc_top := (upShortComplex.obj M).map (res S.subtype)
  -- the above complex of S-modules is exact
  have htopexact : upsc_top.ShortExact := shortExact_upSES_res M S.subtype
  -- so δ : H^{d+1}(S,up_G M) ≅ H^{d+2}(S,M)...
  let up_δ_top_isIso : IsIso (δ (htopexact) (d + 1) (d + 2) rfl) := by
    -- ...because `coind₁'^G M` has trivial cohomology as S-module
    -- have := M.coind₁'_trivialCohomology
    have : upsc_top.X₂.TrivialCohomology := Rep.TrivialCohomology.res_subtype (coind₁'.obj M)
    refine isIso_δ_of_isZero (htopexact) (d + 1) ?_ ?_
    all_goals simpa only [upSES_X₂] using isZero_of_trivialCohomology
  let ih := cores_obj (up.obj M) (d + 1)
  (asIso (δ (htopexact) (d + 1) (d + 2) rfl)).inv ≫ ih ≫ (up_δ_bottom_Iso).hom.app M

theorem cores_succ_naturality (n : ℕ) (X Y : Rep R G) (f : X ⟶ Y) :
    (res S.subtype ⋙ functor R (↥S) (n + 1)).map f ≫ cores_obj Y (n + 1) =
    cores_obj X (n + 1) ≫ (functor R G (n + 1)).map f := by
  revert X Y f
  induction n with
  | zero => exact fun _ _ _ ↦ cores₁_naturality ..
  | succ n ih =>
    intro X Y f
    have := δ_naturality (shortExact_upSES_res X S.subtype) (shortExact_upSES_res Y S.subtype)
      ((upShortComplex ⋙ (res (R := R) S.subtype).mapShortComplex).map f) (n + 1) (n + 2) rfl
    simp only [Functor.comp_obj, functor_obj, Functor.comp_map, functor_map, cores_obj,
      ShortComplex.map_X₃, ShortComplex.map_X₁, asIso_inv, up_obj, Functor.id_obj, coind₁'_obj,
      δUpNatIso, δUpIso, NatIso.ofComponents_hom_app, asIso_hom, Category.assoc, IsIso.eq_inv_comp]
    rw [← Category.assoc]
    simp only [ShortComplex.map_X₃, upSES_X₃, up_obj, Functor.id_obj, coind₁'_obj,
      ShortComplex.map_X₁, upSES_X₁, Functor.comp_map, upShortComplex_obj,
      Functor.mapShortComplex_map_τ₁, upShortComplex_map_τ₁, Functor.mapShortComplex_map_τ₃,
      upShortComplex_map_τ₃, up_map] at this
    rw [this, Category.assoc, ← Category.assoc (δ _ _ _ _), IsIso.hom_inv_id, Category.id_comp,
      δ_naturality (shortExact_upSES X) (shortExact_upSES Y) ⟨f, coind₁'.map f, up.map f, rfl,
      by aesop_cat⟩ (n + 1) (n + 2) rfl, ← Category.assoc, ← Category.assoc]
    exact congr((· ≫ δ (shortExact_upSES _) _ _ _) $(ih (up.obj X) (up.obj Y) (up.map f)))

variable (R) (S) in
/-- Corestriction as a natural transformation. -/
def coresNatTrans (n : ℕ) : Rep.res S.subtype ⋙ functor R S n ⟶ functor R G n where
  app M := (groupCohomology.cores_obj M n)
  naturality X Y f := match n with
    | 0 => cores₀.naturality f
    | n + 1 => cores_succ_naturality n X Y f

lemma map_H0Iso_hom_f_apply'.{u} {k G H : Type u} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    (f : G →* H) (φ : A ↓ f ⟶ B) (x : groupCohomology A 0) :
    (H0Iso B).hom.hom ((map f φ 0).hom x) =
    φ.hom.hom ((H0Iso A).hom.hom x : A) :=
  map_H0Iso_hom_f_apply ..

-- `simp` does a lot of work here, and it was quite some effort getting
-- it to do so, so I hope this proof never breaks...
lemma cores_res₀ : rest (R := R) (S.subtype) 0 ≫ cores₀ = S.index • (.id _) := by
  ext M v
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback (H0Iso M).hom)
  ext
  simp [rest, Subgroup.index, groupCohomology.map_H0Iso_hom_f_apply' S.subtype,
    (M.ρ.mem_invariants ((H0Iso M).hom.hom v)).1 (Subtype.prop _)]

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
    δ (shortExact_upSES M) n (n + 1) rfl ≫ (rest S.subtype (n + 1) ≫ coresNatTrans R S (n + 1)).app M := by
  rw [NatTrans.comp_app, NatTrans.comp_app]
  match n with
  | 0 =>
    exact comp_commSq _ _ _ _ _ _ _ (δ (shortExact_upSES_res M S.subtype) 0 1 rfl)
      (rest_δ_naturality (shortExact_upSES M) S.subtype 0 1 rfl |>.symm) (commSq_cores₁ ..|>.symm)
  | n + 1 =>
    refine comp_commSq _ _ _ _ _ _ _ (δ (shortExact_upSES_res M S.subtype) (n + 1) (n + 2) rfl)
      (rest_δ_naturality (shortExact_upSES M) S.subtype (n + 1) (n + 2) rfl).symm ?_
    simp [-up_obj, coresNatTrans, cores_obj, δUpNatIso, δUpIso]

lemma cores_res (n : ℕ) :
    (rest (R := R) (S.subtype) n ≫ coresNatTrans R S n : functor R G n ⟶ functor R G n) =
      S.index • (.id _) := by
  induction n with
  | zero => exact cores_res₀
  | succ n ih =>
    ext M : 2
    haveI : Epi (δ (shortExact_upSES M) n (n + 1) rfl) :=
    match n with
    | 0 => δ_up_zero_epi ..
    | m + 1 => δ_up_isIso M m|>.epi_of_iso _
    rw [← cancel_epi (δ (shortExact_upSES M) n (n + 1) rfl),  ← commSqₙ n M, ih]
    simp

/-- Any element of H^n-hat (n ∈ ℤ) is `|G|`-torsion. -/
lemma torsion_of_finite_of_neZero {n : ℕ} [NeZero n] (M : Rep R G)
    (x : groupCohomology M n) : Nat.card G • x = 0 := by
  if hG : Infinite G then simp else
  simp only [not_infinite_iff_finite] at hG
  have := by simpa using (LinearMap.ext_iff.1 <| ModuleCat.hom_ext_iff.1
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
    ZeroMemClass.coe_zero, smul_zero, add_zero, map_smul, Module.End.natCast_apply,
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
  haveI : NeZero n := ⟨ne_of_gt hn⟩
  simpa [Functor.comp_obj, functor_obj, rest_app, ne_eq] using by_contra fun hx2 ↦ hx' <|
    @Subtype.ext_iff _ (p := fun x ↦ x ∈ Submodule.torsionBy R (groupCohomology M n) (Nat.card P))
    ⟨x, pTorsion_eq_sylowTorsion M p P x|>.1 hx⟩ 0|>.1 <| groupCohomology.injects_to_sylowCoh M p P
    (by simp [not_not.1 hx2])
