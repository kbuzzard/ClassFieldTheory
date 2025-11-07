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
  simp [-Action.res_obj_V, -res_obj_ρ, rest, Subgroup.index,
    groupCohomology.map_H0Iso_hom_f_apply' S.subtype,
    (M.ρ.mem_invariants ((H0Iso M).hom.hom v)).1]

theorem _root_.CategoryTheory.comp_commSq (C' : Type*) [Category C'] {A B C D E F : C'}
    (f₁ : A ⟶ B) (f₂ : B ⟶ C) (g₁ : A ⟶ D) (g₂ : C ⟶ F) (h₁ : D ⟶ E) (h₂ : E ⟶ F) (f : B ⟶ E)
    (comm1 : f₁ ≫ f = g₁ ≫ h₁) (comm2 : f₂ ≫ g₂ = f ≫ h₂) :
    (f₁ ≫ f₂) ≫ g₂ = g₁ ≫ (h₁ ≫ h₂) := by
  rw [← Category.assoc, ← comm1, Category.assoc, comm2, Category.assoc]

/-!
            rest                       cores
Hⁿ(G, up M) ---> Hⁿ(S, upM ↓ S.subtype) ---> Hⁿ(G, up M)
    |                                         |
    | δ                                       | δ
    v       rest                       cores  v
Hⁿ⁺¹(G, M)  ---> Hⁿ⁺¹(S, M ↓ S.subtype) ---> Hⁿ⁺¹(G, M)

-/
lemma commSqₙ (n : ℕ) [DecidableEq G] (M : Rep R G) :
    (rest S.subtype n ≫ coresNatTrans R S n).app (up.obj M) ≫ δ (up_shortExact M) n (n + 1) rfl =
    δ (up_shortExact M) n (n + 1) rfl ≫ (rest S.subtype (n + 1) ≫ coresNatTrans R S (n + 1)).app M := by
  rw [NatTrans.comp_app, NatTrans.comp_app]
  match n with
  | 0 =>
    exact comp_commSq _ _ _ _ _ _ _ (δ (up_shortExact_res M S.subtype) 0 1 rfl)
      (rest_δ_naturality (up_shortExact M) S.subtype 0 1 rfl |>.symm) (commSq_cores₁ ..|>.symm)
  | n + 1 =>
    refine comp_commSq _ _ _ _ _ _ _ (δ (up_shortExact_res M S.subtype) (n + 1) (n + 2) rfl)
      (rest_δ_naturality (up_shortExact M) S.subtype (n + 1) (n + 2) rfl).symm ?_
    simp [-up_obj, coresNatTrans, cores_obj]
    rfl

lemma cores_res (n : ℕ) [DecidableEq G] :
    (rest (R := R) (S.subtype) n ≫ coresNatTrans R S n : functor R G n ⟶ functor R G n) =
      S.index • (.id _) := by
  induction n with
  | zero => exact cores_res₀
  | succ n ih =>
    ext M : 2
    haveI : Epi (δ (up_shortExact M) n (n + 1) rfl) :=
    match n with
    | 0 => δ_up_zero_epi ..
    | m + 1 => δ_up_isIso M m|>.epi_of_iso _
    rw [← cancel_epi (δ (up_shortExact M) n (n + 1) rfl),  ← commSqₙ n M, ih]
    simp

/-- Any element of H^n-hat (n ∈ ℤ) is `|G|`-torsion. -/
lemma torsion_of_finite_of_neZero {n : ℕ} [NeZero n] [Fintype G] (M : Rep R G)
    (x : (functor R G n).obj M) : Nat.card G • x = 0 := sorry

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
lemma groupCohomology_Sylow {n : ℕ} (hn : 0 < n) [Finite G] (M : Rep R G)
    (x : groupCohomology M n) (p : ℕ) (P : Sylow p G) (hx : ∃ d, (p ^ d) • x = 0)
    (hx' : x ≠ 0) : (groupCohomology.rest (P.toSubgroup.subtype) n).app M x ≠ 0 := sorry

-- Want an analogous statement for Tate cohomology but I can't find restriction
-- in Tate cohomology
