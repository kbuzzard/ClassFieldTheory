/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Aaron Liu
-/
import Mathlib
import ClassFieldTheory.GroupCohomology.«08_DimensionShift»

/-

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
variable {G : Type} [Group G] {S : Subgroup G} [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace groupCohomology

lemma cores_aux₁ {V : Type} [AddCommMonoid V] [Module R V] (ρ : Representation R G V)
    (v : V) (hv : ∀ s ∈ S, (ρ s) v = v)
    (g₁ g₂ : G) (h : (QuotientGroup.mk g₁ : G ⧸ S) = QuotientGroup.mk g₂) :
    ρ g₁ v = ρ g₂ v := by
  sorry

lemma cores_aux₂ {X : Type} [Fintype X]
    (s₁ : X → G) (hs₁ : Function.Bijective (fun x ↦ QuotientGroup.mk (s₁ x) : X → G ⧸ S))
    (s₂ : X → G) (hs₂ : Function.Bijective (fun x ↦ QuotientGroup.mk (s₁ x) : X → G ⧸ S))
    {V : Type} [AddCommMonoid V] [Module R V] (ρ : Representation R G V)
    (v : V) (hv : ∀ s ∈ S, (ρ s) v = v) :
    ∑ x : X, ρ (s₁ x) v = ∑ x : X, ρ (s₂ x) v := by
  sorry

/-- The H^0 corestriction map for S ⊆ G a finite index subgroup, as an `R`-linear
map on invariants. -/
def _root_.Representation.cores₀_obj {V : Type} [AddCommMonoid V] [Module R V] (ρ : Representation R G V) :
    Representation.invariants (MonoidHom.comp ρ S.subtype) →ₗ[R] ρ.invariants where
  toFun x := ⟨∑ i : G ⧸ S, ρ i.out x.1, sorry⟩
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' := by simp [Finset.smul_sum]


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
    have comm := congr(∑ i : G ⧸ S, ModuleCat.Hom.hom $(f.comm i.out) x.val)
    simpa [Representation.cores₀_obj] using comm.symm

/-- The morphism `H¹(S, M↓S) ⟶ H¹(G, M)`. -/
def cores₁_obj [DecidableEq G] (M : Rep R G) :
    -- defining H¹(S, M↓S) ⟶ H¹(G, M) by a diagram chase
    (functor R S 1).obj (M ↓ S.subtype) ⟶ (functor R G 1).obj M := by
  -- Recall we have 0 ⟶ M ⟶ coind₁'^G M ⟶ up_G M ⟶ 0 a short exact sequence
  -- of `G`-modules which restricts to a short exact sequence of `S`-modules.
  -- First I claim δ : H⁰(S,(up_G M)↓S) ⟶ H¹(S,M↓S) is surjective
  have : Epi (mapShortComplex₃ (up_shortExact_res M S.subtype) (rfl : 0 + 1 = 1)).g :=
    -- because `coind₁'^G M` has trivial cohomology
    up_δ_zero_epi_res (R := R) (φ := S.subtype) M S.subtype_injective
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
    let foo := ((upShortComplex.obj M).map (res S.subtype))
    let bar := cokernel.π (coind₁'_ι.app M)
    let moo := (res S.subtype ⋙ functor R (↥S) 0).map bar
    -- cores₀ : res S.subtype ⋙ functor R (↥S) 0 ⟶ functor R G 0
    have baz := cores₀.naturality (F := (res S.subtype ⋙ functor R (↥S) 0)) bar
    change ((res S.subtype ⋙ functor R (↥S) 0).map bar ≫ (cores₀.app (up.obj M))) ≫ _ = 0
    change _ ≫ (cores₀.app (up.obj M)) = _ ≫ _ at baz
    rw [baz, Category.assoc]
    convert comp_zero -- cancel first functor
    exact (mapShortComplex₃ (up_shortExact M) (rfl : 0 + 1 = 1)).zero

def cores_obj [DecidableEq G] : (M : Rep R G) → (n : ℕ) → (functor R S n).obj (M ↓ S.subtype) ⟶ (functor R G n).obj M
| M, 0 => cores₀.app M
| M, 1 => cores₁_obj M
| M, (d + 2) =>
  -- δ : H^{d+1}(G,up -) ≅ H^{d+2}(G,-)
  let up_δ_bottom_Iso := Rep.dimensionShift.up_δiso_natTrans (R := R) (G := G) d
  -- `M ⟶ coind₁'^G M ⟶ up_G M` as a complex of S-modules
  let upsc_top := (upShortComplex.obj M).map (res S.subtype)
  -- the above complex of S-modules is exact
  have htopexact : upsc_top.ShortExact := up_shortExact_res M S.subtype
  -- so δ : H^{d+1}(S,up_G M) ≅ H^{d+2}(S,M)...
  let up_δ_top_isIso : IsIso (δ (htopexact) (d + 1) (d + 2) rfl) := by
    -- ...because `coind₁'^G M` has trivial
    -- cohomology as S-module (hopefully this is somewhere in the repo)
    have : upsc_top.X₂.TrivialCohomology := by
      change (of M.ρ.coind₁' ↓ S.subtype).TrivialCohomology
      -- ⊢ (of M.ρ.coind₁' ↓ S.subtype).TrivialCohomology
      sorry -- missing proof
    refine isIso_δ_of_isZero (htopexact) (d + 1) ?_ ?_
    all_goals simpa only [upShortComplex_obj_X₂] using isZero_of_trivialCohomology
  let ih := cores_obj (up.obj M) (d + 1)
  (asIso (δ (htopexact) (d + 1) (d + 2) rfl)).inv ≫ ih ≫ (up_δ_bottom_Iso).hom.app M
