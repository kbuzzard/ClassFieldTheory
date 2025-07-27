/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Aaron Liu
-/
import Mathlib
import ClassFieldTheory.GroupCohomology._8_DimensionShift

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

Unsorry the data
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
def cores₀_obj {V : Type} [AddCommMonoid V] [Module R V] (ρ : Representation R G V) :
    Representation.invariants (MonoidHom.comp ρ S.subtype) →ₗ[R] ρ.invariants where
  toFun x := ⟨∑ i : G ⧸ S, ρ i.out x.1, sorry⟩
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' := by simp [Finset.smul_sum]


/-- The corestriction functor on H^0 for S ⊆ G a finite index subgroup, as a
functor `H^0(S,-) → H^0(G,-)`. -/
def cores₀ : Rep.res S.subtype ⋙ functor R S 0 ⟶ functor R G 0 where
  app M := (H0Iso (M ↓ S.subtype)).hom ≫ (ModuleCat.ofHom (cores₀_obj M.ρ)) ≫ (H0Iso M).inv
  naturality := by
    intro X Y f
    simp_rw [← Category.assoc]
    rw [(H0Iso Y).comp_inv_eq]
    simp_rw [Category.assoc]
    rw [functor_map, map_id_comp_H0Iso_hom, (H0Iso X).inv_hom_id_assoc, Functor.comp_map,
      functor_map, map_id_comp_H0Iso_hom_assoc, (H0Iso (X ↓ S.subtype)).cancel_iso_hom_left]
    ext x
    have comm := congr(∑ i : G ⧸ S, ModuleCat.Hom.hom $(f.comm i.out) x.val)
    simpa [cores₀_obj] using comm.symm

def cores_obj [DecidableEq G] : (M : Rep R G) → (n : ℕ) → (functor R S n).obj (M ↓ S.subtype) ⟶ (functor R G n).obj M
| M, 0 => cores₀.app M
| M, 1 => by
    -- WIP
    let foo : (functor R S 0).obj (up.obj M ↓ S.subtype) ⟶ (functor R G 0).obj (up.obj M) := cores₀.app (up.obj M)
    let bar : (functor R G 0).obj (up.obj M) ⟶ (functor R G 1).obj M := δ (up_shortExact M) 0 1 rfl
    let bar' : (functor R S 0).obj (up.obj (M ↓ S.subtype)) ⟶ (functor R S 1).obj (M ↓ S.subtype) := δ (up_shortExact (M ↓ S.subtype)) 0 1 rfl
    let f := foo ≫ bar
    have baz := up_δ_zero_epi_res (R := R) (φ := S.subtype) M S.subtype_injective
    let upsc_bottom := upShortComplex.obj M
    let upsc_top := upsc_bottom.map (res S.subtype)
    have hbottomexact : upsc_bottom.ShortExact := up_shortExact M
    have htopexact : (upsc_bottom.map (res S.subtype)).ShortExact :=
      up_shortExact_res M S.subtype
    -- this is H^0(S,M|S)->H^0(S,(up_G M)|S)->H^1(S,M|S)
    let sc1 := mapShortComplex₃ htopexact (rfl : 0 + 1 = 1)
    -- this is H^0(G,M)->H^0(G,(up_G M))->H^1(G,M)
    let sc2 := mapShortComplex₃ hbottomexact (rfl : 0 + 1 = 1)
    -- this is the claim that `H^0(S,(up_G M)|S)->H^1(S,M|S)` is surjective
    have hepi : Epi (mapShortComplex₃ htopexact (rfl : 0 + 1 = 1)).g := baz
    -- the idea is to get a map `H^1(S,M|S) → H^1(G,M)` from a diagram chase.
    -- We have the maps on the H^0 terms and that the square commutes.
    sorry -- data -- see kmb question on Fri morning
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
      sorry
    refine isIso_δ_of_isZero (htopexact) (d + 1) ?_ ?_
    all_goals simpa only [upShortComplex_obj_X₂] using isZero_of_trivialCohomology
  let ih := cores_obj (up.obj M) (d + 1)
  (asIso (δ (htopexact) (d + 1) (d + 2) rfl)).inv ≫ ih ≫ (up_δ_bottom_Iso).hom.app M
