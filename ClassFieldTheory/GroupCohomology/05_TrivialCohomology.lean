import Mathlib
import ClassFieldTheory.GroupCohomology._01_Basic
import ClassFieldTheory.GroupCohomology._02_restriction
import ClassFieldTheory.GroupCohomology._04_TateCohomology_def
import ClassFieldTheory.Tactic.Dualize

/-!
# Trivial (Tate) (co)homology

An object `M : Rep R G` is has *trivial cohomology* if
`Hⁿ(S, M)=0` for all `n > 0` and all subgroup `S` of `G`.

`M` has *trivial homology* if for all subgroups `S` and all `n > 0`
we have `Hₙ(S, M) ≅ 0`.

`M` has *trivial Tate cohomology* if for all subgroups `S` and all `n : ℤ`
we have `Hⁿ_{Tate}(S, M) ≅ 0`.

We define these three classes of representation, and prove that they are preserved
by isomorphisms.
-/

open
  CategoryTheory
  CategoryTheory.Limits
  groupCohomology

namespace Rep
variable {R G : Type} [CommRing R] [Group G]

/--
A representation `M : Rep R G` has trivial cohomology if the cohomology groups `Hⁿ(H, M)`
are zero for every subgroup `H` of `G` and every `n > 0`.
-/
class TrivialCohomology (M : Rep R G) : Prop where
  isZero ⦃H : Type⦄ [Group H] (φ : H →* G) (inj : Function.Injective φ) {n : ℕ} :
    IsZero (groupCohomology (M ↓ φ) (n + 1))

lemma TrivialCohomology.of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialCohomology] :
    M.TrivialCohomology := by
  constructor
  intro H _ φ inj n
  have : (functor R H n.succ).obj (M ↓ φ) ≅ (functor R H n.succ).obj (N ↓ φ)
  · apply (functor _ _ n.succ).mapIso
    exact (res φ).mapIso f
  exact (isZero _ inj).of_iso this

protected lemma TrivialCohomology.res (M : Rep R G ){H : Type} [Group H] {f : H →* G}
    (hf : Function.Injective f) [M.TrivialCohomology] : (M ↓ f).TrivialCohomology where
  isZero _ _ φ hφ _ := isZero (f.comp φ) (hf.comp hφ)

lemma isZero_of_trivialCohomology {M : Rep R G} [M.TrivialCohomology] {n : ℕ} :
    IsZero (groupCohomology M (n + 1)) :=
  TrivialCohomology.isZero (.id G) Function.injective_id

lemma trivialCohomology_iff_res {M : Rep R G} :
    M.TrivialCohomology ↔
      ∀ {H : Type} [Group H] (f : H →* G), Function.Injective f → (M ↓ f).TrivialCohomology where
  mp _ _ _ _ inj := TrivialCohomology.res M inj
  mpr h := h (f := .id G) Function.injective_id

class TrivialHomology (M : Rep R G) : Prop where
  isZero ⦃H : Type⦄ [Group H] (φ : H →* G) (inj : Function.Injective φ) {n : ℕ} :
    IsZero (groupHomology (M ↓ φ : Rep R H) (n + 1))

lemma TrivialHomology.of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialHomology] :
    M.TrivialHomology := by
  constructor
  intro S _ φ inj n
  have : (groupHomology.functor R S n.succ).obj (M ↓ φ) ≅
      (groupHomology.functor R S n.succ).obj (N ↓ φ)
  · apply (groupHomology.functor R S n.succ).mapIso
    exact (res φ).mapIso f
  exact (isZero _ inj).of_iso this

protected lemma TrivialHomology.res (M : Rep R G) {H : Type} [Group H] {f : H →* G}
    (hf : Function.Injective f) [M.TrivialHomology] : (M ↓ f).TrivialHomology where
  isZero _ _ φ hφ _ := isZero (f.comp φ) (hf.comp hφ)

lemma isZero_of_trivialHomology [DecidableEq G] {M : Rep R G} [M.TrivialHomology] {n : ℕ} :
    IsZero (groupHomology M (n + 1)) :=
  TrivialHomology.isZero (φ := .id G) Function.injective_id

lemma trivialHomology_iff_res {M : Rep R G} :
    M.TrivialHomology ↔
      ∀ {H : Type} [Group H] (f : H →* G), Function.Injective f → (M ↓ f).TrivialHomology
    where
  mp _ _ _ _ inj := .res M inj
  mpr h := h (f := .id G) Function.injective_id

class TrivialTateCohomology [Finite G] (M : Rep R G) : Prop where
  isZero ⦃H : Type⦄ [Group H] [DecidableEq H] (φ : H →* G) (inj : Function.Injective φ) {n : ℤ} :
    have := Finite.of_injective φ inj
    IsZero ((tateCohomology n).obj (M ↓ φ : Rep R H))

lemma TrivialTateCohomology.of_iso [Finite G] {M N : Rep R G} (f : M ≅ N)
    [N.TrivialTateCohomology] :
    M.TrivialTateCohomology := by
  constructor
  intro S _ _ φ hφ n
  have _ : Finite S := Finite.of_injective φ hφ
  have : (tateCohomology n).obj (M ↓ φ) ≅ (tateCohomology n).obj (N ↓ φ)
  · apply (tateCohomology n).mapIso
    exact (res φ).mapIso f
  exact (TrivialTateCohomology.isZero _ hφ).of_iso this

lemma isZero_of_trivialTateCohomology [Finite G] [DecidableEq G] {M : Rep R G}
    [M.TrivialTateCohomology] {n : ℕ} : IsZero ((tateCohomology n).obj M) :=
  TrivialTateCohomology.isZero (.id G) Function.injective_id

instance TrivialTateCohomology.to_trivialCohomology [Finite G] {M : Rep R G}
    [M.TrivialTateCohomology] : M.TrivialCohomology where
  isZero H _ φ hφ n := by
    classical
    have : Finite H := .of_injective _ hφ
    exact (TrivialTateCohomology.isZero _ hφ).of_iso
      (tateCohomology.isoGroupCohomology n|>.app (M ↓ φ)).symm

instance TrivialTateCohomology.to_trivialHomology [Finite G] {M : Rep R G}
    [M.TrivialTateCohomology] : M.TrivialHomology where
  isZero H _ φ hφ n := by
    classical
    have : Finite H := .of_injective _ hφ
    exact (TrivialTateCohomology.isZero _ hφ).of_iso
      (tateCohomology.isoGroupHomology n|>.app (M ↓ φ)).symm

lemma TrivialTateCohomology.of_cases [Finite G] {M : Rep R G}
    [M.TrivialCohomology] [M.TrivialHomology]
    (h : ∀ {H : Type} [Group H] [DecidableEq H] (φ : H →* G) (inj : Function.Injective φ),
      have := Finite.of_injective φ inj
      IsZero ((tateCohomology 0).obj (M ↓ φ : Rep R H)) ∧
        IsZero ((tateCohomology (-1)).obj (M ↓ φ : Rep R H))) :
    TrivialTateCohomology M where
  isZero _ _ _ φ inj n := by
    have := Finite.of_injective φ inj
    match n with
    | .ofNat (n + 1) =>
      letI := TrivialCohomology.res M inj
      exact (isZero_of_trivialCohomology).of_iso <|
        (tateCohomology.isoGroupCohomology n).app (M ↓ φ)
    | .negSucc (n + 1) =>
      letI := TrivialHomology.res M inj
      rw [show Int.negSucc (n + 1) = -n - 2 by grind]
      exact isZero_of_trivialHomology.of_iso <|
        (tateCohomology.isoGroupHomology n).app (M ↓ φ)
    | 0 =>
      aesop
    | .negSucc 0 =>
      aesop

instance [Subsingleton G] {M : Rep R G} : M.TrivialCohomology where
  isZero H _ _ hf _ := by
    letI : Subsingleton H := Function.Injective.subsingleton hf
    apply isZero_groupCohomology_succ_of_subsingleton

instance [Subsingleton G] {M : Rep R G} : M.TrivialHomology where
  isZero H _ _ hf _ := by
    letI : Subsingleton H := Function.Injective.subsingleton hf
    apply isZero_groupHomology_succ_of_subsingleton

instance [Subsingleton G] {M : Rep R G} : M.TrivialTateCohomology := by
  refine .of_cases ?_
  intro H _ _ φ inj
  have : Subsingleton H := Function.Injective.subsingleton inj
  have : (M ↓ φ).ρ.IsTrivial := {
    out g := by
      rw [Subsingleton.eq_one g, map_one]
      rfl }
  constructor
  · refine IsZero.of_iso ?_ (tateCohomology.zeroIsoOfIsTrivial _)
    rw [Nat.card_unique, Nat.cast_one, LinearMap.range_eq_top_of_cancel (by exact fun _ _ a ↦ a)]
    exact ModuleCat.isZero_of_subsingleton _
  refine IsZero.of_iso ?_ (tateCohomology.negOneIsoOfIsTrivial _)
  rw [Nat.card_unique, Nat.cast_one, LinearMap.ker_eq_bot_of_cancel (by exact fun _ _ a ↦ a)]
  exact ModuleCat.isZero_of_subsingleton _

end Rep
