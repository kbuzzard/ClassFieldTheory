import ClassFieldTheory.GroupCohomology.«04_TateCohomology_def»
import ClassFieldTheory.Mathlib.RepresentationTheory.Rep

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
  isZero (H : Subgroup G) {n : ℕ} : IsZero (groupCohomology (M ↓ H.subtype) (n + 1))

theorem isZero_of_injective (M : Rep R G) {H : Type} [Group H] (f : H →* G) (n : ℕ) (hn : n ≠ 0)
    (hf : Function.Injective f) [M.TrivialCohomology] : IsZero (groupCohomology (M ↓ f) n) := by
  cases n with
  | zero => tauto
  | succ n =>
    exact .of_iso (TrivialCohomology.isZero f.range) (resSubtypeRangeIso M f (n + 1) hf).symm

lemma TrivialCohomology.of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialCohomology] :
    M.TrivialCohomology where
  isZero H n := (isZero H).of_iso <| (functor _ _ n.succ).mapIso <| (res H.subtype).mapIso f

protected lemma TrivialCohomology.res (M : Rep R G) {H : Subgroup G} [M.TrivialCohomology] :
    (M ↓ H.subtype).TrivialCohomology where
  isZero S n := isZero_of_injective M (H.subtype.comp S.subtype) (n + 1) (by omega)
      (H.subtype_injective.comp S.subtype_injective)

lemma isZero_of_trivialCohomology {M : Rep R G} [M.TrivialCohomology] {n : ℕ} :
    IsZero (groupCohomology M (n + 1)) :=
  isZero_of_injective M (.id G) n.succ (by omega) Function.injective_id

lemma trivialCohomology_iff_res {M : Rep R G} :
    M.TrivialCohomology ↔
      ∀ {H : Type} [Group H] (f : H →* G), Function.Injective f → (M ↓ f).TrivialCohomology where
  mp _ _ _ f inj := ⟨fun S n ↦ isZero_of_injective M (f.comp S.subtype) (n + 1) (by omega)
    (inj.comp S.subtype_injective)⟩
  mpr h := h (f := .id G) Function.injective_id

class TrivialHomology (M : Rep R G) : Prop where
  isZero (H : Subgroup G) {n : ℕ} : IsZero (groupHomology (M ↓ H.subtype) (n + 1))

lemma TrivialHomology.of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialHomology] :
    M.TrivialHomology := by
  constructor
  intro H n
  exact (isZero _).of_iso <| (groupHomology.functor R H n.succ).mapIso <| (res H.subtype).mapIso f

lemma TrivialHomology.of_injective {M : Rep R G} {H : Type} [Group H] (f : H →* G) (n : ℕ)
    (hn : n ≠ 0) (hf : Function.Injective f) [M.TrivialHomology] :
    IsZero (groupHomology (M ↓ f) n) := by
  cases n with
  | zero => tauto
  | succ n =>
    exact .of_iso (TrivialHomology.isZero f.range)
      (groupHomology.resSubtypeRangeIso M f (n + 1) hf).symm

protected lemma TrivialHomology.res (M : Rep R G) {H : Type} [Group H] {f : H →* G}
    (hf : Function.Injective f) [M.TrivialHomology] : (M ↓ f).TrivialHomology where
  isZero H n :=
    TrivialHomology.of_injective (f.comp H.subtype) (n + 1) (by omega) <|
      show Function.Injective (f ∘ _) from Function.Injective.comp hf H.subtype_injective

lemma isZero_of_trivialHomology {M : Rep R G} [M.TrivialHomology] {n : ℕ} :
    IsZero (groupHomology M (n + 1)) :=
  TrivialHomology.of_injective (.id G) n.succ (by omega) Function.injective_id

lemma trivialHomology_iff_res {M : Rep R G} :
    M.TrivialHomology ↔
      ∀ {H : Type} [Group H] (f : H →* G), Function.Injective f → (M ↓ f).TrivialHomology
    where
  mp _ _ _ _ inj := .res M inj
  mpr h := h (f := .id G) Function.injective_id

class TrivialTateCohomology [Finite G] (M : Rep R G) : Prop where
  isZero (H : Subgroup G) {n : ℤ} :
    IsZero ((tateCohomology n).obj (M ↓ H.subtype : Rep R H))

lemma TrivialTateCohomology.of_iso [Finite G] {M N : Rep R G} (f : M ≅ N)
    [N.TrivialTateCohomology] :
    M.TrivialTateCohomology := ⟨fun H ↦ (TrivialTateCohomology.isZero _).of_iso <|
    (tateCohomology _).mapIso <| (res H.subtype).mapIso f⟩

attribute [local instance] Fintype.ofFinite in
lemma TrivialTateCohomology.of_injective [Fintype G] {M : Rep R G} {H : Type} [Fintype H]
    [Group H] (f : H →* G) (n : ℤ) (hf : Function.Injective f)
    [M.TrivialTateCohomology] : IsZero ((tateCohomology n).obj (M ↓ f)) :=
  .of_iso (isZero (M := M) f.range (n := n)) <| TateCohomology.res_iso
    (MonoidHom.ofInjective hf) (Iso.refl _) (by aesop) _

lemma isZero_of_trivialTateCohomology [Fintype G] {M : Rep R G}
    [M.TrivialTateCohomology] {n : ℕ} : IsZero ((tateCohomology n).obj M) :=
  TrivialTateCohomology.of_injective (.id G) n Function.injective_id

instance TrivialTateCohomology.to_trivialCohomology [Fintype G] {M : Rep R G}
    [M.TrivialTateCohomology] : M.TrivialCohomology where
  isZero H n := (TrivialTateCohomology.isZero (M := M) H (n := Nat.cast n + 1)).of_iso <|
    TateCohomology.isoGroupCohomology n|>.app (M ↓ H.subtype)|>.symm

instance TrivialTateCohomology.to_trivialHomology [Fintype G] {M : Rep R G}
    [M.TrivialTateCohomology] : M.TrivialHomology where
  isZero H n := (TrivialTateCohomology.isZero H (n := - n - 2)).of_iso <|
    (TateCohomology.isoGroupHomology n|>.app (M ↓ H.subtype)).symm

lemma TrivialTateCohomology.of_cases [Fintype G] {M : Rep R G}
    [M.TrivialCohomology] [M.TrivialHomology]
    (h : ∀ (H : Subgroup G),
      IsZero ((tateCohomology 0).obj (M ↓ H.subtype : Rep R H)) ∧
        IsZero ((tateCohomology (-1)).obj (M ↓ H.subtype : Rep R H))) :
    TrivialTateCohomology M where
  isZero H n := by
    match n with
    | .ofNat (n + 1) =>
      letI := TrivialCohomology.res M (H := H)
      exact isZero_of_trivialCohomology.of_iso <|
        (TateCohomology.isoGroupCohomology n).app (M ↓ H.subtype)
    | .negSucc (n + 1) =>
      letI := TrivialHomology.res M (H := H) H.subtype_injective
      rw [show Int.negSucc (n + 1) = -n - 2 by grind]
      exact isZero_of_trivialHomology.of_iso <|
        (TateCohomology.isoGroupHomology n).app (M ↓ H.subtype)
    | 0 =>
      aesop
    | .negSucc 0 =>
      aesop

instance [Subsingleton G] {M : Rep R G} : M.TrivialCohomology where
  isZero H n := by
    apply isZero_groupCohomology_succ_of_subsingleton

instance [Subsingleton G] {M : Rep R G} : M.TrivialHomology where
  isZero H n := by
    apply isZero_groupHomology_succ_of_subsingleton

instance [Subsingleton G] {M : Rep R G} : M.TrivialTateCohomology := by
  haveI := Fintype.ofFinite G
  refine .of_cases ?_
  intro H
  have : (M ↓ H.subtype).ρ.IsTrivial := by
    constructor; intro g; rw [Subsingleton.eq_one g, map_one]; rfl
  constructor
  · refine IsZero.of_iso ?_ (TateCohomology.zeroIsoOfIsTrivial _)
    rw [Nat.card_unique, Nat.cast_one, LinearMap.range_eq_top_of_cancel (by exact fun _ _ a ↦ a)]
    exact ModuleCat.isZero_of_subsingleton _
  refine IsZero.of_iso ?_ (TateCohomology.negOneIsoOfIsTrivial _)
  rw [Nat.card_unique, Nat.cast_one, LinearMap.ker_eq_bot_of_cancel (by exact fun _ _ a ↦ a)]
  exact ModuleCat.isZero_of_subsingleton _

noncomputable def _root_.TrivialTateCohomology.zeroIso_ofTrivial
    [Fintype G] (M : Rep R G) [M.IsTrivial] :
    (tateCohomology 0).obj M ≅ ModuleCat.of R (M ⧸ LinearMap.range (Nat.card G : M →ₗ[R] M)) :=
  groupCohomology.TateCohomology.zeroIso M|>.trans <| LinearEquiv.toModuleIso <|
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (by ext; simp) ≪≫ₗ Submodule.topEquiv) <| by
    rw [Representation.norm_ofIsTrivial]
    ext m
    simp [Submodule.submoduleOf]

end Rep
