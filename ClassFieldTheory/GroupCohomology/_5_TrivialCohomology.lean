import Mathlib
import ClassFieldTheory.GroupCohomology._1_Basic
import ClassFieldTheory.GroupCohomology._2_restriction
import ClassFieldTheory.GroupCohomology._4_TateCohomology_def

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
  isZero ⦃H : Type⦄ [Group H] [DecidableEq H] (φ : H →* G) (inj : Function.Injective φ) {n : ℕ} :
    IsZero (groupCohomology (M ↓ φ) (n + 1))

lemma TrivialCohomology.of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialCohomology] :
    M.TrivialCohomology := by
  constructor
  intro H _ _ φ inj n
  have : (functor R H n.succ).obj (M ↓ φ) ≅ (functor R H n.succ).obj (N ↓ φ)
  · apply (functor _ _ n.succ).mapIso
    exact (res φ).mapIso f
  exact (isZero _ inj).of_iso this

lemma isZero_of_trivialCohomology [DecidableEq G] {M : Rep R G} [M.TrivialCohomology] {n : ℕ} :
    IsZero (groupCohomology M (n + 1)) :=
  TrivialCohomology.isZero (.id G) Function.injective_id

class TrivialHomology (M : Rep R G) : Prop where
  isZero ⦃H : Type⦄ [Group H] [DecidableEq H] (φ : H →* G) (inj : Function.Injective φ) {n : ℕ} :
    IsZero (groupHomology (M ↓ φ : Rep R H) (n + 1))

lemma TrivialHomology.of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialHomology] :
    M.TrivialHomology := by
  constructor
  intro S _ _ φ inj n
  have : (groupHomology.functor R S n.succ).obj (M ↓ φ) ≅
      (groupHomology.functor R S n.succ).obj (N ↓ φ)
  · apply (groupHomology.functor R S n.succ).mapIso
    exact (res φ).mapIso f
  exact (isZero _ inj).of_iso this

lemma isZero_of_trivialHomology [DecidableEq G] {M : Rep R G} [M.TrivialHomology] {n : ℕ} :
    IsZero (groupHomology M (n + 1)) :=
  TrivialHomology.isZero (φ := .id G) Function.injective_id

class TrivialTateCohomology [Finite G] (M : Rep R G) : Prop where
  isZero ⦃H : Type⦄ [Group H] [DecidableEq H] (φ : H →* G) (inj : Function.Injective φ) {n : ℤ} :
    have := Finite.of_injective φ inj
    IsZero ((TateCohomology n).obj (M ↓ φ : Rep R H))

lemma TrivialTateCohomology.of_iso [Finite G] {M N : Rep R G} (f : M ≅ N)
    [N.TrivialTateCohomology] :
    M.TrivialTateCohomology := by
  constructor
  intro S _ _ φ hφ n
  have _ : Finite S := Finite.of_injective φ hφ
  have : (TateCohomology n).obj (M ↓ φ) ≅ (TateCohomology n).obj (N ↓ φ)
  · apply (TateCohomology n).mapIso
    exact (res φ).mapIso f
  exact (TrivialTateCohomology.isZero _ hφ).of_iso this

lemma isZero_of_trivialTateCohomology [Finite G] [DecidableEq G] {M : Rep R G}
    [M.TrivialTateCohomology] {n : ℕ} : IsZero ((TateCohomology n).obj M) :=
  TrivialTateCohomology.isZero (.id G) Function.injective_id

instance TrivialTateCohomology.to_trivialCohomology [Finite G] {M : Rep R G}
    [M.TrivialTateCohomology] : M.TrivialCohomology where
  isZero H _ _ φ hφ n := by
    classical
    have : Finite H := .of_injective _ hφ
    exact (TrivialTateCohomology.isZero _ hφ).of_iso
      (TateCohomology.isoGroupCohomology n (M ↓ φ)).symm

instance TrivialTateCohomology.to_trivialHomology [Finite G] {M : Rep R G}
    [M.TrivialTateCohomology] : M.TrivialHomology where
  isZero H _ _ φ hφ n := by
    classical
    have : Finite H := .of_injective _ hφ
    exact (TrivialTateCohomology.isZero _ hφ).of_iso
      (TateCohomology.isoGroupHomology n (M ↓ φ)).symm

end Rep
