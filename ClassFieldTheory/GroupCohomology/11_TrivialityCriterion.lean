import Mathlib
import ClassFieldTheory.GroupCohomology.«04_TateCohomology_def»
import ClassFieldTheory.GroupCohomology.«05_TrivialCohomology»
import ClassFieldTheory.GroupCohomology.«08_DimensionShift»
import ClassFieldTheory.GroupCohomology.«10_inflationRestriction»
import ClassFieldTheory.GroupCohomology.«09_CyclicGroup»
import ClassFieldTheory.Mathlib.Algebra.Group.Solvable

/-
Suppose `G` is a finite group, and there are positive integers `r` and `s`
with `r` even and `s` odd, such that `Hʳ(S,M) ≅ Hˢ(S,M) ≅ 0` for all subgroup `S` of `G`.
Then we prove that `M` has trivial cohomology.
This is used in proving that `split σ` has trivial cohomology, where `σ` is a fundamental class
in a finite class formation.

The theorem is proved first for solvable groups, by induction on the subgroup
using inflation-restriction.
The proof in the general case requires the corestriction map `Cor : Hⁿ(H,M) ⟶ Hⁿ(G,M)`.

As a corollary, we show that if `M` has trivial cohomology then `up.obj M` and `down.obj M`
both have trivial cohomology. Using this, we show that if `M` has trivial cohomology then it has
trivial Tate cohomology.
-/

open
  CategoryTheory
  CategoryTheory.Limits
  groupCohomology
  Rep
  dimensionShift

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]

/--
If `H²ⁿ⁺²(H,M)` and `H²ᵐ⁺¹(H,M)` are both zero for every subgroup `H` of `G` then `M` is acyclic.
-/
theorem groupCohomology.trivialCohomology_of_even_of_odd_of_solvable [Fintype G] [IsSolvable G]
    (M : Rep R G) (n m : ℕ)
    (h_even : ∀ (H : Type) [Group H] {φ : H →* G} (_ : Function.Injective φ),
      IsZero (groupCohomology (M ↓ φ) (2 * n + 2)))
    (h_odd : ∀ (H : Type) [Group H] {φ : H →* G} (_ : Function.Injective φ),
      IsZero (groupCohomology (M ↓ φ) (2 * m + 1))) :
    M.TrivialCohomology where
  isZero H := by
    classical
    induction H using solvable_ind with
    | bot =>
      intro n
      exact isZero_groupCohomology_succ_of_subsingleton ..
    | ind K H h12 h1 h2 h3 =>
    have IH : ∀ i, IsZero (groupCohomology (M ↓ H.subtype ↓
        (QuotientGroup.mk' (K.subgroupOf H)).ker.subtype) (i + 1)) := by
      refine fun i ↦ .of_iso (h3 (n := i)) <| groupCohomology.mapIso ((MulEquiv.subgroupCongr <|
        QuotientGroup.ker_mk' _).trans <| Subgroup.subgroupOfEquivOfLe h12)
        (by exact Iso.refl _) (by simp) _
    have : ∀ n, IsIso ((infl (QuotientGroup.mk'_surjective
        (K.subgroupOf H)) (n + 1)).app (M ↓ H.subtype)) := by
      intro n
      apply (config := { allowSynthFailures := true }) isIso_of_mono_of_epi
      · exact inflation_restriction_mono (R := R)
          (QuotientGroup.mk'_surjective (K.subgroupOf H)) n (M := M ↓ H.subtype) (fun i _ ↦ IH i)
      · exact (inflation_restriction_exact (R := R)
          (QuotientGroup.mk'_surjective (K.subgroupOf H)) n (M := M ↓ H.subtype) (fun i _ ↦ IH i)).epi_f
          (IsZero.eq_zero_of_tgt (IH _) _)
    have : ∀ n : ℕ, groupCohomology ((M ↓ H.subtype) ↑
      (QuotientGroup.mk'_surjective (K.subgroupOf H))) (n + 1) ≅
      groupCohomology (M ↓ H.subtype) (n + 1) := fun n ↦ asIso ((infl (QuotientGroup.mk'_surjective
        (K.subgroupOf H)) (n + 1)).app (M ↓ H.subtype))
    specialize h_even H H.subtype_injective
    specialize h_odd H H.subtype_injective
    have zero1 := IsZero.of_iso h_even <| this (2 * n + 1)
    have zero2 := IsZero.of_iso h_odd <| this (2 * m)
    intro k
    exact IsZero.of_iso (Rep.isZero_ofEven_Odd zero1 zero2 k) <| this k |>.symm
  /-
  This is proved by induction on `H`.
  If `H` is the trivial subgroup then the result is true.
  Assume that the result is true for every proper subgroup of `H`, and choose a
  normal subgroup `K` of `H` such that `H ⧸ K` is cyclic. We are therefore assuming
  that the restriction of `M` to `K` is acyclic.

  Since `M` is `K`-acyclic, we have for every `r > 0` an inflation-restriction sequence:

    `0 ⟶ Hʳ(H/K,Mᴷ) ⟶ Hʳ(H,M) ⟶ Hʳ(K,M)`.

  as the last term is zero, we have isomorphisms `Hʳ(H/K,Mᴷ) ≅ Hʳ(H,M)` for all `r > 0`.
  In particular `H²ⁿ⁺²(H/K,Mᴷ)` and `H²ᵐ⁺¹(H/K,Mᴷ)` are both zero.
  By the periodicity of the cohomology of a cyclic group, `Hʳ(H/K,Mᴷ)` is zero for all `r > 0`.
  Therefore `Hʳ(H,M)=0` for all `r > 0`.
  -/

theorem groupCohomology.trivialCohomology_of_even_of_odd [Finite G]
    (M : Rep R G) (n m : ℕ)
    (h_even : ∀ (H : Type) [Group H] {φ : H →* G} (inj : Function.Injective φ) [DecidableEq H],
      IsZero (groupCohomology (M ↓ φ) (2 * n + 2)))
    (h_odd : ∀ (H : Type) [Group H] {φ : H →* G} (inj : Function.Injective φ) [DecidableEq H],
      IsZero (groupCohomology (M ↓ φ) (2 * m + 1))) :
    M.TrivialCohomology := by
  /-
  Let `p` be any prime number and let `S` be a subgroup of `G`.
  The group `Hⁿ(S,M)[p^∞]` is isomorphic to a subgroup of `Hⁿ(Sₚ,M)` where
  `Sₚ` is a Sylow `p`-subgroup of `S`.
  Since `p`-groups are solvable, the previous theorem implies that `Hⁿ(Sₚ,M) ≅ 0`.
  This shows that `Hⁿ(S,M)` has no elements of finite order.
  Since `n > 0`, the cohomology groups are torsion.
  -/
  sorry

instance Rep.dimensionShift.up_trivialCohomology [Finite G] (M : Rep R G) [M.TrivialCohomology] :
    (up.obj M).TrivialCohomology := sorry

instance Rep.dimensionShift.down_trivialCohomology [Finite G] (M : Rep R G) [M.TrivialCohomology] :
    (down.obj M).TrivialCohomology := sorry

instance Rep.tateCohomology_of_trivialCohomology [Finite G] (M : Rep R G) [M.TrivialCohomology] :
    M.TrivialTateCohomology := sorry

instance Rep.trivialHomology_of_trivialCohomology [Finite G] (M : Rep R G) [M.TrivialCohomology] :
    M.TrivialHomology := sorry
