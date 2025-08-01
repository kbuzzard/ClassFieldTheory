import Mathlib
import ClassFieldTheory.GroupCohomology.«04_TateCohomology_def»
import ClassFieldTheory.GroupCohomology.«05_TrivialCohomology»
import ClassFieldTheory.GroupCohomology.«08_DimensionShift»
import ClassFieldTheory.GroupCohomology.«10_inflationRestriction»
import ClassFieldTheory.GroupCohomology.«09_CyclicGroup»

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

section Mathlib

@[simp, norm_cast]
theorem Pi.coe_evalMonoidHom.{u, v} {I : Type u} (f : I → Type v) [(i : I) → MulOneClass (f i)] (i : I) :
    ⇑(Pi.evalMonoidHom f i) = Function.eval i := rfl

theorem Subgroup.Quotient.nontrivial_of_ne_top {G : Type*} [Group G] {p : Subgroup G} (h : p ≠ ⊤) :
    Nontrivial (G ⧸ p) := by
  obtain ⟨x, -, notMem_s⟩ : ∃ x ∈ ⊤, x ∉ p := SetLike.exists_of_lt (lt_top_iff_ne_top.2 h)
  refine ⟨⟨QuotientGroup.mk x, QuotientGroup.mk 1, ?_⟩⟩
  simpa [QuotientGroup.eq] using notMem_s

theorem CommGroup.exists_mulHom_zmod_surjective_of_finite (G : Type*) [CommGroup G] [Finite G] [Nontrivial G] :
    ∃ n > 1, ∃ (f : G →* Multiplicative (ZMod n)), (⇑f).Surjective := by
  obtain ⟨ι, _, n, hn1, ⟨equiv⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  obtain ⟨i⟩ : Nonempty ι := by
    rw [← not_isEmpty_iff]
    intro
    apply not_subsingleton G
    exact equiv.subsingleton
  refine ⟨n i, hn1 i, (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i).comp equiv, ?_⟩
  simp [Function.surjective_eval]

theorem exists_isCyclic_quotient_of_finite {G : Type*} [Group G] [Finite G] {H : Subgroup G} [H.Normal]
    (hH: H ≠ ⊤) (comm : IsMulCommutative (G ⧸ H)) : ∃ H' ∈ Set.Ico H ⊤, ∃ (_ : H'.Normal), IsCyclic (G ⧸ H') := by
  have := Subgroup.Quotient.nontrivial_of_ne_top hH
  obtain ⟨n, hn, f, hf⟩ := CommGroup.exists_mulHom_zmod_surjective_of_finite (G ⧸ H)
  refine ⟨(f.comp (QuotientGroup.mk' H)).ker, ?_, inferInstance, ?_⟩
  · rw [Set.mem_Ico, ← MonoidHom.comap_ker, ← Subgroup.map_le_iff_le_comap,
      QuotientGroup.map_mk'_self, and_iff_right bot_le, lt_top_iff_ne_top,
      ← Subgroup.comap_top (QuotientGroup.mk' H), (Subgroup.comap_injective (QuotientGroup.mk'_surjective H)).ne_iff,
      ne_eq, MonoidHom.ker_eq_top_iff]
    rintro rfl
    apply Fact.mk at hn
    have := uniqueOfSurjectiveOne (G ⧸ H) hf
    exact not_subsingleton (ZMod n) Multiplicative.ofAdd.subsingleton
  · exact (QuotientGroup.quotientKerEquivRange _).isCyclic.2 inferInstance

theorem solvable_ind {G : Type*} [Group G] [IsSolvable G] [Finite G] {motive : Subgroup G → Prop}
    (bot : motive ⊥) (ind : ∀ (H H' : Subgroup G) (_ : H ≤ H') (normal : (H.subgroupOf H').Normal),
      IsCyclic (H' ⧸ H.subgroupOf H') → motive H → motive H') (t : Subgroup G) : motive t := by
  by_cases ht : t = ⊥
  · exact ht ▸ bot
  · have hhh : ⁅t, t⁆ < t := IsSolvable.commutator_lt_of_ne_bot ht
    have sub_eq : (⁅t, t⁆).subgroupOf t = commutator t := by
      apply Subgroup.map_injective t.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hhh.le, map_commutator_eq, Subgroup.range_subtype]
    have normal : ((⁅t, t⁆).subgroupOf t).Normal := by
      rw [sub_eq]
      infer_instance
    have comm : IsMulCommutative (t ⧸ (⁅t, t⁆).subgroupOf t) := by
      revert normal
      rw [sub_eq]
      intro normal
      simp_rw [← Abelianization.eq_def]
      exact ⟨⟨mul_comm⟩⟩
    have htt : (⁅t, t⁆).subgroupOf t ≠ ⊤ := by simpa using hhh.not_ge
    obtain ⟨t', ⟨-, ht'⟩, _, cyclic⟩ := exists_isCyclic_quotient_of_finite htt comm
    have h : (Subgroup.map t.subtype t').subgroupOf t = t' := by
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective t.subtype_injective]
    have normal : ((Subgroup.map t.subtype t').subgroupOf t).Normal :=
      (congrArg Subgroup.Normal h).mpr inferInstance
    apply ind (t'.map t.subtype) t ((Subgroup.map_mono ht'.le).trans_eq
      ((MonoidHom.range_eq_map t.subtype).symm.trans t.range_subtype)) normal
      ((QuotientGroup.quotientMulEquivOfEq h).isCyclic.2 cyclic)
    have : Subgroup.map t.subtype t' < t := by
      apply ((Subgroup.map_lt_map_iff_of_injective t.subtype_injective).2 ht').trans_eq
      rw [← MonoidHom.range_eq_map t.subtype, t.range_subtype]
    exact solvable_ind bot ind (Subgroup.map t.subtype t')
termination_by wellFounded_lt.wrap t

end Mathlib
open
  CategoryTheory
  CategoryTheory.Limits
  groupCohomology
  Rep
  dimensionShift

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]

attribute [local instance] Fintype.ofFinite in
-- set_option maxHeartbeats 600000 in
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


def _root_.groupCohomology.pTorsionEquivSylow (M : Rep R G) (n p : ℕ) (hp : p.Prime) :
    ModuleCat.of R (Submodule.torsionBySet R (groupCohomology M (n + 1)) (Submonoid.powers (p : R)))
    ≅ groupCohomology (M ↓ (Sylow.toSubgroup
    (Classical.choice (α := Sylow p G) inferInstance)).subtype) (n + 1) := sorry

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
