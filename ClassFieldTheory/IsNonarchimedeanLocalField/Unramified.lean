/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.LocalCFT.Teichmuller
import ClassFieldTheory.Mathlib.RingTheory.HenselPolynomial
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-! # Unramified extension of local field of a given degree

This file shows that if `K` is a non-archimedean local field and `n > 0` is any positive integer,
then there is a unique (up to in general non-unique isomorphism) unramified extension of `K` of
degree `n`.
-/

noncomputable section

namespace IsNonarchimedeanLocalField

open Polynomial ValuativeRel

/-- **The** unramified extension of degree `n > 0` of a given non-archimedean local field `K`. -/
def UnramifiedExtension (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : Type _ :=
  SplittingField (X ^ (Nat.card 𝓀[K] ^ n - 1) - 1 : K[X])
deriving Field, Algebra K, FiniteDimensional K

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (n : ℕ)

instance : ValuativeRel (UnramifiedExtension K n) :=
  (isNonarchimedeanLocalField_of_finiteDimensional K _).choose

instance : ValuativeExtension K (UnramifiedExtension K n) :=
  (isNonarchimedeanLocalField_of_finiteDimensional K _).choose_spec.choose

instance : TopologicalSpace (UnramifiedExtension K n) :=
  (isNonarchimedeanLocalField_of_finiteDimensional K _).choose_spec.choose_spec.choose

instance : IsNonarchimedeanLocalField (UnramifiedExtension K n) :=
  (isNonarchimedeanLocalField_of_finiteDimensional K _).choose_spec.choose_spec.choose_spec

instance UnramifiedExtension.isSplittingField :
    IsSplittingField K (UnramifiedExtension K n) (X ^ (Nat.card 𝓀[K] ^ n - 1) - 1) :=
  .splittingField _

theorem UnramifiedExtension.splits :
    (X ^ (Nat.card 𝓀[K] ^ n - 1) - 1 : (UnramifiedExtension K n)[X]).Splits (.id _) := by
  have := (UnramifiedExtension.isSplittingField K n).splits
  simpa using (splits_id_iff_splits _).mpr this

theorem UnramifiedExtension.factors :
    (X ^ (Nat.card 𝓀[K] ^ n - 1) - 1 : (UnramifiedExtension K n)[X]).Factors := by
  simpa [Splits] using splits K n

open UnramifiedExtension

section zero

theorem finrank_unramifiedExtension_zero : Module.finrank K (UnramifiedExtension K 0) = 1 := by
  have := UnramifiedExtension.isSplittingField K 0
  rw [pow_zero, Nat.sub_self, pow_zero, sub_self, isSplittingField_iff_intermediateField,
    rootSet_zero, IntermediateField.adjoin_empty,
    IntermediateField.bot_eq_top_iff_finrank_eq_one] at this
  exact this.2

instance : Subsingleton (Subalgebra K (UnramifiedExtension K 0)) :=
  subsingleton_of_bot_eq_top <| Subalgebra.bot_eq_top_of_finrank_eq_one <|
    finrank_unramifiedExtension_zero K

instance : Subsingleton (IntermediateField K (UnramifiedExtension K 0)) :=
  IntermediateField.toSubalgebra_injective.subsingleton

end zero

-- An auxiliary lemma that we might need more than once
theorem card_residue_pow_sub_one_in_residue_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 :) : 𝓀[K]) ≠ 0 := by
  have hp := Fact.mk <| prime_ringChar K
  have := ZMod.algebra
  rw [ne_eq, CharP.cast_eq_zero_iff, Module.natCard_eq_pow_finrank (K := ZMod (ringChar 𝓀[K])),
    Nat.card_zmod, ← pow_mul, Nat.dvd_sub_iff_right, Nat.dvd_one]
  · exact hp.out.ne_one
  · exact one_le_pow_of_one_le' hp.out.one_le _
  · exact dvd_pow_self _ <| mul_ne_zero Module.finrank_pos.ne' hn

-- An auxiliary lemma that we might need more than once
theorem card_residue_pow_sub_one_in_integers_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 :) : 𝒪[K]) ≠ 0 := by
  refine ne_zero_of_map (f := algebraMap 𝒪[K] 𝓀[K]) ?_
  rw [map_natCast]
  exact card_residue_pow_sub_one_in_residue_ne_zero K hn

-- An auxiliary lemma that we might need more than once
theorem card_residue_pow_sub_one_in_field_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 :) : K) ≠ 0 := by
  rw [← map_natCast (algebraMap 𝒪[K] K), ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  exact card_residue_pow_sub_one_in_integers_ne_zero K hn

-- An auxiliary lemma that we might need more than once
theorem card_residue_pow_sub_one_in_unramifiedExtension_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 :) : UnramifiedExtension K n) ≠ 0 := by
  rw [← map_natCast (algebraMap K _), ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  exact card_residue_pow_sub_one_in_field_ne_zero K hn

-- An auxiliary lemma that we might need more than once
theorem card_residue_pow_sub_one_in_ne_zero {n : ℕ} (hn : n ≠ 0) :
    Nat.card 𝓀[K] ^ n - 1 ≠ 0 :=
  ne_zero_of_map (f := algebraMap ℕ K) <| card_residue_pow_sub_one_in_field_ne_zero K hn

instance : IsGalois K (UnramifiedExtension K n) := by
  obtain _ | n := n
  · have := finrank_unramifiedExtension_zero K
    rw [← IntermediateField.bot_eq_top_iff_finrank_eq_one] at this
    rw [← isGalois_iff_isGalois_top, ← this]
    exact isGalois_bot
  refine .of_separable_splitting_field (p := X ^ (Nat.card 𝓀[K] ^ (n + 1) - 1) - 1) ?_
  rw [X_pow_sub_one_separable_iff]
  exact card_residue_pow_sub_one_in_field_ne_zero K n.succ_ne_zero

-- move
theorem _root_.Polynomial.nodup_nthRoots_of_natCast_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {a : R} (hn : (n : R) ≠ 0) (ha : a ≠ 0) : (nthRoots n a).Nodup := by
  have : (⇑(algebraMap R (FractionRing R))).Injective := FaithfulSMul.algebraMap_injective ..
  rw [nthRoots, ← Multiset.nodup_map_iff_of_injective this]
  refine Multiset.nodup_of_le (map_roots_le_of_injective _ this) ?_
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  refine nodup_roots <| separable_X_pow_sub_C _ ?_ (map_ne_zero_iff _ this |>.mpr ha)
  · rw [← map_natCast (algebraMap R _)]
    exact map_ne_zero_iff _ this |>.mpr hn

-- move
theorem _root_.Polynomial.nodup_nthRoots_one_of_natCast_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (hn : (n : R) ≠ 0) : (nthRoots n (1 : R)).Nodup :=
  nodup_nthRoots_of_natCast_ne_zero hn one_ne_zero

-- move?
theorem _root_.image_rootsOfUnity_eq_nthRoots {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (hn : n ≠ 0) : Units.val '' (rootsOfUnity n R : Set Rˣ) = (nthRootsFinset n 1 : Finset R) := by
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, mem_rootsOfUnity, Units.ext_iff,
    Units.val_pow_eq_pow_val, Units.val_one, mem_nthRootsFinset (pos_of_ne_zero hn)]
  exact ⟨by grind, fun hxn ↦ ⟨.ofPowEqOne _ _ hxn hn, hxn, rfl⟩⟩

-- move?
/-- If a domain `R` satisfies that `X ^ n - 1` splits in `R` and `n ≠ 0` then `R` has enough
`n`-th roots of unity. -/
theorem _root_.HasEnoughRootsOfUnity.of_splits {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (hr : (X ^ n - 1 : R[X]).Factors) (hn : (n : R) ≠ 0) : HasEnoughRootsOfUnity R n := by
  have := NeZero.mk <| show n ≠ 0 by aesop
  refine .of_card_le ?_
  classical
  rw [Fintype.card_eq_nat_card, ← SetLike.coe_sort_coe,
    ← Nat.card_image_of_injective Units.val_injective, image_rootsOfUnity_eq_nthRoots this.out,
    SetLike.coe_sort_coe, Nat.card_eq_finsetCard, nthRootsFinset,
    Multiset.toFinset_card_of_nodup (nodup_nthRoots_one_of_natCast_ne_zero hn), nthRoots, C_1,
    ← hr.natDegree_eq_card_roots, ← C_1, natDegree_X_pow_sub_C]

variable {n} in
instance [NeZero n] :
    HasEnoughRootsOfUnity (UnramifiedExtension K n) (Nat.card 𝓀[K] ^ n - 1) :=
  .of_splits (factors K n) <| card_residue_pow_sub_one_in_unramifiedExtension_ne_zero K NeZero.out

example [NeZero n] : ∃ ζ : UnramifiedExtension K n, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1) :=
  HasEnoughRootsOfUnity.exists_primitiveRoot _ _

theorem UnramifiedExtension.top_eq_adjoin_roots :
    (⊤ : Subalgebra K (UnramifiedExtension K n)) = Algebra.adjoin K
      (nthRootsFinset (Nat.card 𝓀[K] ^ n - 1) 1 : Finset (UnramifiedExtension K n)) := by
  rw [← (isSplittingField K n).adjoin_rootSet, rootSet, aroots, nthRootsFinset, nthRoots]
  simp

-- move
/-- If `M` has enough `n`-th roots of unity and we are given a primitive root `ζ`, then any `n`-th
root of unity is a power of `ζ`. -/
theorem _root_.HasEnoughRootsOfUnity.exists_pow {M : Type*} [CommMonoid M] {n : ℕ} (hn : n ≠ 0)
    [HasEnoughRootsOfUnity M n] {ζ : M} (hζ : IsPrimitiveRoot ζ n) {ω : M} (hω : ω ^ n = 1) :
    ∃ i < n, ζ ^ i = ω := by
  have := NeZero.mk hn
  let ζ' : rootsOfUnity n M := ⟨.ofPowEqOne _ _ hζ.1 hn, Units.ext hζ.1⟩
  have hoζ' : orderOf ζ' = n := by
    rw [ ← orderOf_injective (Subgroup.subtype _) Subtype.val_injective ζ',
      ← orderOf_injective (Units.coeHom _) Units.val_injective]
    exact hζ.eq_orderOf.symm
  have hζ' : Subgroup.zpowers ζ' = ⊤ := by
    refine Subgroup.eq_top_of_le_card _ ?_
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_zpowers, hoζ']
  classical
  simp_rw [Subgroup.eq_top_iff', mem_zpowers_iff_mem_range_orderOf, Finset.mem_image,
    Finset.mem_range, hoζ'] at hζ'
  obtain ⟨i, hin, hi⟩ := hζ' ⟨.ofPowEqOne _ _ hω hn, Units.ext hω⟩
  exact ⟨i, hin, congr(($hi).val.val)⟩

theorem UnramifiedExtension.top_eq_adjoin_primitive_root
    {ζ : UnramifiedExtension K n} (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    (⊤ : Subalgebra K (UnramifiedExtension K n)) = Algebra.adjoin K {ζ} := by
  obtain _ | n := n
  · subsingleton
  have := card_residue_pow_sub_one_in_ne_zero K n.succ_ne_zero
  rw [top_eq_adjoin_roots]
  refine le_antisymm (Algebra.adjoin_le fun ω hω ↦ ?_) <|
    Algebra.adjoin_le <| Set.singleton_subset_iff.mpr <| Algebra.subset_adjoin ?_
  · rw [SetLike.mem_coe, mem_nthRootsFinset (pos_of_ne_zero this)] at hω
    obtain ⟨i, _, rfl⟩ := HasEnoughRootsOfUnity.exists_pow this hζ hω
    exact pow_mem (Algebra.subset_adjoin <| Set.mem_singleton _) _
  · rw [SetLike.mem_coe, mem_nthRootsFinset (pos_of_ne_zero this), hζ.1]

-- move?
/-- The minimal polynomial of a primitive `(q^n-1)`-st root of unity has degree `n`. -/
theorem _root_.FiniteField.degree_minpoly_of_isPrimitiveRoot
    {K L : Type*} [Field K] [Field L] [Finite L] [Algebra K L] {n : ℕ} (hn : n ≠ 0)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (Nat.card K ^ n - 1)) : (minpoly K ζ).natDegree = n := by
  have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
  sorry

variable {n} in
theorem finrank_unramifiedExtension (hn : n ≠ 0) :
    Module.finrank K (UnramifiedExtension K n) = n :=
  sorry

instance : IsUnramified K (UnramifiedExtension K n) :=
  sorry

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
  (E : IntermediateField K L)

instance : ValuativeRel E := sorry
instance : ValuativeExtension K E := sorry
instance : IsNonarchimedeanLocalField E := sorry

theorem isUnramified_intermediateField_iff {E : IntermediateField K L} :
    IsUnramified K E ↔ E = .adjoin K (rootSet (X ^ Nat.card 𝓀[K] ^ (f K E) - 1 : K[X]) L) :=
  sorry

/-- If `L/K` is an extension of local fields and `Kf` is the unramified extension of `K` of
degree `f(L/K)` then `Kf → L`. This is the (non-unique) universal property of unramified
extensions. -/
def ofUnramifiedExtension : UnramifiedExtension K (f K L) →ₐ[K] L := sorry

end IsNonarchimedeanLocalField
