/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.LocalCFT.Teichmuller
import ClassFieldTheory.IsNonarchimedeanLocalField.EF
import ClassFieldTheory.Mathlib.RingTheory.HenselPolynomial
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
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
theorem card_residue_pow_sub_one_in_unramifiedExtension_residue_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 :) : 𝓀[UnramifiedExtension K n]) ≠ 0 := by
  rw [← map_natCast (algebraMap 𝓀[K] _), ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  exact card_residue_pow_sub_one_in_residue_ne_zero K hn

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

-- ????
theorem _root_.Multiset.toFinset_range {n : ℕ} : (Multiset.range n).toFinset = .range n :=
  Finset.val_injective (Finset.range n).nodup.dedup

-- move
theorem _root_.IsPrimitiveRoot.nthRoots_one_eq {R : Type*}
    [CommRing R] [IsDomain R] {n : ℕ}
    {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    nthRoots n (1 : R) = (Multiset.range n).map (ζ ^ ·) := by
  simp_rw [hζ.nthRoots_eq (one_pow n), mul_one]

-- move
theorem _root_.IsPrimitiveRoot.nthRootsFinset_one_eq {R : Type*}
    [CommRing R] [IsDomain R] [DecidableEq R] {n : ℕ}
    {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    nthRootsFinset n (1 : R) = (Finset.range n).image (ζ ^ ·) := by
  simp_rw [nthRootsFinset, hζ.nthRoots_one_eq, @Multiset.toFinset_map, Multiset.toFinset_range]
  congr
  subsingleton

-- move
/-- Over domain `R`, `ζ : R` is a primitive `n`-th root iff the multiset `{ ζ ^ i | 0 ≤ i < n }`
is equal to the multiset `nthRoots n 1`, and the multiset has no duplicates. -/
theorem _root_.isPrimitiveRoot_iff_nthRoots_and_nodup {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (hn : 1 < n) {ζ : R} :
    IsPrimitiveRoot ζ n ↔
    (Multiset.range n).map (ζ ^ ·) = nthRoots n 1 ∧ (nthRoots n (1 : R)).Nodup := by
  classical
  refine ⟨fun hζ ↦ ⟨hζ.nthRoots_one_eq.symm, hζ.nthRoots_one_nodup⟩,
    fun ⟨h₁, h₂⟩ ↦ IsPrimitiveRoot.iff (by grind) |>.mpr ⟨?_, fun i h0i hin ↦ ?_⟩⟩
  · rw [← mem_nthRoots (by grind), ← h₁, Multiset.mem_map]
    simp_rw [Multiset.mem_range]
    exact ⟨1, hn, pow_one ζ⟩
  · rw [← h₁] at h₂
    replace h₂ := Multiset.inj_on_of_nodup_map h₂
    simp_rw [Multiset.mem_range] at h₂
    simpa [h0i.ne'] using h₂ i hin 0 (h0i.trans hin)

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

theorem UnramifiedExtension.intermediateFieldTop_eq_adjoin_primitive_root
    {ζ : UnramifiedExtension K n} (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    (⊤ : IntermediateField K (UnramifiedExtension K n)) = .adjoin K {ζ} :=
  IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ <| by
    simp [top_eq_adjoin_primitive_root _ _ hζ]

-- move
section finite_field

/-- For each `n`, `{x : L | x ^ q ^ n = x}` is an intermediate field (where `q = Nat.card K`). -/
def _root_.FiniteField.intermediateField
    (K L : Type*) [Field K] [Field L] [Finite L] [Algebra K L] (n : ℕ) :
    IntermediateField K L where
  carrier := {x | x ^ Nat.card K ^ n = x}
  mul_mem' hx hy := by simp_all [mul_pow]
  add_mem' hx hy := by
    obtain ⟨p, _⟩ := CharP.exists K
    have := charP_of_injective_algebraMap' K (A := L) p
    have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
    have := Fintype.ofFinite K
    have := ZMod.algebra K p
    have := Fact.mk (CharP.char_is_prime K p)
    simp_all [Module.card_eq_pow_finrank (K := ZMod p) (V := K), ← pow_mul, add_pow_char_pow]
  algebraMap_mem' := by
    have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
    have := Fintype.ofFinite K
    simp [← map_pow, FiniteField.pow_card_pow]
  inv_mem' hx := by simp_all [inv_pow]

open FiniteField IntermediateField

variable {K L : Type*} [Field K] [Field L] [Finite L] [Algebra K L] {n : ℕ}

theorem _root_.FiniteField.mem_intermediateField_iff {x : L} :
    x ∈ intermediateField K L n ↔ x ^ Nat.card K ^ n = x := Iff.rfl

theorem _root_.FiniteField.intermediateField_eq_rootSet (hn : n ≠ 0) :
    (intermediateField K L n : Set L) = (X ^ Nat.card K ^ n - X : L[X]).rootSet L := by
  have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
  ext x
  rw [mem_rootSet_of_ne (FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn Finite.one_lt_card)]
  simp [mem_intermediateField_iff, sub_eq_zero]

theorem _root_.FiniteField.mem_intermediateField_iff' {x : L} :
    x ∈ intermediateField K L n ↔ x = 0 ∨ x ^ (Nat.card K ^ n - 1) = 1 := by
  have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
  have : 2 ≤ Nat.card K := Finite.one_lt_card
  have h : 1 ≤ Nat.card K ^ n := Nat.pow_pos (by grind)
  conv_lhs => rw [mem_intermediateField_iff, ← Nat.sub_add_cancel h]
  rw [pow_succ, mul_left_eq_self₀, or_comm]

theorem _root_.FiniteField.intermediateField_eq_insert_zero_nthRootsFinset_one (hn : n ≠ 0) :
    (intermediateField K L n : Set L) =
    insert 0 (nthRootsFinset (Nat.card K ^ n - 1) (1 : L) : Set L) := by
  have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
  have : 2 ≤ Nat.card K := Finite.one_lt_card
  have h2n : 2 ≤ Nat.card K ^ n := one_lt_pow' (M := ℕ) this hn
  ext x
  rw [SetLike.mem_coe, mem_intermediateField_iff', Set.mem_insert_iff, SetLike.mem_coe,
    mem_nthRootsFinset (by grind)]

theorem _root_.FiniteField.adjoin_eq_intermediateField_of_isPrimitiveRoot
    (hn : n ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ (Nat.card K ^ n - 1)) :
    adjoin K {ζ} = intermediateField K L n := by
  have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
  have : HasEnoughRootsOfUnity L (Nat.card K ^ n - 1) := ⟨⟨_, hζ⟩, inferInstance⟩
  have h2n : 2 ≤ Nat.card K ^ n := (Nat.le_pow (pos_of_ne_zero hn)).trans <|
    (Nat.pow_le_pow_iff_left hn).mpr Finite.one_lt_card
  have h1n : 1 ≤ Nat.card K ^ n := by grind
  refine le_antisymm (adjoin_le_iff.mpr <| Set.singleton_subset_iff.mpr ?_) fun x hx ↦ ?_
  · rw [SetLike.mem_coe, mem_intermediateField_iff', hζ.1]
    exact .inr rfl
  · rw [mem_intermediateField_iff'] at hx
    obtain rfl | hx := hx
    · simp
    · obtain ⟨i, _, rfl⟩ := HasEnoughRootsOfUnity.exists_pow (by grind) hζ hx
      exact pow_mem (mem_adjoin_simple_self _ _) _

theorem _root_.X_pow_sub_X_factors_of_isPrimitiveRoot {R : Type*} [Field R]
    {n : ℕ} (hn : n ≠ 0) {ζ : R} (hζ : IsPrimitiveRoot ζ (n - 1)) :
    (X ^ n - X : R[X]).Factors := by
  rw [← Nat.sub_add_cancel (pos_of_ne_zero hn), pow_succ, ← sub_one_mul]
  exact .mul (by simpa [Splits] using X_pow_sub_one_splits hζ) .X

/-- The minimal polynomial of a primitive `(q^n-1)`-st root of unity has degree `n`. -/
theorem _root_.FiniteField.degree_minpoly_of_isPrimitiveRoot
    (hn : n ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ (Nat.card K ^ n - 1)) :
    (minpoly K ζ).natDegree = n := by
  have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (intermediateField K L n)
  have key : adjoin K {ζ} = FiniteField.intermediateField K L n :=
    adjoin_eq_intermediateField_of_isPrimitiveRoot hn hζ
  obtain ⟨p, _⟩ := CharP.exists K
  have := Fact.mk <| CharP.char_is_prime K p
  have := ZMod.algebra K p
  have := charP_of_injective_algebraMap' K (A := L) p
  have : 1 < Nat.card K := Finite.one_lt_card
  have : 1 < Nat.card K ^ n := one_lt_pow' this hn
  have : p ∣ Nat.card K ^ n := dvd_pow (Nat.card_zmod p ▸ AddSubgroup.card_dvd_of_injective
    (algebraMap (ZMod p) K) (FaithfulSMul.algebraMap_injective _ _)) hn
  classical
  rw [← IntermediateField.adjoin.finrank (.of_finite _ _), key,
    ← Nat.pow_right_inj (Finite.one_lt_card (α := K)),
    Nat.card_eq_fintype_card, ← Module.card_eq_pow_finrank, Fintype.card_eq_nat_card,
    ← SetLike.coe_sort_coe, intermediateField_eq_rootSet hn, rootSet, aroots,
    Algebra.algebraMap_self, Polynomial.map_id, SetLike.coe_sort_coe, Nat.card_eq_finsetCard,
    Multiset.toFinset_card_of_nodup (nodup_roots <| galois_poly_separable _ _ this),
    ← (X_pow_sub_X_factors_of_isPrimitiveRoot (by grind) hζ).natDegree_eq_card_roots,
    FiniteField.X_pow_card_sub_X_natDegree_eq _ (by grind), Fintype.card_eq_nat_card]

end finite_field

/-- If `f : R →+* S` and `ζ : R` is a primitive `n`-th root and `(n : S) ≠ 0` then `f ζ` is
a primitive `n`-th root in `S`. -/
theorem _root_.IsPrimitiveRoot.map_of_ne_zero {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (f : R →+* S) (hn : (n : S) ≠ 0) :
    IsPrimitiveRoot (f ζ) n := by
  by_cases hn1 : n = 1
  · rw [hn1, IsPrimitiveRoot.one_right_iff] at hζ
    simp [hζ, hn1]
  have : n ≠ 0 := by aesop
  replace hn1 : 1 < n := by grind
  have hζ' := hζ
  rw [isPrimitiveRoot_iff_nthRoots_and_nodup hn1] at hζ' ⊢
  constructor
  · simp_rw [← map_pow]
    change Multiset.map (f ∘ (ζ ^ ·)) _ = _
    rw [← Multiset.map_map, hζ'.1, nthRoots,
      (monic_X_pow_sub_C _ this).roots_map_of_card_eq_natDegree, Polynomial.map_sub,
      Polynomial.map_pow, map_X, map_C, map_one, nthRoots]
    · rw [← nthRoots, hζ.card_nthRoots_one, natDegree_X_pow_sub_C]
  · exact nodup_nthRoots_one_of_natCast_ne_zero hn

-- ask andrew
instance : IsAdicComplete 𝓂[K] 𝒪[K] := sorry

variable {n} in
private theorem finrank_unramifiedExtension_and_residue (hn : n ≠ 0) :
    Module.finrank K (UnramifiedExtension K n) = n ∧
    n ≤ Module.finrank 𝓀[K] 𝓀[UnramifiedExtension K n] := by
  have := NeZero.mk hn
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (UnramifiedExtension K n) (Nat.card 𝓀[K] ^ n - 1)
  have : 1 < Nat.card 𝓀[K] ^ n := Nat.one_lt_pow hn Finite.one_lt_card
  have h₁ : IsIntegral 𝒪[K] ζ := .of_pow (n := Nat.card 𝓀[K] ^ n - 1) (by grind)
    (by rw [hζ.1]; exact isIntegral_one)
  lift ζ to 𝒪[UnramifiedExtension K n] using isIntegral_iff.mp h₁
  have h₂ : IsIntegral 𝒪[K] ζ := h₁.tower_bot Subtype.val_injective
  have h₃ : minpoly 𝒪[K] ζ.val = minpoly 𝒪[K] ζ :=
    minpoly.algHom_eq (Algebra.algHom _ _ _) Subtype.val_injective ζ
  have h₄ : minpoly 𝒪[K] ζ ∣ X ^ Nat.card 𝓀[K] ^ n - X := by
    rw [← map_dvd_map (f := algebraMap 𝒪[K] K) (FaithfulSMul.algebraMap_injective _ _)
      (minpoly.monic h₂), ← h₃, ← minpoly.isIntegrallyClosed_eq_field_fractions' K h₁]
    refine minpoly.dvd _ _ ?_
    rw [← Nat.sub_add_cancel (show 1 ≤ Nat.card 𝓀[K] ^ n by grind)]
    simp [pow_succ, hζ.1]
  let ⟨p, hp⟩ := CharP.exists 𝓀[K]
  have := Fact.mk <| CharP.char_is_prime 𝓀[K] p
  have := ZMod.algebra 𝓀[K] p
  have h₅ : p ∣ Nat.card 𝓀[K] ^ n := dvd_pow (Nat.card_zmod p ▸ AddSubgroup.card_dvd_of_injective
    (algebraMap (ZMod p) 𝓀[K]) (FaithfulSMul.algebraMap_injective _ _)) hn
  have h₆ : (map (IsLocalRing.residue 𝒪[K]) (minpoly 𝒪[K] ζ)).Separable :=
    Polynomial.Separable.of_dvd (by simpa using galois_poly_separable p _ h₅) <|
      map_dvd (IsLocalRing.residue _) h₄
  have key : map (IsLocalRing.residue 𝒪[K]) (minpoly 𝒪[K] ζ) =
      minpoly 𝓀[K] (IsLocalRing.residue _ ζ) :=
    minpoly.eq_of_irreducible_of_monic
      (irreducible_map_of_irreducible_of_separable_map (minpoly.monic h₂) (minpoly.irreducible h₂)
        h₆)
      (by rw [← IsLocalRing.ResidueField.algebraMap_eq 𝒪[K], aeval_map_algebraMap,
        show ⇑(IsLocalRing.residue 𝒪[UnramifiedExtension K n]) = Algebra.algHom 𝒪[K] _ _ from rfl,
        aeval_algHom_apply, minpoly.aeval, map_zero])
      ((minpoly.monic h₂).map _)
  have h₇ : IsIntegral 𝓀[K] (IsLocalRing.residue _ ζ) :=
    (h₂.map <| Algebra.algHom 𝒪[K] _ _).tower_top
  have hζ₁ := hζ.of_map_of_injective (Subring.subtype_injective _)
  have hζ₂ := hζ₁.map_of_ne_zero (IsLocalRing.residue _) <|
    card_residue_pow_sub_one_in_unramifiedExtension_residue_ne_zero K hn
  have h₈ : (minpoly 𝓀[K] ((IsLocalRing.residue 𝒪[UnramifiedExtension K n]) ζ)).natDegree = n :=
    FiniteField.degree_minpoly_of_isPrimitiveRoot hn hζ₂
  constructor
  · rw [← IntermediateField.finrank_top', intermediateFieldTop_eq_adjoin_primitive_root _ _ hζ,
      IntermediateField.adjoin.finrank (h₁.tower_top),
      minpoly.isIntegrallyClosed_eq_field_fractions' K h₁,
      natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _),
      ← Monic.natDegree_map (minpoly.monic h₁) (IsLocalRing.residue 𝒪[K]), h₃, key, h₈]
  · conv_lhs => rw [← h₈]
    exact minpoly.natDegree_le _

variable {n} in
@[simp] theorem finrank_unramifiedExtension (hn : n ≠ 0) :
    Module.finrank K (UnramifiedExtension K n) = n :=
  (finrank_unramifiedExtension_and_residue K hn).1

variable {n} in
@[simp] theorem f_unramifiedExtension (hn : n ≠ 0) :
    f K (UnramifiedExtension K n) = n := by
  refine le_antisymm ?_ (by simpa [hn, f] using (finrank_unramifiedExtension_and_residue K hn).2)
  conv_rhs => rw [← finrank_unramifiedExtension K hn]
  exact f_le_n _ _

instance : IsUnramified K (UnramifiedExtension K n) := .mk <| by
  obtain rfl | hn := eq_or_ne n 0
  · exact e_eq_one_of_n_eq_one _ _ <| finrank_unramifiedExtension_zero K
  rw [← Nat.mul_left_inj (ne_of_gt <| f_pos K (UnramifiedExtension K n)),
    one_mul, e_mul_f_eq_n]
  simp [hn]

section more_stuff_on_finite_fields
variable (F : Type*) [Field F] [Finite F]

open FiniteField

theorem _root_.FiniteField.rootsOfUnity_eq_top : rootsOfUnity (Nat.card F - 1) F = ⊤ :=
  have := Fintype.ofFinite F
  eq_top_iff.mpr fun x _ ↦ Units.ext <| by simp [FiniteField.pow_card_sub_one_eq_one _ x.ne_zero]

instance : HasEnoughRootsOfUnity F (Nat.card F - 1) := by
  have := Finite.one_lt_card (α := F)
  have : NeZero (Nat.card F - 1) := .mk <| by grind
  exact .of_card_le <| by simp [Fintype.card_eq_nat_card, rootsOfUnity_eq_top, Nat.card_units]

end more_stuff_on_finite_fields

instance : HasEnoughRootsOfUnity K (Nat.card 𝓀[K] - 1) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot 𝓀[K] (Nat.card 𝓀[K] - 1)
  have := Finite.one_lt_card (α := 𝓀[K])
  have : NeZero (Nat.card 𝓀[K] - 1) := .mk <| by grind
  exact ⟨⟨_, hζ.map_of_injective teichmuller_injective⟩, inferInstance⟩

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

/-- If `Kn` denotes the unramified extension of `K` of degree `n`, then `Kn` embeds into `L` if
`n ∣ f K L`. This is half of the universal property. -/
theorem nonempty_unramifiedExtension_alghom_of_dvd_f (n : ℕ) (hn : n ∣ f K L) :
    Nonempty (UnramifiedExtension K n →ₐ[K] L) := by
  have hf0 := NeZero.mk (f_pos K L).ne'
  have hn0 := NeZero.mk <| ne_zero_of_dvd_ne_zero hf0.out hn
  have h₁ := Nat.pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hn
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (UnramifiedExtension K n) (Nat.card 𝓀[K] ^ n - 1)
  have h₂ := pos_of_ne_zero <| card_residue_pow_sub_one_in_ne_zero K hn0.out
  have h₃ := pos_of_ne_zero <| card_residue_pow_sub_one_in_ne_zero K hf0.out
  refine IntermediateField.nonempty_algHom_of_adjoin_splits
    (forall_eq.mpr ⟨.of_pow h₂ <| hζ.1 ▸ isIntegral_one,
      .of_dvd (g := X ^ (Nat.card 𝓀[K] ^ n - 1) - C 1) ?_
        (X_pow_sub_C_ne_zero h₂ _) ?_⟩)
    (intermediateFieldTop_eq_adjoin_primitive_root K _ hζ).symm
  · rw [f_spec'] at h₁ h₃
    have := NeZero.mk h₃.ne'
    have := HasEnoughRootsOfUnity.of_dvd L h₁
    obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Nat.card 𝓀[K] ^ n - 1)
    simpa [Splits] using X_pow_sub_one_splits hζ'
  · conv_rhs => exact show _ = map (algebraMap K L) (X ^ (Nat.card 𝓀[K] ^ n - 1) - C 1) by simp
    rw [map_dvd_map', minpoly.dvd_iff]
    simp [hζ.1]

/-- The universal property of unramified extensions. -/
theorem nonempty_unramifiedExtension_alghom_iff_dvd_f {n : ℕ} (hn : n ≠ 0) :
    Nonempty (UnramifiedExtension K n →ₐ[K] L) ↔ n ∣ f K L :=
  ⟨fun ⟨φ⟩ ↦ f_unramifiedExtension K hn ▸ f_dvd_f φ,
  nonempty_unramifiedExtension_alghom_of_dvd_f _ _ _⟩

/-- If `L/K` is unramified, then `L` is isomorphic to `Kn` where `n = [L:K]`. -/
theorem nonempty_unramifiedExtension_algEquiv_of_isUnramified [IsUnramified K L] :
    Nonempty (UnramifiedExtension K (Module.finrank K L) ≃ₐ[K] L) := by
  obtain ⟨φ⟩ := nonempty_unramifiedExtension_alghom_of_dvd_f K L (Module.finrank K L)
    (IsUnramified.n_dvd_f K L)
  have : φ.fieldRange = ⊤ := IntermediateField.toSubalgebra_injective <|
    Subalgebra.toSubmodule_injective <| Submodule.eq_top_of_finrank_eq <| by
    change Module.finrank K (LinearMap.range φ.toLinearMap) = _
    rw [LinearMap.finrank_range_of_inj φ.toRingHom.injective,
      finrank_unramifiedExtension _ Module.finrank_pos.ne']
  exact ⟨(AlgEquiv.ofInjective φ φ.toRingHom.injective).trans <|
    (IntermediateField.equivOfEq this).trans <| IntermediateField.topEquiv⟩

/-- Any unramified extension is Galois. -/
instance [IsUnramified K L] : IsGalois K L :=
  let ⟨φ⟩ := nonempty_unramifiedExtension_algEquiv_of_isUnramified K L
  .of_algEquiv φ

/-- The maximal unramified subextension. -/
def maximalUnramified : IntermediateField K L :=
  (nonempty_unramifiedExtension_alghom_of_dvd_f K L (f K L) dvd_rfl).some.fieldRange

instance : IsUnramified K (maximalUnramified K L) := by
  unfold maximalUnramified
  infer_instance

variable {K L} (E : IntermediateField K L)

/-- The maximal unramified subextension is maximal. -/
theorem le_maximalUnramified_iff : E ≤ maximalUnramified K L ↔ IsUnramified K E := by
  refine ⟨fun h ↦ .comap <| show E →ₐ[K] maximalUnramified K L from Subalgebra.inclusion h,
    fun _ ↦ ?_⟩
  obtain ⟨φ₁⟩ := nonempty_unramifiedExtension_algEquiv_of_isUnramified K E
  have h₁ : Module.finrank K E ∣ f K L := .trans (IsUnramified.n_dvd_f K E) <| f_dvd_f_top ..
  obtain ⟨φ₂⟩ := nonempty_unramifiedExtension_alghom_of_dvd_f K (UnramifiedExtension K (f K L))
    (Module.finrank K E) (by simpa [f_unramifiedExtension _ (f_pos _ _).ne'])
  unfold maximalUnramified
  generalize Nonempty.some _ = φ₃
  rw [← IntermediateField.toSubalgebra_le_toSubalgebra, AlgHom.fieldRange_toSubalgebra,
    ← AlgHom.fieldRange_of_normal (E := E) (φ₃.comp (φ₂.comp φ₁.symm)),
    AlgHom.fieldRange_toSubalgebra]
  exact AlgHom.range_comp_le_range ..

end IsNonarchimedeanLocalField
