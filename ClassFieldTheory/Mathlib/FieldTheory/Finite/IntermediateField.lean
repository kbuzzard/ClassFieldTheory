/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import ClassFieldTheory.Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Results on intermediate fields of finite fields -/

open Polynomial

namespace FiniteField

/-- For each `n`, `{x : L | x ^ q ^ n = x}` is an intermediate field (where `q = Nat.card K`). -/
def intermediateField (K L : Type*) [Field K] [Field L] [Finite L] [Algebra K L] (n : ℕ) :
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

theorem mem_intermediateField_iff {x : L} :
    x ∈ intermediateField K L n ↔ x ^ Nat.card K ^ n = x := Iff.rfl

theorem intermediateField_eq_rootSet (hn : n ≠ 0) :
    (intermediateField K L n : Set L) = (X ^ Nat.card K ^ n - X : L[X]).rootSet L := by
  have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
  ext x
  rw [mem_rootSet_of_ne (FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn Finite.one_lt_card)]
  simp [mem_intermediateField_iff, sub_eq_zero]

theorem mem_intermediateField_iff' {x : L} :
    x ∈ intermediateField K L n ↔ x = 0 ∨ x ^ (Nat.card K ^ n - 1) = 1 := by
  have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
  have : 2 ≤ Nat.card K := Finite.one_lt_card
  have h : 1 ≤ Nat.card K ^ n := Nat.pow_pos (by grind)
  conv_lhs => rw [mem_intermediateField_iff, ← Nat.sub_add_cancel h]
  rw [pow_succ, mul_left_eq_self₀, or_comm]

theorem intermediateField_eq_insert_zero_nthRootsFinset_one (hn : n ≠ 0) :
    (intermediateField K L n : Set L) =
    insert 0 (nthRootsFinset (Nat.card K ^ n - 1) (1 : L) : Set L) := by
  have := Finite.of_injective _ <| FaithfulSMul.algebraMap_injective K L
  have : 2 ≤ Nat.card K := Finite.one_lt_card
  have h2n : 2 ≤ Nat.card K ^ n := one_lt_pow' (M := ℕ) this hn
  ext x
  rw [SetLike.mem_coe, mem_intermediateField_iff', Set.mem_insert_iff, SetLike.mem_coe,
    mem_nthRootsFinset (by grind)]

theorem adjoin_eq_intermediateField_of_isPrimitiveRoot
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

/-- The minimal polynomial of a primitive `(q^n-1)`-st root of unity has degree `n`. -/
theorem degree_minpoly_of_isPrimitiveRoot
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
    ← (X_pow_sub_X_splits hζ).natDegree_eq_card_roots,
    FiniteField.X_pow_card_sub_X_natDegree_eq _ (by grind), Fintype.card_eq_nat_card]

variable (F : Type*) [Field F] [Finite F]

open FiniteField

theorem rootsOfUnity_eq_top : rootsOfUnity (Nat.card F - 1) F = ⊤ :=
  have := Fintype.ofFinite F
  eq_top_iff.mpr fun x _ ↦ Units.ext <| by simp [FiniteField.pow_card_sub_one_eq_one _ x.ne_zero]

instance : HasEnoughRootsOfUnity F (Nat.card F - 1) := by
  have := Finite.one_lt_card (α := F)
  have : NeZero (Nat.card F - 1) := .mk <| by grind
  exact .of_card_le <| by simp [Fintype.card_eq_nat_card, rootsOfUnity_eq_top, Nat.card_units]
