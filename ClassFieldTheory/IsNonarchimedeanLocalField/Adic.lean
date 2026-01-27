/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.IsNonarchimedeanLocalField.Basic
import Mathlib.RingTheory.AdicCompletion.Topology

/-! # Facts about the adic topology and local fields -/

namespace IsNonarchimedeanLocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open ValuativeRel WithZero

theorem maximalIdeal_pow_eq (n : ℕ) : ((𝓂[K] ^ n :) : Set 𝒪[K]) =
    Subtype.val ⁻¹' {x | valuation K x ≤ (valueGroupWithZeroIsoInt K).symm (exp (-n))} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ, Ideal.span_singleton_pow]
  ext x
  simp_rw [SetLike.mem_coe, Set.mem_preimage, Set.mem_setOf, Ideal.mem_span_singleton,
    (Valuation.integer.integers _).dvd_iff_le, map_pow, Algebra.algebraMap_ofSubsemiring_apply,
    valuation_irreducible hϖ, ← map_pow, ← exp_nsmul, smul_neg, Int.nsmul_eq_mul, mul_one]

theorem isAdic : IsAdic 𝓂[K] := by
  refine isAdic_iff.mpr ⟨fun n ↦ isOpen_induced_iff.mpr ?_, fun s hs ↦ ?_⟩
  · rw [maximalIdeal_pow_eq K]
    exact ⟨_, IsValuativeTopology.isOpen_closedBall (by simp), rfl⟩
  · simp_rw [maximalIdeal_pow_eq K]
    obtain ⟨t, ht, hts⟩ := (mem_nhds_induced _ _ _).mp hs;
    obtain ⟨n, hn, hnt⟩ := (IsValuativeTopology.hasBasis_nhds_zero' _).mem_iff.mp ht
    obtain ⟨n, rfl⟩ := (valueGroupWithZeroIsoInt K).symm.surjective n
    replace hn := EmbeddingLike.map_ne_zero_iff.mp hn
    lift n to ℤ using hn
    obtain ⟨m, hmn⟩ : ∃ m : ℕ, -m < n := ⟨n.natAbs + 1, by grind⟩
    refine ⟨m, fun x hx ↦ hts <| hnt ?_⟩
    simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq] at hx ⊢
    exact hx.trans_lt <| (map_lt_map_iff ..).mpr <| exp_lt_exp.mpr hmn

instance : IsAdicComplete 𝓂[K] 𝒪[K] :=
  let := IsTopologicalAddGroup.rightUniformSpace K
  (isAdic K).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

end IsNonarchimedeanLocalField
