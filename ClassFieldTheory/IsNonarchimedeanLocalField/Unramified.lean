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

instance isSplittingField :
    IsSplittingField K (UnramifiedExtension K n) (X ^ (Nat.card 𝓀[K] ^ n - 1) - 1) :=
  .splittingField _

theorem finrank_unramifiedExtension_zero : Module.finrank K (UnramifiedExtension K 0) = 1 := by
  have := isSplittingField K 0
  rw [pow_zero, Nat.sub_self, pow_zero, sub_self, isSplittingField_iff_intermediateField,
    rootSet_zero, IntermediateField.adjoin_empty,
    IntermediateField.bot_eq_top_iff_finrank_eq_one] at this
  exact this.2

instance : IsGalois K (UnramifiedExtension K n) := by
  obtain _ | n := n
  · have := finrank_unramifiedExtension_zero K
    rw [← IntermediateField.bot_eq_top_iff_finrank_eq_one] at this
    rw [← isGalois_iff_isGalois_top, ← this]
    exact isGalois_bot
  refine .of_separable_splitting_field (p := X ^ (Nat.card 𝓀[K] ^ (n + 1) - 1) - 1) ?_
  rw [X_pow_sub_one_separable_iff, ← map_natCast (algebraMap 𝒪[K] K),
    ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  refine ne_zero_of_map (f := algebraMap 𝒪[K] 𝓀[K]) ?_
  have hp := Fact.mk <| prime_ringChar K
  have := ZMod.algebra
  rw [map_natCast, ne_eq, CharP.cast_eq_zero_iff,
    Module.natCard_eq_pow_finrank (K := ZMod (ringChar 𝓀[K])), Nat.card_zmod, ← pow_mul,
    Nat.dvd_sub_iff_right, Nat.dvd_one]
  · exact hp.out.ne_one
  · exact one_le_pow_of_one_le' hp.out.one_le _
  · exact dvd_pow_self _ <| mul_ne_zero Module.finrank_pos.ne' n.succ_ne_zero

variable {n} in
instance (hn : n ≠ 0) :
    HasEnoughRootsOfUnity (UnramifiedExtension K n) (Nat.card 𝓀[K] ^ n - 1) := by
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
