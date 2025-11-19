/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import ClassFieldTheory.Cohomology.Functors.Restriction
import ClassFieldTheory.IsNonarchimedeanLocalField.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
/-

# 1 → 𝒪[K]ˣ → Kˣ → ℤ → 0

We construct the short exact sequence `0 → Additive (𝒪[K]ˣ) → Additive (Kˣ) → ℤ → 0` in
the following sense: we define the maps `ker_v K` and `v K`, prove the first is
injective, the second is surjective, and the pair is `Function.Exact`.

-/

namespace ValuativeRel

section proofWanted

-- I only need it for IsNonarchimedeanLocalField but it should be true in this generality
lemma valuation_eq_one_iff (K : Type*) [Field K] [ValuativeRel K] (x : K) :
  (ValuativeRel.valuation K) x = 1 ↔ ∃ r : 𝒪[K]ˣ, x = r := sorry

end proofWanted

def ker_v (K : Type*) [CommRing K] [ValuativeRel K] : Additive (𝒪[K]ˣ) →+ Additive Kˣ :=
  (Units.map (𝒪[K].subtype).toMonoidHom).toAdditive

variable {K : Type*} [CommRing K] [ValuativeRel K]

lemma ker_v_def (r : 𝒪[K]ˣ) :
  ker_v K (.ofMul r) = .ofMul (Units.map (𝒪[K].subtype).toMonoidHom r) := rfl

lemma ker_v_injective : (ker_v K : Additive (𝒪[K]ˣ) → Additive Kˣ).Injective := by
  intro a b h
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
  obtain ⟨b, rfl⟩ := Additive.ofMul.surjective b
  exact Units.map_injective ((Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a) h

end ValuativeRel

namespace IsNonarchimedeanLocalField

section valuation

open ValuativeRel

open scoped WithZero

/--
The ℤᵐ⁰-valued valuation on a nonarchimedean local field. Note that it sends
a uniformiser to `.exp (-1)`.
-/
noncomputable def v₀ {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : K →*₀ ℤᵐ⁰ :=
  (valueGroupWithZeroIsoInt K : ValueGroupWithZero K →*₀ ℤᵐ⁰).comp
  (ValuativeRel.valuation K : K →*₀ ValueGroupWithZero K)

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

lemma v₀_uniformiser {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    v₀ (ϖ : K) = .exp (-1) :=
  valueGroupWithZeroIsoInt_irreducible hϖ

/--
The valuation on the units of a nonarch local field. Domain is actually
`Additive Kˣ` so that it can be an additive group homomorphism to ℤ.
Normalised so that it sends a uniformiser to +1.
-/
noncomputable def v (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Additive Kˣ →+ ℤ :=
  let f₃ : Kˣ →* (ℤᵐ⁰)ˣ := Units.map (v₀.toMonoidHom : K →* ℤᵐ⁰)
  -- here we introduce the sign
  let f₄ : (ℤᵐ⁰)ˣ →* Multiplicative ℤ := (WithZero.unitsWithZeroEquiv.toMonoidHom)⁻¹
  (f₄.comp f₃).toAdditiveLeft

lemma v_def (x : Kˣ) : Multiplicative.ofAdd (v K (.ofMul x)) = v₀ (x⁻¹ : K) := by
  simp [v, v₀]

lemma v_uniformiser {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    v K (.ofMul <| Units.mk0 (ϖ : K) hϖ.ne_zero') = 1 := by
  apply Multiplicative.ofAdd.injective
  apply WithZero.coe_injective
  simp [v_def, v₀_uniformiser hϖ, WithZero.exp]

lemma v_surjective : (v K : Additive Kˣ → ℤ).Surjective := by
  intro n
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible (𝒪[K])
  let ϖ : Kˣ := Units.mk0 (ϖ₀ : K) hϖ₀.ne_zero'
  use n • (.ofMul ϖ)
  simp [v_uniformiser hϖ₀, ϖ]

lemma v_eq_zero_iff (x : Kˣ) : v K (.ofMul x) = 0 ↔ valuation K x = 1 := by
  rw [← Multiplicative.ofAdd.apply_eq_iff_eq, ← WithZero.coe_inj]
  simp [v_def, v₀]

lemma ker_v_ker : Function.Exact (ker_v K) (v K) := by
  intro x
  obtain ⟨k, rfl⟩ := Additive.ofMul.surjective x
  rw [v_eq_zero_iff, valuation_eq_one_iff]
  simp only [Set.mem_range, Additive.exists, ker_v_def, Additive.ofMul.apply_eq_iff_eq]
  apply exists_congr (fun r ↦ ?_)
  rw [← Units.val_inj]
  simp [Eq.comm]

end valuation

end IsNonarchimedeanLocalField
