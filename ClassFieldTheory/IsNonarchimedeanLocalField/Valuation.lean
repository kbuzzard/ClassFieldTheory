/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import ClassFieldTheory.Cohomology.Functors.Restriction
import ClassFieldTheory.IsNonarchimedeanLocalField.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
/-

# 1 → 𝒪[L]ˣ → Lˣ → ℤ → 0

We construct the short exact sequence `1 → 𝒪[L]ˣ → Lˣ → ℤ → 0` in Rep ℤ G.

-/

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
  let f₁ : K →*₀ ValueGroupWithZero K := ValuativeRel.valuation K
  let f₂ : ValueGroupWithZero K →*₀ ℤᵐ⁰ := valueGroupWithZeroIsoInt K
  f₂.comp f₁

/--
The valuation on the units of a nonarch local field. Taking values in
`Multiplicative ℤ` so it can be a group homomorphism between multiplicative
groups. Note that it sends a uniformiser to +1.
-/
noncomputable def v {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative ℤ :=
  let f₃ : Kˣ →* (ℤᵐ⁰)ˣ := Units.map (v₀.toMonoidHom : K →* ℤᵐ⁰)
  -- here we introduce the sign
  let f₄ : (ℤᵐ⁰)ˣ →* Multiplicative ℤ := (WithZero.unitsWithZeroEquiv.toMonoidHom)⁻¹
  f₄.comp f₃

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

lemma v_def (x : Kˣ) : v x = v₀ (x⁻¹ : K) := by
  simp [v, v₀]

lemma v₀_uniformiser {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    v₀ (ϖ : K) = .exp (-1) :=
  valueGroupWithZeroIsoInt_irreducible hϖ

lemma v_uniformiser {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    v (Units.mk0 (ϖ : K) hϖ.ne_zero') = .ofAdd 1 := by
  apply WithZero.coe_injective
  simp [v_def, v₀_uniformiser hϖ, WithZero.exp]

lemma v_surjective : Function.Surjective (v : Kˣ → Multiplicative ℤ) := by
  intro n
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible (𝒪[K])
  let ϖ : Kˣ := Units.mk0 (ϖ₀ : K) hϖ₀.ne_zero'
  use ϖ ^ n.toAdd
  ext
  simp [v_uniformiser hϖ₀, ϖ]

lemma v_ker : v.ker = 𝒪[K].toSubmonoid.units := by
  ext x
  have hx : (x : K) ≠ 0 := x.ne_zero
  rw [MonoidHom.mem_ker, ← WithZero.coe_inj, v_def]
  simp only [map_inv₀, WithZero.coe_one, inv_eq_one]
  simp [v₀]
  /-
  x : Kˣ
  ⊢ (valuation K) ↑x = 1 ↔ x ∈ 𝒪[K].units
  -/
  sorry

noncomputable def vₐ : Additive Kˣ →+ ℤ := (v : Kˣ →* Multiplicative ℤ).toAdditiveLeft

end valuation

section short_exact_sequence

variable (G K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L]
    [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]

open CategoryTheory

open scoped ValuativeRel

noncomputable def valuationShortComplex : ShortComplex (Rep ℤ G) where
  X₁ := (Rep.res <|
          -- restrict along `G ≃* (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]`
          (IsGaloisGroup.mulEquivAlgEquiv G K L).trans (galRestrict 𝒪[K] K L 𝒪[L])).obj <|
        -- Gal(L/K)-module Lˣ
        Rep.ofAlgebraAutOnUnits 𝒪[K] 𝒪[L]
        -- restrict along an isomorphism
  X₂ := (Rep.res <|
          -- G ≃* Gal(L/K)
          IsGaloisGroup.mulEquivAlgEquiv G K L).obj <|
        -- Gal(L/K)-module Lˣ
        Rep.ofAlgebraAutOnUnits K L
  X₃ := .trivial ℤ G ℤ
  f := {
    hom := ModuleCat.ofHom (Units.map 𝒪[L].subtype : 𝒪[L]ˣ →* Lˣ).toAdditive.toIntLinearMap
    comm g := sorry -- should be easy (surprised it's not rfl)
  }
  g := {
    hom := ModuleCat.ofHom (vₐ : (Additive Lˣ) →+ ℤ).toIntLinearMap
    comm := sorry -- has some content, see https://leanprover.zulipchat.com/#narrow/channel/516717-Oxford-Class-Field-Theory-2025-workshop/topic/valuation.20exact.20sequence.20for.20herbrand.20quotient/near/554423613
  }
  zero := sorry -- v(𝒪[L]ˣ) = 0

-- first map monic should be easy, second map epi should be `IsNonarchimedeanLocalField.v_surjective`
-- and exactness in the middle should be v(x)=0 => x is a unit
lemma valuationShortComplex.shortExact : (valuationShortComplex G K L).ShortExact := sorry

end short_exact_sequence
