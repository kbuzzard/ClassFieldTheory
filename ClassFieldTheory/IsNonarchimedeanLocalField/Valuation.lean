/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import ClassFieldTheory.Cohomology.Functors.Restriction
import ClassFieldTheory.IsNonarchimedeanLocalField.Basic
import ClassFieldTheory.Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.FieldTheory.Galois.IsGaloisGroup
/-

# 1 → 𝒪[K]ˣ → Kˣ → ℤ → 0

We construct the short exact sequence `0 → Additive 𝒪[K]ˣ → Additive (Kˣ) → ℤ → 0` in
the following sense: we define the maps `kerV K` and `v K`, prove the first is
injective, the second is surjective, and the pair is `Function.Exact`.

-/

namespace ValuativeRel

def kerV (K : Type*) [CommRing K] [ValuativeRel K] : Additive 𝒪[K]ˣ →+ Additive Kˣ :=
  (Units.map 𝒪[K].subtype).toAdditive

variable {K : Type*} [CommRing K] [ValuativeRel K]

@[simp] lemma kerV_apply (r : 𝒪[K]ˣ) :
    kerV K (.ofMul r) = .ofMul (Units.map (𝒪[K].subtype).toMonoidHom r) := rfl

lemma kerV_injective : (⇑(kerV K)).Injective :=
  Units.map_injective Subtype.val_injective

end ValuativeRel

namespace IsNonarchimedeanLocalField

section valuation

open ValuativeRel

open scoped WithZero

/--
The `ℤᵐ⁰`-valued valuation on a nonarchimedean local field. Note that it sends
a uniformiser to `.exp (-1)`.
-/
noncomputable def valuationInt (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Valuation K ℤᵐ⁰ :=
  (valuation K).map (valueGroupWithZeroIsoInt K) <| OrderHomClass.mono <| valueGroupWithZeroIsoInt K

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

-- move
theorem _root_.OrderIsoClass.strict_mono {α β F : Type*} [Preorder α] [Preorder β]
    [EquivLike F α β] [OrderIsoClass F α β] (f : F) : StrictMono f := fun x y ↦
  by simp [lt_iff_le_not_ge]

instance : (valuationInt K).Compatible :=
  Valuation.compatible_map _ <| OrderIsoClass.strict_mono _

lemma valuationInt_uniformiser {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuationInt K ϖ = .exp (-1) :=
  valueGroupWithZeroIsoInt_irreducible hϖ

/--
The valuation on the units of a nonarch local field. Domain is actually
`Additive Kˣ` so that it can be an additive group homomorphism to ℤ.
Normalised so that it sends a uniformiser to +1.
-/
noncomputable def v (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Additive Kˣ →+ ℤ :=
  let f₃ : Kˣ →* (ℤᵐ⁰)ˣ := Units.map (valuationInt K)
  -- here we introduce the sign
  let f₄ : (ℤᵐ⁰)ˣ →* Multiplicative ℤ := (WithZero.unitsWithZeroEquiv.toMonoidHom)⁻¹
  (f₄.comp f₃).toAdditiveLeft

@[simp] lemma v_apply (x : Additive Kˣ) : v K x = -(valuationInt K x.toMul).log := by
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
  rw [toMul_ofMul]
  generalize hy : valuationInt K x = y
  cases y using WithZero.expRecOn with
  | zero => simp at hy
  | exp y => simp [v, hy]

lemma v_uniformiser {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    v K (.ofMul <| Units.mk0 (ϖ : K) hϖ.ne_zero') = 1 := by
  simp [valuationInt_uniformiser hϖ]

lemma v_surjective : (v K : Additive Kˣ → ℤ).Surjective := by
  intro n
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  use n • .ofMul (.mk0 (ϖ₀ : K) hϖ₀.ne_zero')
  simp [valuationInt_uniformiser hϖ₀]

-- move
@[simp] lemma _root_.WithZero.log_eq_zero_iff {α : Type*} [AddMonoid α] {x : αᵐ⁰} :
    x.log = 0 ↔ x = 0 ∨ x = 1 := by
  cases x using WithZero.expRecOn with
  | zero => simp
  | exp x => simp

lemma v_eq_zero_iff (x : Kˣ) : v K (.ofMul x) = 0 ↔ valuation K x = 1 := by
  simpa using (ValuativeRel.isEquiv _ _).eq_one_iff_eq_one

lemma exact_kerV_v : Function.Exact (kerV K) (v K) := by
  intro x
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
  rw [v_eq_zero_iff, valuation_eq_one_iff]
  simp [Units.ext_iff]

end valuation

end IsNonarchimedeanLocalField
