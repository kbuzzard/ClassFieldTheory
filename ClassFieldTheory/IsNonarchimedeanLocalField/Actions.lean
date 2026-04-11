module

public import ClassFieldTheory.IsNonarchimedeanLocalField.Basic
public import ClassFieldTheory.Mathlib.Topology.Algebra.Valued.ValuativeRel

/-! # Actions on local fields

If `L/K` is an extension of local fields then `Gal(L/K)` preserves the valuation.

This is a sorry-free version of `Instances.lean`.
-/

public section

namespace IsNonarchimedeanLocalField

variable {K L : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

open ValuativeRel

-- variable (K L) in
-- /-- `𝒪[L]` as an `𝒪[K]`-subalgebra of `L`. -/
-- def subalgebra : Subalgebra 𝒪[K] L where
--   __ := 𝒪[L]
--   algebraMap_mem' x := (algebraMap 𝒪[K] 𝒪[L] x).2

-- move
@[simp] lemma _root_.Units.coe_inv₀ {F σ : Type*} [GroupWithZero F] [SetLike σ F]
    [SubmonoidClass σ F] {s : σ} {x : sˣ} : ((x⁻¹ :) : F) = (x : F)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv₀ (by exact (x.map (SubmonoidClass.subtype s)).ne_zero),
    ← MulMemClass.coe_mul, x.inv_mul, OneMemClass.coe_one]

-- move
-- generality: DVR as ValuationSubring (note: `𝒪[K] : Subring K`)
theorem exists_units_mul_irreducible_zpow {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃ (u : 𝒪[K]ˣ) (n : ℤ), u * ϖ ^ n = x := by
  obtain h | h := (valuation K).valuationSubring.mem_or_inv_mem x
  · lift x to 𝒪[K] using h
    replace hx : x ≠ 0 := by aesop
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    exact ⟨u, n, by simp⟩
  · rw [← inv_inv x] at hx ⊢
    generalize x⁻¹ = x at *
    lift x to 𝒪[K] using h
    replace hx : x ≠ 0 := by aesop
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    exact ⟨u⁻¹, -n, by simp [mul_comm]⟩

@[simp] theorem valuation_algEquiv_apply {g : L ≃ₐ[K] L} {x : L} :
    valuation L (g x) = valuation L x := by
  have h₁ {g : L ≃ₐ[K] L} : ↑𝒪[L] ⊆ g⁻¹' 𝒪[L] := fun x hx ↦ by
    simp only [SetLike.mem_coe, Valuation.mem_integer_iff, ← isIntegral_iff (K := K),
      Set.mem_preimage] at hx ⊢
    exact hx.map g
  have h₂ : 𝒪[L].map g = 𝒪[L] :=
    le_antisymm (Subring.map_le_iff_le_comap.mpr h₁) <| by
      erw [Subring.map_equiv_eq_comap_symm g.toRingEquiv]
      exact h₁ (g := g.symm)
  let g' : 𝒪[L] ≃+* 𝒪[L] := g.subringMap |>.trans <| RingEquiv.subringCongr h₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hgϖ := hϖ.map g'
  obtain rfl | hx := eq_or_ne x 0
  · simp
  obtain ⟨u, n, rfl⟩ := exists_units_mul_irreducible_zpow hϖ hx
  rw [map_mul]
  change valuation L (u.map g'.toMonoidHom * _) = _
  rw [map_mul, valuation_units_integer_eq_one]
  simp [valuation_irreducible hϖ, show valuation L (g ϖ) = _ from valuation_irreducible hgϖ]

@[simp] theorem valuation_algHom_apply {g : L →ₐ[K] L} {x : L} :
    valuation L (g x) = valuation L x :=
  valuation_algEquiv_apply (g := .ofBijective g g.bijective)

variable (K) in
theorem valuation_smul {M : Type*} [Monoid M] [MulSemiringAction M L] [SMulCommClass M K L]
    {g : M} {x : L} : valuation L (g • x) = valuation L x :=
  valuation_algHom_apply (g := MulSemiringAction.toAlgHom K L g)

-- `K` cannot be inferred
variable (K) in
theorem invariant {M : Type*} [Monoid M] [MulSemiringAction M L] [SMulCommClass M K L] :
    IsInvariantSubring M 𝒪[L] :=
  ⟨fun g x hx ↦ by simpa [Valuation.mem_integer_iff, valuation_smul K]⟩

instance : IsInvariantSubring (L ≃ₐ[K] L) 𝒪[L] := invariant K

noncomputable example {M : Type*} [Monoid M] [MulSemiringAction M L] [SMulCommClass M K L] :
    MulSemiringAction M 𝒪[L] :=
  have := invariant (M := M) K (L := L)
  inferInstance

end IsNonarchimedeanLocalField
