/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ClassFieldTheory.IsNonarchimedeanLocalField.Basic

/-! # Basic facts about e and f and unramified

todo: totally ramified
-/

namespace IsNonarchimedeanLocalField
variable (K L L₁ L₂ F : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K L] [Algebra K L₁] [Algebra K L₂] [Algebra L F] [Algebra K F]
  [ValuativeExtension K L] [ValuativeExtension K L₁] [ValuativeExtension K L₂]
  [ValuativeExtension L F] [ValuativeExtension K F]
  [IsScalarTower K L F]

open ValuativeRel

-- move
instance : IsScalarTower 𝒪[K] 𝒪[L] 𝒪[F] :=
  .of_algebraMap_eq fun x ↦ Subtype.ext <| IsScalarTower.algebraMap_apply K L F x

-- move
instance : IsScalarTower 𝓀[K] 𝓀[L] 𝓀[F] :=
  .of_algebraMap_eq fun x ↦ (Ideal.Quotient.mk_surjective x).elim fun x hx ↦
    hx ▸ congr(IsLocalRing.residue _ $(IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[L] 𝒪[F] x))

theorem f_mul_f : f K L * f L F = f K F :=
  by simp [← f_spec, Module.finrank_mul_finrank]

theorem f_dvd_f_bot : f L F ∣ f K F :=
  f_mul_f K L F ▸ dvd_mul_left ..

theorem f_dvd_f_top : f K L ∣ f K F :=
  f_mul_f K L F ▸ dvd_mul_right ..

theorem e_mul_e : e K L * e L F = e K F := by
  refine mul_right_cancel₀ (mul_ne_zero (f_pos K L).ne' (f_pos L F).ne') ?_
  rw [mul_mul_mul_comm, e_mul_f_eq_n, e_mul_f_eq_n, f_mul_f, e_mul_f_eq_n,
    Module.finrank_mul_finrank]

theorem e_dvd_e_bot : e L F ∣ e K F :=
  e_mul_e K L F ▸ dvd_mul_left ..

theorem e_dvd_e_top : e K L ∣ e K F :=
  e_mul_e K L F ▸ dvd_mul_right ..

variable {K L L₁ L₂}

theorem e_dvd_e (φ : L₁ →ₐ[K] L₂) : e K L₁ ∣ e K L₂ := by
  algebraize [φ.toRingHom]
  have : ValuativeExtension L₁ L₂ := sorry -- ask andrew
  exact e_dvd_e_top ..

theorem f_dvd_f (φ : L₁ →ₐ[K] L₂) : f K L₁ ∣ f K L₂ := by
  algebraize [φ.toRingHom]
  have : ValuativeExtension L₁ L₂ := sorry -- ask andrew
  exact f_dvd_f_top ..

theorem e_congr (φ : L₁ ≃ₐ[K] L₂) : e K L₁ = e K L₂ :=
  dvd_antisymm (e_dvd_e φ) (e_dvd_e φ.symm)

theorem f_congr (φ : L₁ ≃ₐ[K] L₂) : f K L₁ = f K L₂ :=
  dvd_antisymm (f_dvd_f φ) (f_dvd_f φ.symm)

theorem IsUnramified.ofAlgEquiv (φ : L₁ ≃ₐ[K] L₂) [IsUnramified K L₁] : IsUnramified K L₂ :=
  ⟨by rw [← e_congr φ, e_eq_one]⟩

-- move
instance (R : Type*) [CommRing R] {σ : Type*} [SetLike σ R] [SubringClass σ R] (s : σ)
    [ValuativeRel R] : ValuativeRel s :=
  .ofValuation <| (valuation R).comap <| (Subring.ofClass s).subtype

-- move
@[simp] theorem subtype_rel
    (R : Type*) [CommRing R] {σ : Type*} [SetLike σ R] [SubringClass σ R] (s : σ)
    [ValuativeRel R] (x y : s) : x ≤ᵥ y ↔ x.val ≤ᵥ y.val :=
  (Valuation.Compatible.rel_iff_le (v := valuation R) ..).symm

-- move
instance (R : Type*) [CommRing R] {σ : Type*} [SetLike σ R] [SubringClass σ R] (s : σ) :
    Algebra s R :=
  (Subring.ofClass s).subtype.toAlgebra

-- move
@[simp] theorem SubringClass.coe_algebraMap  (R : Type*) [CommRing R] {σ : Type*}
    [SetLike σ R] [SubringClass σ R] (s : σ) : ⇑(algebraMap s R) = Subtype.val := rfl

-- move
instance (R : Type*) [CommRing R] {σ : Type*} [SetLike σ R] [SubringClass σ R] (s : σ)
    [ValuativeRel R] : ValuativeExtension s R where
  rel_iff_rel _ _ := by simp

-- todo
instance (K L : Type*)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [ValuativeExtension K L]
    (E : IntermediateField K L) : IsNonarchimedeanLocalField E := sorry

-- move
instance (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [ValuativeRel A] [ValuativeRel B] [ValuativeExtension A B]
    {σ : Type*} [SetLike σ B] [SubringClass σ B] [SMulMemClass σ A B] (s : σ) :
    ValuativeExtension A s :=
  ⟨by simp [ValuativeExtension.rel_iff_rel]⟩

theorem InUnramified.intermediateField [IsUnramified K L] (E : IntermediateField K L) :
    IsUnramified K E :=
  ⟨Nat.dvd_one.mp <| IsUnramified.e_eq_one (K := K) (L := L) ▸ e_dvd_e (Algebra.algHom ..)⟩

@[simp] theorem e_fieldRange (φ : L₁ →ₐ[K] L₂) : e K φ.fieldRange = e K L₁ :=
  e_congr <| (AlgEquiv.ofInjective _ φ.toRingHom.injective).symm

@[simp] theorem f_fieldRange (φ : L₁ →ₐ[K] L₂) : f K φ.fieldRange = f K L₁ :=
  f_congr <| (AlgEquiv.ofInjective _ φ.toRingHom.injective).symm

instance [IsUnramified K L₁] (φ : L₁ →ₐ[K] L₂) : IsUnramified K φ.fieldRange := ⟨by simp⟩

theorem IsUnramified.comap [IsUnramified K L₂] (φ : L₁ →ₐ[K] L₂) : IsUnramified K L₁ :=
  ⟨Nat.dvd_one.mp <| e_eq_one K L₂ ▸ e_dvd_e φ⟩

variable (K L)

theorem IsUnramified.of_tower_top [IsUnramified K F] : IsUnramified K L :=
  ⟨Nat.dvd_one.mp <| e_eq_one K F ▸ e_dvd_e_top ..⟩

theorem IsUnramified.of_tower_bot [IsUnramified K F] : IsUnramified L F :=
  ⟨Nat.dvd_one.mp <| e_eq_one K F ▸ e_dvd_e_bot ..⟩

theorem IsUnramified.trans [IsUnramified K L] [IsUnramified L F] : IsUnramified K F :=
  ⟨by simp [← e_mul_e K L F]⟩

theorem IsUnramified.n_eq_f [IsUnramified K L] : Module.finrank K L = f K L := by
  simp [← e_mul_f_eq_n]

theorem IsUnramified.n_dvd_f [IsUnramified K L] : Module.finrank K L ∣ f K L := by
  simp [← e_mul_f_eq_n]

end IsNonarchimedeanLocalField
