import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

namespace ValuativeRel

section Ring

variable {R : Type*} [CommRing R]

attribute [ext] ValuativeRel

variable [ValuativeRel R]

theorem posSubmonoid.ne_zero (x : posSubmonoid R) : x.val ≠ 0 :=
  mt (· ▸ vle_rfl) x.2

instance _root_.Valuation.compatible_map {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommMonoidWithZero Γ₀] {v : Valuation R Γ₀} [ValuativeRel R]
    {Γ₁ : Type*} [LinearOrderedCommMonoidWithZero Γ₁] (f : Γ₀ →*₀ Γ₁) (hf : StrictMono f)
    [v.Compatible] : (v.map f hf.monotone).Compatible :=
  ⟨fun _ _ ↦ (Valuation.Compatible.vle_iff_le (v := v) _ _).trans hf.le_iff_le.symm⟩

end Ring


section Field

variable {F : Type*} [Field F] [ValuativeRel F]

theorem vle_iff_div_vle_one (x : F) {y : F} (hy : y ≠ 0) :
    x ≤ᵥ y ↔ x / y ≤ᵥ 1 := by
  rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F),
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F),
    map_div₀, map_one, div_le_one₀ (bot_lt_iff_ne_bot.2 ((map_ne_zero _).2 hy))]

/-- Two valuative relations on a field are equal iff their rings of integers are equal. -/
@[ext high] theorem ext_of_field {F : Type*} [Field F] {v v' : ValuativeRel F}
    (h : ∀ x, v.vle x 1 ↔ v'.vle x 1) : v = v' := by
  ext x y
  by_cases hy : y = 0
  · simp_rw [hy, vle_zero_iff]
  · rw [vle_iff_div_vle_one _ hy, @vle_iff_div_vle_one _ _ v x y hy, h]

theorem unitsMap_valuation_surjective :
    Function.Surjective (Units.map (valuation F : F →* ValueGroupWithZero F)) :=
  fun γ ↦ let ⟨x, hx⟩ := valuation_surjective γ.val
  ⟨Units.mk0 x (mt (by rw [← hx, ·, map_zero]) γ.ne_zero),
    Units.ext <| by simpa using hx⟩

end Field

end ValuativeRel


namespace ValuativeExtension

open ValuativeRel

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [ValuativeRel A] [ValuativeRel B] [ValuativeRel C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [ValuativeExtension A B] {a b : A}

instance : ValuativeExtension A A where
  vle_iff_vle _ _ := .rfl

variable (A B C) in
theorem trans [ValuativeExtension B C] : ValuativeExtension A C where
  vle_iff_vle _ _ := by simp_rw [Algebra.algebraMap_eq_smul_one, ← map_one (algebraMap B C),
    Algebra.algebraMap_eq_smul_one, ← IsScalarTower.smul_assoc, ← Algebra.algebraMap_eq_smul_one,
    vle_iff_vle]

lemma algebraMap_le : valuation B (algebraMap A B a) ≤ valuation B (algebraMap A B b) ↔
    valuation A a ≤ valuation A b := by
  simp_rw [← Valuation.Compatible.vle_iff_le, vle_iff_vle]

lemma algebraMap_eq : valuation B (algebraMap A B a) = valuation B (algebraMap A B b) ↔
    valuation A a = valuation A b := by
  simp_rw [le_antisymm_iff, algebraMap_le]

lemma algebraMap_lt : valuation B (algebraMap A B a) < valuation B (algebraMap A B b) ↔
    valuation A a < valuation A b := by
  simp_rw [lt_iff_le_not_ge, algebraMap_le]

end ValuativeExtension


namespace ValuativeRel

instance (R : Type*) [CommRing R] {σ : Type*} [SetLike σ R] [SubringClass σ R] (s : σ)
    [ValuativeRel R] : ValuativeRel s where
  vle x y := x.val ≤ᵥ y.val
  vle_total x y := vle_total x.1 y.1
  vle_trans := vle_trans (R := R)
  vle_add := vle_add
  mul_vle_mul_left hxy z := mul_vle_mul_left hxy z.1
  vle_mul_cancel := vle_mul_cancel
  not_vle_one_zero := not_vle_one_zero

instance (R : Type*) [CommRing R] {σ : Type*} [SetLike σ R] [SubringClass σ R] (s : σ)
    [ValuativeRel R] : ValuativeExtension s R where
  vle_iff_vle _ _ := Iff.rfl

variable {R : Type*} [CommRing R] {σ : Type*} [SetLike σ R] [SubringClass σ R] {s : σ}
variable [ValuativeRel R]

@[simp] theorem subringclassRel_eq (x y : s) : (x ≤ᵥ y) = (x.val ≤ᵥ y.val) := rfl

theorem subringclassRel_iff (x y : s) : x ≤ᵥ y ↔ x.val ≤ᵥ y.val := Iff.rfl

instance (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [ValuativeRel A] [ValuativeRel B] [ValuativeExtension A B]
    {σ : Type*} [SetLike σ B] [SubringClass σ B] [SMulMemClass σ A B] (s : σ) :
    ValuativeExtension A s :=
  ⟨by simp [ValuativeExtension.vle_iff_vle]⟩

end ValuativeRel
