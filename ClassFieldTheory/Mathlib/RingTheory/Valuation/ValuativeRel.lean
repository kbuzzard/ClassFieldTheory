import ClassFieldTheory.Mathlib.Algebra.Algebra.Subalgebra.Basic
import ClassFieldTheory.Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

namespace ValuativeRel

section Ring

variable {R : Type*} [CommRing R]

attribute [ext] ValuativeRel

variable [ValuativeRel R]

theorem posSubmonoid.ne_zero (x : posSubmonoid R) : x.val ≠ 0 :=
  mt (· ▸ rel_rfl) x.2

instance _root_.Valuation.compatible_map {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommMonoidWithZero Γ₀] {v : Valuation R Γ₀} [ValuativeRel R]
    {Γ₁ : Type*} [LinearOrderedCommMonoidWithZero Γ₁] (f : Γ₀ →*₀ Γ₁) (hf : StrictMono f)
    [v.Compatible] : (v.map f hf.monotone).Compatible :=
  ⟨fun _ _ ↦ (Valuation.Compatible.rel_iff_le (v := v) _ _).trans hf.le_iff_le.symm⟩

end Ring


section Field

variable {F : Type*} [Field F] [ValuativeRel F]

theorem rel_iff_div_rel_one (x : F) {y : F} (hy : y ≠ 0) :
    x ≤ᵥ y ↔ x / y ≤ᵥ 1 := by
  rw [Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation F),
    Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation F),
    map_div₀, map_one, div_le_one₀ (bot_lt_iff_ne_bot.2 ((map_ne_zero _).2 hy))]

theorem rel_zero_iff (x : F) : x ≤ᵥ 0 ↔ x = 0 := by
  rw [Valuation.Compatible.rel_iff_le (v := valuation F), map_zero, le_zero_iff, map_eq_zero]

/-- Two valuative relations on a field are equal iff their rings of integers are equal. -/
@[ext high] theorem ext_of_field {F : Type*} [Field F] {v v' : ValuativeRel F}
    (h : ∀ x, v.rel x 1 ↔ v'.rel x 1) : v = v' := by
  ext x y
  by_cases hy : y = 0
  · simp_rw [hy, rel_zero_iff]
  · rw [rel_iff_div_rel_one _ hy, @rel_iff_div_rel_one _ _ v x y hy, h]

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

theorem trans [ValuativeExtension B C] : ValuativeExtension A C where
  rel_iff_rel _ _ := by simp_rw [Algebra.algebraMap_eq_smul_one, ← map_one (algebraMap B C),
    Algebra.algebraMap_eq_smul_one, ← IsScalarTower.smul_assoc, ← Algebra.algebraMap_eq_smul_one,
    rel_iff_rel]

lemma algebraMap_le : valuation B (algebraMap A B a) ≤ valuation B (algebraMap A B b) ↔
    valuation A a ≤ valuation A b := by
  simp_rw [← Valuation.Compatible.rel_iff_le, rel_iff_rel]

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
  rel x y := x.val ≤ᵥ y.val
  rel_total x y := rel_total x.1 y.1
  rel_trans := rel_trans (R := R)
  rel_add := rel_add
  rel_mul_right z := rel_mul_right z.1
  rel_mul_cancel := rel_mul_cancel
  not_rel_one_zero := not_rel_one_zero

instance (R : Type*) [CommRing R] {σ : Type*} [SetLike σ R] [SubringClass σ R] (s : σ)
    [ValuativeRel R] : ValuativeExtension s R where
  rel_iff_rel _ _ := Iff.rfl

variable {R : Type*} [CommRing R] {σ : Type*} [SetLike σ R] [SubringClass σ R] {s : σ}
variable [ValuativeRel R]

@[simp] theorem subringclassRel_eq (x y : s) : (x ≤ᵥ y) = (x.val ≤ᵥ y.val) := rfl

theorem subringclassRel_iff (x y : s) : x ≤ᵥ y ↔ x.val ≤ᵥ y.val := Iff.rfl

instance (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [ValuativeRel A] [ValuativeRel B] [ValuativeExtension A B]
    {σ : Type*} [SetLike σ B] [SubringClass σ B] [SMulMemClass σ A B] (s : σ) :
    ValuativeExtension A s :=
  ⟨by simp [ValuativeExtension.rel_iff_rel]⟩

end ValuativeRel
