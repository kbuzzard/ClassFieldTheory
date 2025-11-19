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

/-- Two valuative relations on a field are equal iff their rings of integers are equal. -/
@[ext high] theorem ext_of_field {F : Type*} [Field F] {v v' : ValuativeRel F}
    (h : ∀ x, v.Rel x 1 ↔ v'.Rel x 1) : v = v' := by
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

variable {A B : Type*} [CommRing A] [CommRing B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B] {a b : A}

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
