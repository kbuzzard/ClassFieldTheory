import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.RingTheory.Valuation.Integers

lemma Valuation.Integers.associated_iff_eq {F Γ₀ O : Type*} [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation F Γ₀}
    [CommRing O] [Algebra O F] (hv : v.Integers O) {x y : O} :
    Associated x y ↔ v (algebraMap O F x) = v (algebraMap O F y) := by
  have := hv.hom_inj.isDomain
  rw [← dvd_dvd_iff_associated, le_antisymm_iff, hv.le_iff_dvd, hv.le_iff_dvd, and_comm]

@[simp] theorem Valuation.algebraMap_integer_coe {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) :
    ⇑(algebraMap v.integer R) = (↑) :=
  rfl
