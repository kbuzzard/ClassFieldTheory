import ClassFieldTheory.Mathlib.RingTheory.Valuation.Integers
import Mathlib.Topology.Algebra.Valued.ValuativeRel

open ValuativeRel

theorem le_valuation_irreducible_of_lt_one {K : Type*} [Field K] [ValuativeRel K]
    {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {x} (hx : x < 1) : x ≤ valuation K ϖ := by
  obtain ⟨x, rfl⟩ := valuation_surjective x
  lift x to 𝒪[K] using hx.le
  obtain h₁ | h₁ := ValuationRing.dvd_total x ϖ
  · obtain h₂ | h₂ := hϖ.dvd_iff.mp h₁
    · exact absurd ((Valuation.integer.integers (valuation K)).one_of_isUnit h₂) (ne_of_lt hx)
    · rw [(Valuation.integer.integers (valuation K)).associated_iff_eq] at h₂
      exact h₂.ge
  · exact (Valuation.integer.integers (valuation K)).le_of_dvd h₁

theorem valuation_map_irreducible_lt_one {K L : Type*} [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L]
    {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    valuation L (algebraMap K L ϖ) < 1 := by
  have : valuation K ϖ < 1 := Valuation.integer.v_irreducible_lt_one hϖ
  rw [← (valuation K).map_one, ← Valuation.srel_iff_lt] at this
  simpa using (Valuation.srel_iff_lt (v := valuation L)).mp <|
    (ValuativeExtension.srel_iff_srel (B := L) (ϖ : K) 1).mpr this

@[simp] lemma valuation_units_integer_eq_one {R : Type*} [CommRing R] [ValuativeRel R]
    (x : 𝒪[R]ˣ) : valuation R x = 1 := by
  refine le_antisymm x.1.2 ?_
  rw [← (valuation R).map_one, ← 𝒪[R].coe_one, ← x.mul_inv, Subring.coe_mul, map_mul]
  exact mul_le_of_le_one_right' x⁻¹.1.2

-- I only need it for IsNonarchimedeanLocalField but it should be true in this generality
lemma valuation_eq_one_iff (K : Type*) [Field K] [ValuativeRel K] (x : K) :
    valuation K x = 1 ↔ ∃ r : 𝒪[K]ˣ, r = x := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · lift x to 𝒪[K] using h.le
    replace h := (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr h
    lift x to 𝒪[K]ˣ using h
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    simp
