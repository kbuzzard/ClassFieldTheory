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
