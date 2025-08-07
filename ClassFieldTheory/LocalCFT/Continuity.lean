import ClassFieldTheory.Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import ClassFieldTheory.Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField

open ValuativeRel

theorem Valuation.sum_eq_iSup {ι R Γ₀ : Type*} (f : ι → R) (s : Finset ι)
    [LinearOrderedCommMonoidWithZero Γ₀] [Ring R] (v : Valuation R Γ₀)
    (H : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v (f i) ≠ 0 → v (f j) ≠ 0 → v (f i) ≠ v (f j)) :
    v (∑ i ∈ s, f i) = s.sup (v ∘ f) := by
  classical
  induction s using Finset.induction with
  | empty => simp [bot_eq_zero'']
  | insert a s has IH =>
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    replace IH := IH fun i his j hjs ↦ H i (by simp [his]) j (by simp [hjs])
    simp only [has, not_false_eq_true, Finset.sum_insert, Finset.sup_insert, ← IH,
      Function.comp_apply]
    obtain H₁ | H₁ := eq_or_ne (v (f a)) 0 <;> obtain H₂ | H₂ := eq_or_ne (v (∑ i ∈ s, f i)) 0
    · simp only [H₁, H₂, max_self]
      rw [← le_zero_iff]
      exact Valuation.map_add_le _ (by simp [H₁]) (by simp [H₂])
    · rw [Valuation.map_add_eq_of_lt_right, max_eq_right]
      · rw [H₁]; exact zero_le'
      · rwa [H₁, zero_lt_iff]
    · rw [Valuation.map_add_eq_of_lt_left, max_eq_left]
      · rw [H₂]; exact zero_le'
      · rwa [H₂, zero_lt_iff]
    rw [v.map_add_of_distinct_val]
    obtain ⟨i, his : i ∈ s, hi : v (f i) = _⟩ := Finset.sup_mem_of_nonempty (f := v ∘ f) hs
    rw [IH, ← hi]
    exact H _ (by simp) _ (by simp [his]) (has <| · ▸ his) (by simp [H₁]) (by simp [hi, ← IH, H₂])

/-- Andrew's Lemma : Density for algebraic extensions. -/
theorem exists_valuation_algebraMap_eq_valuation_pow
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel L]
    [Algebra.IsAlgebraic K L] (y : L) :
    ∃ x n, n ≠ 0 ∧ valuation L (algebraMap K L x) = valuation L y ^ n := by
  by_cases hy : y = 0
  · use 0, 1, one_ne_zero
    simp [hy]
  by_contra! H
  have := congr(valuation L $(minpoly.aeval K y))
  rw [Polynomial.aeval_eq_sum_range, Valuation.sum_eq_iSup] at this; swap
  · simp only [Finset.mem_range, Nat.lt_succ, ne_eq, map_eq_zero, smul_eq_zero, pow_eq_zero_iff',
      hy, false_and, or_false]
    intros i hi j hj hij hi' hj' e
    wlog hij' : i ≤ j generalizing i j
    · exact this j hj i hi (Ne.symm hij) hj' hi' e.symm (by omega)
    obtain ⟨k, rfl⟩ := exists_add_of_le hij'
    simp [Algebra.smul_def] at e
    apply H ((minpoly K y).coeff i / (minpoly K y).coeff (i + k)) k (by simpa using hij)
    apply mul_left_injective₀ (b := (valuation L) y ^ i) (by simp [hy])
    simp [*, -mul_eq_mul_right_iff, div_mul_eq_mul_div, pow_add, mul_comm]
  · simp only [map_zero, ← bot_eq_zero'', Finset.sup_eq_bot_iff] at this
    simp only [Finset.mem_range, Function.comp_apply, bot_eq_zero'', map_eq_zero, smul_eq_zero,
      pow_eq_zero_iff', hy, ne_eq, false_and, or_false, Nat.lt_succ] at this
    exact minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral _) hy (this 0 (by simp))

lemma exists_valuation_algebraMap_le_valuation
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel L]
    [Algebra.IsAlgebraic K L] (y : Lˣ) :
    ∃ x : Kˣ, valuation L (algebraMap K L x) ≤ valuation L y.val := by
  obtain hy1 | h1y := le_total (valuation L y.val) 1
  · obtain ⟨x, n, hn, hxy⟩ := exists_valuation_algebraMap_eq_valuation_pow K y.val
    have hx0 : x ≠ 0 :=
      (y.ne_zero <| by rwa [·, map_zero, map_zero, eq_comm, pow_eq_zero_iff hn, map_eq_zero] at hxy)
    exact ⟨Units.mk0 x hx0, by rw [Units.val_mk0, hxy]; exact pow_le_of_le_one bot_le hy1 hn⟩
  · exact ⟨1, by rwa [Units.val_one, map_one, map_one]⟩

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]
  [IsTopologicalAddGroup K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsValuativeTopology L]
  [IsTopologicalAddGroup L]
  [Algebra K L] [Algebra.IsAlgebraic K L] [ValuativeExtension K L]

/-- Maddy's Lemma : Density implies continuity. -/
@[fun_prop] instance continuous_algebraMap_of_density :
    Continuous (algebraMap K L) := by
  apply continuous_of_continuousAt_zero _ _
  simp only [ContinuousAt, map_zero]
  have B₁ := IsValuativeTopology.hasBasis_nhds_zero K
  have B₂ := IsValuativeTopology.hasBasis_nhds_zero L
  apply (Filter.HasBasis.tendsto_iff B₁ B₂).mpr
  simp only [Set.mem_setOf_eq, true_and, true_imp_iff]
  intro b
  obtain ⟨a, rfl⟩ := unitsMap_valuation_surjective b
  obtain ⟨a', ha'⟩ := exists_valuation_algebraMap_le_valuation K a
  refine ⟨a'.map (valuation K), fun x hx ↦ ?_⟩
  simp only [Units.coe_map, MonoidHom.coe_coe] at hx ⊢
  exact lt_of_lt_of_le (ValuativeExtension.algebraMap_lt.mpr hx) ha'

instance : ContinuousSMul K L :=
  letI := IsTopologicalAddGroup.toUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  continuousSMul_of_algebraMap K L (continuous_algebraMap_of_density K L)
