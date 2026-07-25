/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Chris Birback
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-! # `ℚ_[p]` is a nonarchimedean local field

`IsNonarchimedeanLocalField K` extends `IsValuativeTopology K`, `LocallyCompactSpace K` and
`ValuativeRel.IsNontrivial K`. For `K = ℚ_[p]` the last two are already instances in Mathlib, so
the only missing ingredient is `IsValuativeTopology ℚ_[p]`: the norm topology on `ℚ_[p]` agrees
with the topology of its canonical valuation. We prove this via `IsValuativeTopology.of_zero`,
comparing valuation balls with norm balls through the dictionary
`‖x‖ = p ^ log (Padic.mulValuation x)`.
-/

@[expose] public section

open ValuativeRel Filter Metric Set

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- Strict comparison of `Padic.mulValuation` matches strict comparison of the norm. -/
lemma mulValuation_lt_iff_norm_lt {z a : ℚ_[p]} :
    mulValuation z < mulValuation a ↔ ‖z‖ < ‖a‖ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [map_zero, norm_zero]
    exact iff_of_false (not_lt.mpr zero_le) (not_lt.mpr (norm_nonneg _))
  rcases eq_or_ne z 0 with rfl | hz
  · simp [pos_iff_ne_zero, norm_pos_iff, ha]
  · have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    rw [norm_eq_zpow_log_mulValuation hz, norm_eq_zpow_log_mulValuation ha,
      zpow_lt_zpow_iff_right₀ hp1,
      WithZero.log_lt_log ((mulValuation (p := p)).zero_iff.not.mpr hz)
        ((mulValuation (p := p)).zero_iff.not.mpr ha)]

/-- Strict comparison of the canonical `ValuativeRel` valuation on `ℚ_[p]` matches strict
comparison of the norm. -/
lemma valuation_lt_iff_norm_lt {z a : ℚ_[p]} :
    ValuativeRel.valuation ℚ_[p] z < ValuativeRel.valuation ℚ_[p] a ↔ ‖z‖ < ‖a‖ := by
  rw [← mulValuation_lt_iff_norm_lt, ← Padic.mulValuation.vlt_iff_lt,
    ← (ValuativeRel.valuation ℚ_[p]).vlt_iff_lt]

lemma valuation_ball_eq_norm_ball (a : ℚ_[p]) : {z | (ValuativeRel.valuation ℚ_[p]) z <
    ValuativeRel.valuation ℚ_[p] a} = Metric.ball 0 ‖a‖ := by
  ext z
  simp [valuation_lt_iff_norm_lt]

/-- The norm topology on `ℚ_[p]` is the valuative topology of its canonical valuation. -/
instance : IsValuativeTopology ℚ_[p] := by
  refine .of_zero fun s ↦ ⟨fun hs ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · -- a valuation ball fits inside any norm neighbourhood of `0`
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨a, ha0, haε⟩ := NormedField.exists_norm_lt ℚ_[p] hε
    exact ⟨Units.mk0 (ValuativeRel.valuation ℚ_[p] a) (by simp [norm_pos_iff.mp ha0]),
      fun z hz ↦ hεs <| mem_ball_zero_iff.2 ((valuation_lt_iff_norm_lt.1 hz).trans haε)⟩
  · -- conversely each valuation ball is a norm ball `ball 0 ‖a‖`, hence a neighbourhood of `0`
    obtain ⟨a, ha⟩ := valuation_surjective (γ : ValueGroupWithZero ℚ_[p])
    have ha0 : a ≠ 0 := by rintro rfl; exact γ.ne_zero (ha.symm.trans (map_zero _))
    refine mem_of_superset ?_ hγ
    simpa [← ha, valuation_ball_eq_norm_ball] using Metric.ball_mem_nhds _ (norm_pos_iff.mpr ha0)

/-- The field of `p`-adic numbers is a nonarchimedean local field. -/
instance : IsNonarchimedeanLocalField ℚ_[p] where

end Padic
