import ClassFieldTheory.Mathlib.RingTheory.Valuation.ValuativeRel
import Mathlib.Topology.Algebra.Valued.NormedValued

namespace NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

open ValuativeRel

variable (K)

/-- Given an ultrametric normed field, make a canonical `ValuativeRel` instance. This instance is
scoped to avoid instance looping. -/
def toValuativeRel : ValuativeRel K :=
  .ofValuation valuation
scoped [NormedField] attribute [instance] toValuativeRel

theorem compatible : valuation.Compatible (R := K) where
  rel_iff_le _ _ := Iff.rfl
scoped [NormedField] attribute [instance] compatible

/-- The `ValuativeRel.valuation K` coming from the `ValuativeRel` that comes from
`NormedField.valuation`, is equivalent to `NormedField.valuation` itself. -/
theorem isEquiv : (ValuativeRel.valuation K).IsEquiv valuation :=
  ValuativeRel.isEquiv _ _

variable {K}

@[simp] theorem ball_norm_eq (x : K) :
    Metric.ball 0 ‖x‖ = { y : K | valuation y < valuation x } := by
  ext y
  simp_rw [mem_ball_zero_iff, Set.mem_setOf_eq, valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm]

theorem valuation_ball_eq (x : K) :
    (valuation (K := K)).ball (valuation x) = Metric.ball 0 ‖x‖ := by
  ext; simp_rw [Valuation.mem_ball_iff, valuation_apply, ← NNReal.coe_lt_coe,
    coe_nnnorm, mem_ball_zero_iff]

variable (K) in
omit [IsUltrametricDist K] in
lemma trivial_or_non_trivial : (∀ x : K, x = 0 ∨ ‖x‖ = 1) ∨ (∃ x : K, 1 < ‖x‖) := by
  by_contra h
  push_neg at h
  obtain ⟨⟨x, hx0, hx1⟩, hk⟩ := h
  obtain hx1 | h1x := lt_or_gt_of_ne hx1
  · exact absurd (hk x⁻¹) (not_le_of_gt <| by rwa [norm_inv, one_lt_inv₀ (norm_pos_iff.2 hx0)])
  · exact not_lt_of_ge (hk x) h1x

theorem nhds_zero_basis_norm {K : Type*} [NormedField K] :
    (nhds 0).HasBasis (fun x : K ↦ 0 < ‖x‖) fun x ↦ Metric.ball (0 : K) ‖x‖ where
  mem_iff' s := by
    refine ⟨fun hs0 ↦ ?_, fun ⟨x, x_pos, hxs⟩ ↦ ?_⟩
    · obtain trivial | ⟨x, h1x⟩ := trivial_or_non_trivial K
      · refine ⟨1, by simp, fun y hy1 ↦ ?_⟩
        rw [(trivial y).resolve_right (ne_of_lt (by simpa using hy1))]
        exact mem_of_mem_nhds hs0
      · have hix1 : ‖x⁻¹‖ < 1 := norm_inv x ▸ inv_lt_one_of_one_lt₀ h1x
        have ix_pos : 0 < ‖x⁻¹‖ := norm_inv x ▸ inv_pos_of_pos (one_pos.trans h1x)
        rw [(Metric.nhds_basis_ball_pow ix_pos hix1).mem_iff] at hs0
        obtain ⟨n, -, hns⟩ := hs0
        refine ⟨(x⁻¹) ^ n, norm_pow x⁻¹ n ▸ pow_pos ix_pos n, by rwa [norm_pow]⟩
    · exact Metric.nhds_basis_ball.mem_iff.2 ⟨_, x_pos, fun y hy ↦ hxs (by simpa using hy)⟩

theorem _root_.DiscreteTopology.of_trivial_norm (trivial : ∀ x : K, x = 0 ∨ ‖x‖ = 1) :
    DiscreteTopology K :=
  DiscreteTopology.of_forall_le_norm one_pos fun x hx ↦ by rw [(trivial x).resolve_left hx]

theorem valuativeTopology (K : Type*) [NormedField K] [IsUltrametricDist K] :
    ValuativeTopology K :=
  .mk' valuation fun s ↦ by simp_rw [valuation_ball_eq, nhds_zero_basis_norm.mem_iff, norm_pos_iff]

theorem isNontrivial (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] :
    ValuativeRel.IsNontrivial K := by
  obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
  refine ⟨⟨ValuativeRel.valuation K x, ?_, ?_⟩⟩
  · rw [Valuation.ne_zero_iff]; exact norm_pos_iff.1 (one_pos.trans hx)
  · exact ne_of_gt <| by rwa [(isEquiv K).one_lt_iff_one_lt, valuation_apply,
      ← NNReal.coe_lt_coe, NNReal.coe_one, coe_nnnorm]

scoped [NormedField] attribute [instance] valuativeTopology isNontrivial
