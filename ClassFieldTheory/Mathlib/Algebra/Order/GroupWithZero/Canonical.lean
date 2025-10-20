import ClassFieldTheory.Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.GroupWithZero.Canonical

namespace WithZero

@[simp] lemma exp_lt_one_iff {M : Type*} [Preorder M] [Zero M] {x : M} :
    WithZero.exp x < 1 ↔ x < 0 :=
  WithZero.exp_lt_exp

/-- The characterisation of `exp (-1) : ℤᵐ⁰`. -/
theorem exp_neg_one_def {x : ℤᵐ⁰} :
    x = .exp (-1) ↔ x < 1 ∧ ∀ y < 1, y ≤ x := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl
    refine ⟨by decide, fun y hy ↦ y.expRecOn (by decide) (fun y hy ↦ ?_) hy⟩
    rw [exp_lt_one_iff] at hy
    rw [exp_le_exp]
    grind
  · cases x
    · exact absurd (h.2 (exp (-1)) (by decide)) (by decide)
    · refine le_antisymm ?_ (h.2 _ (by decide))
      rw [exp_lt_one_iff] at h
      rw [exp_le_exp]
      grind

end WithZero
