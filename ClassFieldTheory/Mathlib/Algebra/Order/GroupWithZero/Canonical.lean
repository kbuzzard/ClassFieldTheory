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

theorem exp_le_exp' {M : Type*} [LE M] {x y : M} : exp x ≤ exp y ↔ x ≤ y := WithZero.coe_le_coe

@[simp] theorem exp_le_one_iff {M : Type*} [LE M] [Zero M] {x : M} : exp x ≤ 1 ↔ x ≤ 0 :=
  exp_zero' (M := M) ▸ exp_le_exp'

@[simp] theorem one_le_exp_iff {M : Type*} [LE M] [Zero M] {x : M} : 1 ≤ exp x ↔ 0 ≤ x :=
  exp_zero' (M := M) ▸ exp_le_exp'

theorem lt_exp_iff {x : ℤᵐ⁰} {n : ℤ} : x < exp n ↔ x ≤ exp (n - 1) := by
  cases x
  · simp
  · simp [-exp_sub, Int.le_sub_one_iff]

end WithZero
