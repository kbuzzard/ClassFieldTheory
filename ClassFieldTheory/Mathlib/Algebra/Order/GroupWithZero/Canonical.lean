import Mathlib.Algebra.Order.GroupWithZero.Canonical

namespace WithZero
variable {M : Type*} [Preorder M] [Zero M] {x : M}

@[simp] lemma exp_le_one : exp x ≤ 1 ↔ x ≤ 0 := exp_le_exp
@[simp] lemma one_le_exp : 1 ≤ exp x ↔ 0 ≤ x := exp_le_exp
@[simp] lemma exp_lt_one : exp x < 1 ↔ x < 0 := exp_lt_exp
@[simp] lemma one_lt_exp : 1 < exp x ↔ 0 < x := exp_lt_exp

/-- The characterisation of `exp (-1) : ℤᵐ⁰`. -/
theorem exp_neg_one_def {x : ℤᵐ⁰} : x = .exp (-1) ↔ x < 1 ∧ ∀ y < 1, y ≤ x := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl
    refine ⟨by decide, fun y hy ↦ y.expRecOn (by decide) (fun y hy ↦ ?_) hy⟩
    rw [exp_lt_one] at hy
    rw [exp_le_exp]
    grind
  induction x using expRecOn
  · exact absurd (h.2 (exp (-1)) (by decide)) (by decide)
  refine le_antisymm ?_ (h.2 _ (by decide))
  rw [exp_lt_one] at h
  rw [exp_le_exp]
  grind

theorem lt_exp_iff {x : ℤᵐ⁰} {n : ℤ} : x < exp n ↔ x ≤ exp (n - 1) := by
  induction x using expRecOn <;> simp [-exp_sub, Int.le_sub_one_iff]

end WithZero
